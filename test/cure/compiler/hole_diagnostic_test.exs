defmodule Cure.Compiler.HoleDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.{Renderer, Sink}
  alias Cure.Elab.{Emit, Program}

  @source """
  mod HoleDiagnostic
    # ??? in prose is not the unfinished program term.
    fn broken() -> Int = ?todo
  end
  """

  test "the real compiler preserves the authored hole and annotation ranges" do
    assert {:error, {:codegen_error, {:unfilled_hole, details}}} =
             Cure.Compiler.compile_and_load(@source,
               file: "hole_diagnostic.cure",
               emit_events: false
             )

    assert details.definition == :"HoleDiagnostic#broken"
    assert details.hole_id == "HoleDiagnostic.broken#todo"
    assert details.span.start_byte == byte_offset!(@source, "?todo")
    assert details.span.end_byte - details.span.start_byte == byte_size("?todo")
    assert details.annotation_span.start_byte == byte_offset!(@source, "Int")
  end

  test "terminal output labels the hole token rather than matching earlier hole-like text" do
    {:error, error} =
      Cure.Compiler.compile_and_load(@source,
        file: "hole_diagnostic.cure",
        emit_events: false
      )

    rendered = Errors.format_with_source(error, "hole_diagnostic.cure", @source)

    assert rendered ==
             """
             -- UNFILLED HOLE [E014] ----------------------------------- hole_diagnostic.cure

             The definition `broken` still contains an unfinished hole.

             at hole_diagnostic.cure:3:24
             3 |   fn broken() -> Int = ?todo
               |                  ---   ^^^^^ this function's result type is declared here; replace this hole with an expression

             Hint: Replace the hole with an expression that satisfies its surrounding type
             """
             |> String.trim_trailing()
  end

  test "LSP output carries the exact hole range and related annotation" do
    {:error, error} =
      Cure.Compiler.compile_and_load(@source,
        file: "hole_diagnostic.cure",
        emit_events: false
      )

    {diagnostic, registry} = Errors.to_diagnostic(error, "hole_diagnostic.cure", @source)
    rendered = Sink.render(Sink.new(format: :lsp, registry: registry), diagnostic)

    assert rendered["code"] == "E014"

    assert rendered["range"] == %{
             "start" => %{"line" => 2, "character" => 23},
             "end" => %{"line" => 2, "character" => 28}
           }

    assert [
             %{
               "location" => %{
                 "uri" => annotation_uri,
                 "range" => annotation_range
               }
             }
           ] = rendered["relatedInformation"]

    assert String.ends_with?(annotation_uri, "/hole_diagnostic.cure")
    assert annotation_range["start"]["line"] == 2

    assert rendered["data"]["suggestions"] == [
             %{
               "message" => "Replace the hole with an expression that satisfies its surrounding type",
               "applicability" => "manual",
               "edits" => []
             }
           ]
  end

  test "an unannotated generated hole asks for a result type at the exact token" do
    source = """
    mod InferredHole
      # ??? in prose is not the unfinished program term.
      fn broken() = ???
    end
    """

    assert {:error, error} = Program.elaborate(source, file: "inferred_hole.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "inferred_hole.cure", source)

    assert diagnostic.code == "E014"
    assert diagnostic.key == :unfilled_hole
    assert diagnostic.payload.kind == :inference_position
    assert diagnostic.primary.span.start_byte == byte_offset!(source, "???", 2)
    assert diagnostic.primary.span.end_byte - diagnostic.primary.span.start_byte == 3

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- HOLE NEEDS A TYPE ANNOTATION [E014] ---------------------- inferred_hole.cure

             Cure cannot infer what this hole should contain because the surrounding
             definition has no declared result type.

             at inferred_hole.cure:3:17
             3 |   fn broken() = ???
               |                 ^^^ this hole has no expected type

             Hint: Declare the result type after `->`, then replace the hole with an expression of that type
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 16},
             "end" => %{"line" => 2, "character" => 19}
           }
  end

  test "a selected definition reports its own hole when another authored hole comes first" do
    source = """
    mod MultipleHoles
      fn first() -> Int = ?first
      fn second() -> Int = ?second
    end
    """

    assert {:ok, env} = Program.elaborate(source, file: "multiple_holes.cure")

    assert {:error, {:unfilled_hole, details}} =
             Emit.compile_forms(env, :MultipleHoles, [:"MultipleHoles#second"])

    assert details.definition == :"MultipleHoles#second"
    assert details.span.start_byte == byte_offset!(source, "?second")

    {diagnostic, registry} =
      Errors.to_diagnostic({:unfilled_hole, details}, "multiple_holes.cure", source)

    assert diagnostic.primary.span.start_byte == byte_offset!(source, "?second")
    assert Renderer.plain(diagnostic, registry) =~ "?second"
    refute Renderer.plain(diagnostic, registry) =~ "?first"
  end

  test "a locationless hole never infers blame from hole-looking source text" do
    source = """
    mod Locationless
      # ??? belongs to this comment, not the independently supplied error
      fn complete() -> Int = 1
    end
    """

    {diagnostic, registry} =
      Errors.to_diagnostic({:unfilled_hole, :missing}, "locationless.cure", source)

    assert diagnostic.primary == nil

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNFILLED HOLE [E014] --------------------------------------------------------

             The compiler reached the unfinished hole `?missing`.
             """)
  end

  defp byte_offset!(source, needle, occurrence \\ 1) do
    {offset, _length} = source |> :binary.matches(needle) |> Enum.at(occurrence - 1)
    offset
  end
end
