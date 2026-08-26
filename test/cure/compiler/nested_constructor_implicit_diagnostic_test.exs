defmodule Cure.Compiler.NestedConstructorImplicitDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @types """
  mod NestedCtor
    type Phase = Up | Down
    type Fail indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
      FRestart : Fail(S(n), Up, n, Up)
      FShutdown : Fail(Z, Up, Z, Down)
    type FailRun indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
      FRDone : FailRun(b, p, b, p)
      FRMore : Fail(b1, p1, bm, pm) -> FailRun(bm, pm, b2, p2) -> FailRun(b1, p1, b2, p2)
  """

  test "an unresolved nested constructor labels its call and the enclosing result" do
    source =
      @types <>
        """
          fn bad() -> FailRun(Z, Up, Z, Down) = FRMore(FRestart(), FRDone())
        end
        """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:unsolved_metavariables, :"NestedCtor#FRestart"} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CANNOT INFER `FRESTART` INSIDE `FRMORE` [E011] ------------- nested_ctor.cure

             Argument 1 of `FRMore` uses `FRestart`, but its hidden type or index values are
             still unknown. The surrounding result and the other constructor fields do not
             determine them.

             at nested_ctor.cure:9:48
             9 |   fn bad() -> FailRun(Z, Up, Z, Down) = FRMore(FRestart(), FRDone())
               |               -----------------------          ^^^^^^^^^^ the surrounding result still does not determine these indices; this nested constructor needs an expected indexed type

             Hint: Use `FRestart` where its expected field type is known, or change the sibling arguments or result annotation so its indices are determined
             """)

    assert diagnostic.payload == %{
             kind: :nested_constructor_implicit,
             name: :"NestedCtor#FRestart",
             constructor: "FRestart",
             owner: :"NestedCtor#FRMore",
             argument_index: 0,
             expectation_origin: :constructor_argument
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(8, 47, 8, 57)

    assert [%{"message" => message, "location" => location}] = lsp["relatedInformation"]
    assert message == "the surrounding result still does not determine these indices"
    assert location["range"] == range(8, 14, 8, 37)
  end

  test "a sibling that determines the nested constructor indices still elaborates" do
    source =
      @types <>
        """
          fn good() -> FailRun(Z, Up, Z, Down) = FRMore(FShutdown(), FRDone())
        end
        """

    assert {:ok, _env} = Program.elaborate(source, file: "nested_ctor.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "nested_ctor.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "nested_ctor.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
