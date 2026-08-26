defmodule Cure.Compiler.PositionalForcedPatternDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a positional dot pattern is rejected before misleading coverage analysis" do
    source = """
    mod Forced
      type Pair = MkPair(Nat, Nat)
      fn bad(pair: Pair) -> Nat = match pair
        MkPair(left, .missing) -> left
    end
    """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:forced_pattern_not_in_pattern, _meta} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- DOT PATTERN MUST NAME AN IMPLICIT FIELD [E093] ------------------ forced.cure

             Field 2 of `MkPair` is positional. A dot pattern checks a value that
             constructor-index refinement already determined, so it must be written inside a
             named implicit pattern such as `{index = .value}`.

             at forced.cure:4:18
             4 |     MkPair(left, .missing) -> left
               |     ------       ^^^^^^^^ this constructor pattern supplies positional fields; this forced check is in a positional field

             Hint: Bind this positional field normally, or move the dot check to the constructor's corresponding named implicit field
             """)

    refute diagnostic.title =~ "MISSING"

    assert diagnostic.payload == %{
             kind: :positional_forced_pattern,
             constructor: "MkPair",
             argument_index: 1,
             expectation_origin: :pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 17, 3, 25)

    assert [%{"message" => message, "location" => location}] = lsp["relatedInformation"]
    assert message == "this constructor pattern supplies positional fields"
    assert location["range"] == range(3, 4, 3, 10)
  end

  test "binding the positional field normally elaborates" do
    source = """
    mod Forced
      type Pair = MkPair(Nat, Nat)
      fn good(pair: Pair) -> Nat = match pair
        MkPair(left, right) -> left
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "forced.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "forced.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "forced.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
