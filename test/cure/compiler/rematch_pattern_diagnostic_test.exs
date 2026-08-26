defmodule Cure.Compiler.RematchPatternDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      ZeroS : SNat(Z)
      SuccS : SNat(n) -> SNat(S(n))
  """

  test "a computing parent expression points to both sides of the rematch" do
    source =
      "mod BadRematch\n" <>
        @preamble <>
        """
          fn f(n: Nat, w: SNat(n), s: SNat(n)) -> Nat = with s
            n + n, w, ZeroS() | ZeroS() -> Z()
            S(m), w, SuccS(k) | SuccS(k) -> Z()
        end
        """

    {diagnostic, registry} = compile_diagnostic(source, "bad_rematch.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REMATCH PATTERN MUST DESCRIBE A SHAPE [E093] --------------- bad_rematch.cure

             The left side of a `with` rematch restates the function's parameter patterns. It
             cannot evaluate an expression such as this `binary_op` node.

             Use variables and constructor patterns here; perform calculations in a guard or
             branch body.

             at bad_rematch.cure:7:5
             6 |   fn f(n: Nat, w: SNat(n), s: SNat(n)) -> Nat = with s
               |        ------ this is the corresponding original function pattern
             7 |     n + n, w, ZeroS() | ZeroS() -> Z()
               |     ^^^^^             - ------- this expression computes a value instead of matching a shape; patterns before this `|` restate the function's left-hand side; this pattern matches the value after `with`

             Hint: Replace this expression with a variable or constructor pattern, then move the calculation into the branch body
             """)

    assert diagnostic.payload == %{
             kind: :with_rematch_non_constructor_pattern,
             details: :binary_op,
             checking: :f,
             original_pattern_count: 3,
             restated_pattern_count: 3
           }

    assert diagnostic.primary.span.start_line == 7
    assert diagnostic.primary.span.start_column == 5
    assert diagnostic.primary.span.end_column == 10

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.message}) == [
             {6, "this is the corresponding original function pattern"},
             {7, "patterns before this `|` restate the function's left-hand side"},
             {7, "this pattern matches the value after `with`"}
           ]

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"]["start"] == %{"line" => 6, "character" => 4}
    assert lsp["range"]["end"] == %{"line" => 6, "character" => 9}
    assert length(lsp["relatedInformation"]) == 3
    assert lsp["data"]["payload"]["details"] == "binary_op"
  end

  test "the wrong number of parent patterns labels both complete lists" do
    source =
      "mod ArityRematch\n" <>
        @preamble <>
        """
          fn f(n: Nat, w: SNat(n), s: SNat(n)) -> Nat = with s
            n, w | ZeroS() -> Z()
            n, w | SuccS(k) -> Z()
        end
        """

    {diagnostic, registry} = compile_diagnostic(source, "arity_rematch.cure")
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.title == "Rematch has the wrong number of parent patterns"
    assert diagnostic.payload.expected == 3
    assert diagnostic.payload.actual == 2
    assert diagnostic.primary.span.start_column == 5
    assert diagnostic.primary.span.end_column == 9
    assert rendered =~ "This function has 3 parent patterns, but the branch restates 2."
    assert rendered =~ "|     ^^^^ - ------- these parent patterns do not match the function's arity"
    assert rendered =~ "Hint: Write exactly 3 parent patterns before `|`"
  end

  test "replacing the expression with a pattern and restoring every parent position compiles" do
    source =
      "mod FixedRematch\n" <>
        @preamble <>
        """
          fn f(n: Nat, w: SNat(n), s: SNat(n)) -> Nat = with s
            n, w, ZeroS() | ZeroS() -> Z()
            n, w, SuccS(k) | SuccS(k) -> Z()
        end
        """

    assert {:ok, :"Cure.FixedRematch", []} =
             Cure.Compiler.compile_string(source, file: "fixed_rematch.cure", emit_events: false)
  end

  defp compile_diagnostic(source, file) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: file, emit_events: false)

    Errors.to_diagnostic(reason, file, source)
  end
end
