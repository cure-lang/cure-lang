defmodule Cure.Migrate.IfElifToPickupTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  # Full reparse (lex AND parse), not just tokenize -- tokenizing successfully
  # does not prove the output is syntactically valid; a malformed `pickup`
  # block could still tokenize while failing to parse. This helper is what
  # every "reparses"/"NOT rewritten ... still warns" assertion below actually
  # calls, so none of them can pass on lex-only success.
  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  test "top-level if/else rewrites to pickup and reparses" do
    {out, warns} = migrate("mod M\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n", "a.cure")
    assert out =~ "pickup"
    assert reparses?(out, "a.cure")

    warning = Enum.find(warns, &(&1.rule == :W_if_elif_pickup))
    assert %Cure.Diagnostic.Span{start_line: 2, start_column: 23, end_column: 25} = warning.span
  end

  test "a comment on the rewritten conditional survives the restructuring rewrite" do
    # NB: Cure only captures a real `else` for an *inline* `if c then a else b`
    # (every multi-line form severs the `else` onto sibling statements, and a
    # trailing comment on a branch line severs it too -- verified 2026-07-10). A
    # rewritable conditional therefore cannot carry per-branch comments; the only
    # comment it can hold is a trailing one on the whole construct. This test
    # guards that trivia survives the conditional->pickup restructuring at all
    # (the plan's original "comments on branches" fixture used an unparseable
    # multi-line shape). See Task 8 notes in the plan.
    src = "mod M\nfn f(x: Int) -> Int = if x > 0 then 1 else 2  # choose branch\n"
    {out, _} = migrate(src, "b.cure")
    assert out =~ "pickup"
    assert out =~ "choose branch"
  end

  test "conditional inside a call-argument list is NOT rewritten (paren-context), still warns" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    {out, warns} = migrate(src, "c.cure")
    refute out =~ "pickup"
    assert Enum.any?(warns, &(&1.rule == :W_if_elif_pickup))
    assert reparses?(out, "c.cure")
  end

  test "a bare-grouped conditional used as an operand is NOT rewritten either (no :function_call ancestor exists to detect structurally), still warns" do
    # `parse_grouped/1` discards the grouping node entirely (parser.ex:526-533)
    # -- this conditional has NO distinguishing ancestor in the AST at all, so
    # only a verify-by-reparse strategy (not an ancestor-shape check) catches
    # this case.
    src = "mod M\nfn g(x: Int) -> Int = (if x > 0 then 1 else 2) + 1\n"
    {out, warns} = migrate(src, "d.cure")
    refute out =~ "pickup"
    assert Enum.any?(warns, &(&1.rule == :W_if_elif_pickup))
    assert reparses?(out, "d.cure")
  end
end
