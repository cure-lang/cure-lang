defmodule Cure.Migrate.ModuleRenameTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate
  alias Cure.Migrate.Rules.ModuleRename

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  # Full migrate path: lex-with-trivia, parse, run the whole registry, reprint.
  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  # Isolated rule application (default ctx), returning the raw rule result.
  defp apply_rule(src, file) do
    ast = parse!(src, file)
    ModuleRename.detect_and_rewrite(ast, Migrate.build_ctx(ast))
  end

  test "renames a `use Std.Eq` import to `use Std.Equatable`" do
    {out, warns} = migrate("mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n", "a.cure")
    assert out =~ ~r/use\s+Std\.Equatable/
    refute out =~ ~r/use\s+Std\.Eq\b/
    assert Enum.any?(warns, &(&1.rule == :W_module_rename))
    assert reparses?(out, "a.cure")
  end

  test "renames the module prefix of a qualified call, keeping the function name" do
    {:rewrite, ast, [span]} =
      apply_rule("mod M\n  fn f(x: Int) -> Bool = Std.Eq.eq(x, x)\n", "b.cure")

    names = qualified_names(ast)
    assert "Std.Equatable.eq" in names
    refute "Std.Eq.eq" in names
    assert %Cure.Diagnostic.Span{start_line: 2, start_column: 26, end_column: 35} = span
  end

  test "a file that references no renamed module is untouched (:no_change)" do
    assert :no_change =
             apply_rule("mod M\n  use Std.List\n  fn f(x: Int) -> Int = x\n", "c.cure")
  end

  test "does not rewrite an unrelated module whose name merely starts with the same letters" do
    # `Std.Equatable` must NOT be re-mangled, and `Std.EqualityDemo` is not a key.
    assert :no_change =
             apply_rule("mod M\n  use Std.Equatable\n  fn f(x: Int) -> Bool = eq(x, x)\n", "d.cure")
  end

  test "renames module references inside signature type meta positions" do
    {out, _warns} = migrate("mod M\n  fn f(x: Std.Eq.T) -> Std.Eq.T = Std.Eq.eq(x)\n", "e.cure")
    assert out =~ "Std.Equatable.T"
    assert out =~ "Std.Equatable.eq"
    refute out =~ "Std.Eq."
  end

  # Every qualified `name` string in a parsed tree.
  defp qualified_names({:function_call, meta, ch}),
    do: [Keyword.get(meta, :name) | qualified_names(ch)]

  defp qualified_names({_k, _meta, ch}) when is_list(ch), do: qualified_names(ch)
  defp qualified_names({_k, _meta, _name, inner}), do: qualified_names(inner)
  defp qualified_names(l) when is_list(l), do: Enum.flat_map(l, &qualified_names/1)
  defp qualified_names(_), do: []
end
