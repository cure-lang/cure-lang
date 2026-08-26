defmodule Cure.Migrate.RemovedModuleTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Migrate
  alias Cure.Migrate.Rules.RemovedModule

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  defp apply_rule(src, file) do
    ast = parse!(src, file)
    RemovedModule.detect_and_rewrite(ast, Migrate.build_ctx(ast))
  end

  test "warns (does not rewrite) on a `use` of a removed module" do
    assert {:warn, [%Cure.Diagnostic.Span{start_line: 2, start_column: 7, end_column: 17}]} =
             apply_rule("mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n", "a.cure")
  end

  test "warns on a qualified reference to a removed module" do
    assert {:warn, [%Cure.Diagnostic.Span{start_line: 2, start_column: 25, end_column: 40}]} =
             apply_rule("mod M\n  fn f(x: Int) -> Int = Std.Equal.equal(x, x)\n", "b.cure")
  end

  test "the full registry surfaces the removed-module warning and leaves the source unchanged" do
    ast = parse!("mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n", "c.cure")
    {new_ast, warns} = Migrate.run(ast, file: "c.cure")

    assert new_ast == ast
    warning = Enum.find(warns, &(&1.rule == :W_removed_module))
    assert warning.tier == :manual
    assert warning.preview == nil
    assert warning.message =~ "completed by hand"
  end

  test "a live module (still present) does not warn" do
    assert :no_change = apply_rule("mod M\n  use Std.List\n  fn f(x: Int) -> Int = x\n", "d.cure")
  end
end
