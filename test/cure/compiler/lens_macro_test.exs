defmodule Cure.Compiler.LensMacroTest do
  use ExUnit.Case, async: false

  test "the lens macro is auto-preluded from Std.Optic" do
    assert {:ok, ast} = Cure.Compiler.parse_source("mod LensSyntax\n  fn first() = lens first\n")

    assert {:container, _, [{:function_def, _, [{:function_call, meta, []}]}]} = ast
    assert Keyword.get(meta, :name) == "first_lens"
  end

  test "lens first and second use the typed Std.Optic implementations" do
    optic_module = :"Cure.Std.Optic"
    first = apply(optic_module, :first_lens, [])
    second = apply(optic_module, :second_lens, [])

    assert apply(optic_module, :view, [first, {10, 20}]) == 10
    assert apply(optic_module, :view, [second, {10, 20}]) == 20
    assert apply(optic_module, :set, [first, 99, {10, 20}]) == {99, 20}
    assert apply(optic_module, :set, [second, 99, {10, 20}]) == {10, 99}
  end
end
