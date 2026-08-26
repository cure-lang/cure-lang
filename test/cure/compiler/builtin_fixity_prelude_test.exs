defmodule Cure.Compiler.BuiltinFixityPreludeTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable}

  test "operators.cure carries @prelude" do
    {:ok, src} = File.read("lib/std/operators.cure")
    # `@prelude` must decorate `Std.Operators` itself, so nothing may stand
    # between them -- except the module's own `##` documentation, which belongs
    # to that module too.
    assert src =~ ~r/@prelude[ \t]*\n(?:[ \t]*(?:##.*)?\n)*[ \t]*mod Std\.Operators/
  end

  test "the built-in table still declares the core operators" do
    t = BuiltinFixity.table()

    for op <- ["+", "*", "|>", "==", "."] do
      assert FixityTable.declares?(t, op), "expected built-in table to declare #{op}"
    end

    refute FixityTable.declares?(t, "✉")
    refute FixityTable.declares?(t, "<-|")
  end

  test "the built-in table is a stable constant (same term on repeat)" do
    assert BuiltinFixity.table() == BuiltinFixity.table()
  end
end
