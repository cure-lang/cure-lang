defmodule Cure.Elab.BoolErasureTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "True/False constructors run as lowercase BEAM booleans" do
    src =
      "mod M\n  fn t() -> Bool = true\n  fn f() -> Bool = false\n  fn c(b: Bool) -> Bool = if b then false else true\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BoolErase1", functions: [:t, :f, :c])
    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
    assert apply(mod, :c, [true]) == false
    assert apply(mod, :c, [false]) == true
  end
end
