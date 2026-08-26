defmodule Cure.Elab.BuiltinOpSurfaceCallTest do
  @moduledoc """
  Phase 2: a builtin primitive op is callable from surface by its qualified name
  `Std.Builtin.<op>`, so interface leaf methods can bottom out in it.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Std.Builtin.int_eq and int_add are callable" do
    src = """
    mod M
      fn my_eq(a: Int, b: Int) -> Bool = Std.Builtin.int_eq(a, b)
      fn my_add(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "Std.Builtin.struct_eq (three-arg, erased type) is callable" do
    src = """
    mod M
      type Color = Red | Green | Blue
      fn ceq(a: Color, b: Color) -> Bool = Std.Builtin.struct_eq(Color, a, b)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
