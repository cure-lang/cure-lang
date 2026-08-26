defmodule Cure.Stdlib.CharCodePointTest do
  @moduledoc """
  `Std.Char.code_point` exposes a Char's Unicode code point as an `Int` — the
  Lean `Fin.val` analog for `Char = Bounded(0x110000)`. A `Char` already
  erases to a native integer, so the runtime bridge (`:cure_std_char.code_point/1`)
  is the identity; the point is purely to give the type-level coercion a name
  so `Std.Comparable`'s `Char`/`String` instances can compare code points.

  This is the foundation of the comparison-operator keystone: routing `<`/`>`
  on non-primitive operands through `Std.Comparable`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  test "code_point of a character literal is its code point" do
    src = """
    mod T
      use Std.Char
      fn go() -> Int = code_point('A')
    end
    """

    assert eval(src, :go, :"Cure.CharCodePointA") == 65
  end

  test "code_point of a higher code point" do
    src = """
    mod T
      use Std.Char
      fn go() -> Int = code_point('z')
    end
    """

    assert eval(src, :go, :"Cure.CharCodePointZ") == 122
  end
end
