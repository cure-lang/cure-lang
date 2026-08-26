defmodule Cure.Core.IntSurfaceTest do
  @moduledoc """
  Spec 2026-07-18-inductive-int, Task 4: the surface flip. `Int` resolves to the
  inductive data family Std.Int#Int (FromNat / NegativeSuccessor), exactly as
  `Nat` resolves to Std.Nat#Nat — so `match i` on `i : Int` is coverage-checked
  over the two constructors, while `{:int_lit, n}` arithmetic keeps folding to a
  native BEAM integer.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  defp run(src, mod_name, fns) do
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: mod_name, functions: fns)
    mod
  end

  test "surface Int resolves to the inductive data family, and match on Int type-checks" do
    src =
      "mod M\n" <>
        "  use Std.Int\n" <>
        "  fn sign(i: Int) -> Nat = match i\n" <>
        "    FromNat(n) -> S(Z())\n" <>
        "    NegativeSuccessor(n) -> Z()\n" <>
        "  fn pos() -> Nat = sign(FromNat(Z()))\n" <>
        "  fn neg() -> Nat = sign(NegativeSuccessor(Z()))\nend\n"

    mod = run(src, :"Cure.IntSurface1", [:sign, :pos, :neg])
    # sign(FromNat(0)) = 1 ; sign(NegativeSuccessor(0) = -1) = 0
    assert apply(mod, :pos, []) == 1
    assert apply(mod, :neg, []) == 0
    # native-integer scrutinee dispatches by sign (constructor rep is native)
    assert apply(mod, :sign, [7]) == 1
    assert apply(mod, :sign, [-4]) == 0
  end

  test "existing Int arithmetic still type-checks and folds to a native integer" do
    src =
      "mod M\n" <>
        "  use Std.Int\n" <>
        "  fn t() -> Int = 2 + 3 * 4\nend\n"

    mod = run(src, :"Cure.IntSurface2", [:t])
    # {:int_lit, 14}; native machine integer at runtime
    assert apply(mod, :t, []) == 14
  end
end
