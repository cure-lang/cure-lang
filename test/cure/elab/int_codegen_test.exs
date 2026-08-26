defmodule Cure.Elab.IntCodegenTest do
  @moduledoc """
  Spec 2026-07-18-inductive-int, Task 3: the canonical Std.Int family
  (FromNat / NegativeSuccessor) lowers to native BEAM machine integers at emit.
  Both constructors are 1-ary, so — unlike Nat's Z/S — the erasure keys off the
  constructor NAME:  FromNat(n) => n (identity), NegativeSuccessor(n) => -(n+1).
  A closed application folds to {:int_lit,_} before emit (Task 2); this OPEN path
  is exercised here by constructor terms over a runtime argument.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  defp run(src, mod_name, fns) do
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: mod_name, functions: fns)
    mod
  end

  test "open FromNat(n) lowers to the identity native integer" do
    src =
      "mod M\n" <>
        "  use Std.Int\n" <>
        "  fn to_int(n: Nat) -> Int = FromNat(n)\n" <>
        "  fn neg1(n: Nat) -> Int = NegativeSuccessor(n)\n" <>
        "  fn t() -> Int = to_int(S(S(Z())))\nend\n"

    mod = run(src, :"Cure.IntCodegen1", [:to_int, :neg1, :t])
    # FromNat(2) => native 2
    assert apply(mod, :t, []) == 2
    # NegativeSuccessor(2) => -(2+1) => -3
    assert apply(mod, :neg1, [2]) == -3
  end

  test "case-on-Int dispatches by sign at runtime" do
    src =
      "mod M\n" <>
        "  use Std.Int\n" <>
        "  fn magnitude(i: Int) -> Nat = match i\n" <>
        "    FromNat(n) -> n\n" <>
        "    NegativeSuccessor(n) -> S(n)\n" <>
        "  fn pos() -> Nat = magnitude(FromNat(S(S(Z()))))\n" <>
        "  fn neg() -> Nat = magnitude(NegativeSuccessor(S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.IntCodegen2", [:magnitude, :pos, :neg])
    # FromNat(2) => 2 ; magnitude 2
    assert apply(mod, :pos, []) == 2
    # NegativeSuccessor(2) => -3 ; magnitude = S(2) = 3
    assert apply(mod, :neg, []) == 3
    # direct native-integer scrutinee dispatch
    assert apply(mod, :magnitude, [5]) == 5
    assert apply(mod, :magnitude, [-3]) == 3
  end
end
