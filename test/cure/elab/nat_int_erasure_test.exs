defmodule Cure.Elab.NatIntErasureTest do
  @moduledoc """
  Spec 2026-07-08-nat-int-erasure: canonical Std.Nat (auto-prelude, @builtin(:nat))
  erases to BEAM machine integers at emit; locally-redeclared Nat keeps tuples
  (nominal, not structural). Kernel/erased-Core stay inductive — pinned elsewhere
  (test/cure/core/*, global_namespace_soundness_test.exs).
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  defp run(src, mod_name, fns) do
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: mod_name, functions: fns)
    mod
  end

  test "rule 1: constructors build machine ints" do
    src = "mod M\n  fn two() -> Nat = S(S(Z()))\n  fn zero() -> Nat = Z()\nend\n"
    mod = run(src, :"Cure.NatInt1", [:two, :zero])
    assert apply(mod, :two, []) == 2
    assert apply(mod, :zero, []) == 0
  end

  test "rule 2: matching S(k) binds the predecessor" do
    src =
      "mod M\n" <>
        "  fn pred(n: Nat) -> Nat = match n\n" <>
        "    Z() -> Z()\n" <>
        "    S(k) -> k\n" <>
        "  fn t() -> Nat = pred(S(S(Z())))\n" <>
        "  fn z() -> Nat = pred(Z())\nend\n"

    mod = run(src, :"Cure.NatInt2", [:pred, :t, :z])
    assert apply(mod, :t, []) == 1
    assert apply(mod, :z, []) == 0
  end

  test "rule 2, deep: S(S(m)) composes two predecessor binds and the body uses m" do
    src =
      "mod M\n" <>
        "  fn sub2(n: Nat) -> Nat = match n\n" <>
        "    S(S(m)) -> m\n" <>
        "    x -> Z()\n" <>
        "  fn t() -> Nat = sub2(S(S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt3", [:sub2, :t])
    assert apply(mod, :t, []) == 1
  end

  test "rule 3: recursive arithmetic over the Int rep computes correctly" do
    src =
      "mod M\n" <>
        "  fn add(a: Nat, b: Nat) -> Nat = match a\n" <>
        "    Z() -> b\n" <>
        "    S(k) -> S(add(k, b))\n" <>
        "  fn t() -> Nat = add(S(S(Z())), S(S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt4", [:add, :t])
    assert apply(mod, :t, []) == 5
  end

  test "generics (§2.3 pin): a polymorphic container holds int Nats through generic code" do
    src =
      "mod M\n" <>
        "  type Pair(a: Type, b: Type) = MkP(a, b)\n" <>
        "  fn swap({a: Type}, {b: Type}, p: Pair(a, b)) -> Pair(b, a) = match p\n" <>
        "    MkP(x, y) -> MkP(y, x)\n" <>
        "  fn t() -> Pair(Nat, Nat) = swap(MkP(Z(), S(S(Z()))))\nend\n"

    mod = run(src, :"Cure.NatInt5", [:swap, :t])
    assert apply(mod, :t, []) == {:MkP, 2, 0}
  end

  test "nominal no-op (§2.4 pin): a locally-redeclared Nat still builds tuples" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n" <>
        "  fn two() -> Nat = S(S(Z()))\nend\n"

    mod = run(src, :"Cure.NatIntLocal", [:two])
    assert apply(mod, :two, []) == {:S, {:S, :Z}}
  end

  describe "rule 4: first-class constructors (resolve_free eta-expansion)" do
    test "S passed to a HOF applies as the increment function" do
      src =
        "mod M\n" <>
          "  fn ap(f: Nat -> Nat, n: Nat) -> Nat = f(n)\n" <>
          "  fn t() -> Nat = ap(S, S(Z()))\nend\n"

      mod = run(src, :"Cure.NatIntEta1", [:ap, :t])
      assert apply(mod, :t, []) == 2
    end

    test "eta-expansion is general: a non-Nat positive-arity ctor works first-class" do
      src =
        "mod M\n  type Box = Mk(Int)\n" <>
          "  fn ap(f: Int -> Box, i: Int) -> Box = f(i)\n" <>
          "  fn t() -> Box = ap(Mk, 3)\nend\n"

      mod = run(src, :"Cure.NatIntEta2", [:ap, :t])
      assert apply(mod, :t, []) == {:Mk, 3}
    end
  end
end
