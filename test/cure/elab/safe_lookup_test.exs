defmodule Cure.Elab.SafeLookupTest do
  @moduledoc """
  Length-safe vector indexing — `lookup : Vector(a, n) -> Fin(n) -> a` — the
  canonical payoff of dependent types (Idris parity). Matching the `Fin` index
  refines the shared length `n`, so each `match v` branch needs only the
  `prepend` case (the `empty` case is impossible: `Fin(Zero)` is uninhabited).
  This composes the whole dependent stack: GADT `Fin`/`Vector`, a result-only
  index variable (`fz : Fin(Suc(m))`), and shared-index dependent matching
  linking the `Fin`'s and the `Vector`'s index. Oracle `dep/dep05_safe_lookup`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @pre "mod M\n  type Nat = Z | S(Nat)\n" <>
         "  type Vector(a: Type) indices (n: Nat)\n" <>
         "    empty : Vector(a, Z)\n" <>
         "    prepend : a -> Vector(a, n) -> Vector(a, S(n))\n" <>
         "  type Fin indices (n: Nat)\n" <>
         "    fz : Fin(S(m))\n    fs : Fin(m) -> Fin(S(m))\n"

  @lookup "  fn lookup({a: Type},{n: Nat}, v: Vector(a, n), i: Fin(n)) -> a = match i\n" <>
            "    fz() -> match v\n      prepend(x, xs) -> x\n" <>
            "    fs(j) -> match v\n      prepend(x, xs) -> lookup(xs, j)\n"

  test "safe indexed lookup elaborates and returns the element at each index" do
    src =
      @pre <>
        @lookup <>
        "  fn vec() -> Vector(Nat, S(S(Z))) = prepend(S(Z()), prepend(Z(), empty()))\n" <>
        "  fn at0() -> Nat = lookup(vec(), fz())\n" <>
        "  fn at1() -> Nat = lookup(vec(), fs(fz()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.SafeLk", functions: [:lookup, :vec, :at0, :at1])

    # vec = [S(Z), Z]; index 0 -> S(Z), index 1 -> Z.
    assert apply(mod, :at0, []) == {:S, :Z}
    assert apply(mod, :at1, []) == :Z
  end

  test "the lookup definition also type-checks with the Fin index first" do
    # The definition is order-agnostic; only the call site's implicit-solving
    # order (the vector solves `n`) motivates vector-first at use.
    src =
      @pre <>
        "  fn lookup({a: Type},{n: Nat}, i: Fin(n), v: Vector(a, n)) -> a = match i\n" <>
        "    fz() -> match v\n      prepend(x, xs) -> x\n" <>
        "    fs(j) -> match v\n      prepend(x, xs) -> lookup(j, xs)\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
