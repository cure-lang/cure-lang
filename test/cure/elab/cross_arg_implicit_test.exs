defmodule Cure.Elab.CrossArgImplicitTest do
  @moduledoc """
  Cross-argument implicit solving (Idris parity): an argument whose type mentions
  an implicit that only a *later* argument determines. `lookup(fz(), vec())` —
  index-first — failed `{:unsolved_metavariables, :fz}`: the implicit length `n`
  is solved by the later `vec()` argument, but `fz() : Fin(n)` was elaborated (by
  inference) before `n` was known, and `fz()` cannot infer standalone.

  The bidirectional application fallback now *defers* an underdetermined argument
  at a still-metavariable-bearing domain — a placeholder metavariable holds its
  position so later domains' de Bruijn frames stay aligned — and a second pass
  (`resolve_deferred_slots`) checks it against the now-solved domain, back-patching
  the placeholder. Oracle `dep/dep06_cross_arg_implicit` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @pre "mod M\n  type Nat = Z | S(Nat)\n" <>
         "  type Vector(a: Type) indices (n: Nat)\n" <>
         "    empty : Vector(a, Z)\n" <>
         "    prepend : a -> Vector(a, n) -> Vector(a, S(n))\n" <>
         "  type Fin indices (n: Nat)\n" <>
         "    fz : Fin(S(m))\n    fs : Fin(m) -> Fin(S(m))\n" <>
         "  fn lookup({a: Type},{n: Nat}, i: Fin(n), v: Vector(a, n)) -> a = match i\n" <>
         "    fz() -> match v\n      prepend(x, xs) -> x\n" <>
         "    fs(j) -> match v\n      prepend(x, xs) -> lookup(j, xs)\n" <>
         "  fn vec() -> Vector(Nat, S(S(Z))) = prepend(S(Z()), prepend(Z(), empty()))\n"

  test "an implicit solved by a later argument lets an earlier underdetermined arg check" do
    src =
      @pre <>
        "  fn at0() -> Nat = lookup(fz(), vec())\n" <>
        "  fn at1() -> Nat = lookup(fs(fz()), vec())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.XArg", functions: [:lookup, :vec, :at0, :at1])

    assert apply(mod, :at0, []) == {:S, :Z}
    assert apply(mod, :at1, []) == :Z
  end

  test "a genuinely ambiguous call (no argument determines the implicit) is still rejected" do
    # `lookup(fz(), fz())` — the second argument is a Fin, not the Vector that
    # would solve `n`, so nothing determines the length; both stay underdetermined.
    assert {:error, _} =
             Program.elaborate(@pre <> "  fn bad() -> Nat = lookup(fz(), fz())\nend\n")
  end
end
