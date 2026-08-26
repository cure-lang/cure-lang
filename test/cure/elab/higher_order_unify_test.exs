defmodule Cure.Elab.HigherOrderUnifyTest do
  @moduledoc """
  Higher-order unification depth fix (Idris parity): unifying a function-typed
  argument's type `(a) -> b` against a callee's expected `(?a) -> ?b` crosses the
  Π binder, so a metavariable solved inside the codomain was captured one de Bruijn
  level too deep and reappeared mis-levelled in the result type (`{:var, 4}` vs
  `{:var, 5}`). `Cure.Elab.Unify` now tracks binder depth and strengthens a
  metavariable's solution back to the ambient frame before recording it (at depth 0
  — every prior unification — this is the identity). This unblocks re-passing a
  polymorphic function argument, so `map` type-checks and runs.

  Oracle `poly/pl06_polymorphic_map` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @lst "mod M\n  type Nat = Z | S(Nat)\n  type Lst(a) = Nil | Cons(a, Lst(a))\n"

  test "polymorphic map type-checks and runs" do
    src =
      @lst <>
        "  fn map({a}, {b}, f: (a)->b, l: Lst(a)) -> Lst(b) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> Cons(f(x), map(f, xs))\n" <>
        "  fn s(n: Nat) -> Nat = S(n)\n" <>
        "  fn mklist() -> Lst(Nat) = Cons(Z(), Cons(S(Z()), Nil()))\n" <>
        "  fn g() -> Lst(Nat) = map(s, mklist())\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.HoMap", functions: [:map, :s, :mklist, :g])

    # map (+1) [0, 1] = [1, 2]
    assert apply(mod, :g, []) == {:Cons, {:S, :Z}, {:Cons, {:S, {:S, :Z}}, :Nil}}
  end

  test "re-passing a function-typed argument to an implicit-solving call type-checks" do
    # The minimal trigger: `q(f, l)` re-passes `f : (a) -> b` while solving q's own
    # implicit parameters — the case that previously failed :cannot_unify.
    src =
      @lst <>
        "  fn q({a}, {b}, f: (a)->b, l: Lst(a)) -> Lst(b) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> q(f, xs)\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an endomorphism argument (a) -> a maps and runs" do
    # The dual of the strengthen fix: the single implicit `a` recurs on both sides
    # of the `(a) -> a` binder, so a solved metavariable read under the codomain
    # binder must be shifted *up* into scope (force_d). Oracle `poly/pl07_endo_map`.
    src =
      @lst <>
        "  fn emap({a}, f: (a)->a, l: Lst(a)) -> Lst(a) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> Cons(f(x), emap(f, xs))\n" <>
        "  fn s(n: Nat) -> Nat = S(n)\n" <>
        "  fn mk() -> Lst(Nat) = Cons(Z(), Cons(S(Z()), Nil()))\n" <>
        "  fn g() -> Lst(Nat) = emap(s, mk())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.EndoMap", functions: [:emap, :s, :mk, :g])

    assert apply(mod, :g, []) == {:Cons, {:S, :Z}, {:Cons, {:S, {:S, :Z}}, :Nil}}
  end

  test "a polymorphic call used as an argument to another call elaborates and runs" do
    # `hd(Z(), map(s, mklist()))` — the `map(...)` result is an argument in
    # inference position. The scoped application path bound the nested implicit
    # call positionally (mis-binding `Lst(Nat)` to the `{a} : Type` slot); the
    # bidirectional fallback checks each argument against the callee's Π domain, so
    # the nested implicit call elaborates in checking mode. Oracle
    # `poly/pl08_map_as_argument`.
    src =
      @lst <>
        "  fn map({a}, {b}, f: (a)->b, l: Lst(a)) -> Lst(b) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> Cons(f(x), map(f, xs))\n" <>
        "  fn s(n: Nat) -> Nat = S(n)\n" <>
        "  fn mklist() -> Lst(Nat) = Cons(Z(), Cons(S(Z()), Nil()))\n" <>
        "  fn hd(d: Nat, l: Lst(Nat)) -> Nat = match l\n    Cons(x, xs) -> x\n    Nil() -> d\n" <>
        "  fn g() -> Nat = hd(Z(), map(s, mklist()))\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.MapArg", functions: [:map, :s, :mklist, :hd, :g])

    # head of map(+1, [0, 1]) = head of [1, 2] = 1
    assert apply(mod, :g, []) == {:S, :Z}
  end
end
