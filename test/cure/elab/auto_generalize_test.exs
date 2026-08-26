defmodule Cure.Elab.AutoGeneralizeTest do
  @moduledoc """
  Idris-style auto-generalization of free type variables (Idris parity). A free
  lowercase type variable in a signature (`fn id(x: a) -> a`) that is not bound as
  a parameter and is not a known family is bound as a leading implicit `{a: Type}`
  (erased), in order of first appearance — so `id`, `const`, and function-type
  HOFs type without the programmer writing the `{a}` binder explicitly.

  Generalization is restricted to occurrences of kind `Type`: a whole parameter or
  return type, a function-type domain/codomain, or a family *parameter* slot whose
  kind is `Type`. An *index* variable (`Vec(a, n)` with `n : Nat`) is deliberately
  NOT generalized, so it cannot be mis-bound at kind `Type`.

  Oracle `func/fn07_autogen_id` + `func/fn08_autogen_hof` pin accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a bare type variable in a parameter and return type generalizes (id)" do
    src = @nat <> "  fn id(x: a) -> a = x\n  fn g() -> Nat = id(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AgId", functions: [:id, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "two distinct bare type variables generalize (const)" do
    src = @nat <> "  fn const(x: a, y: b) -> a = x\n  fn g() -> Nat = const(S(Z()), Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AgConst", functions: [:const, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "type variables under a function type generalize (higher-order)" do
    src =
      @nat <>
        "  fn ap(f: (a) -> b, x: a) -> b = f(x)\n  fn inc(n: Nat) -> Nat = S(n)\n" <>
        "  fn g() -> Nat = ap(inc, S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AgAp", functions: [:ap, :inc, :g])

    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "a type variable in a family parameter slot generalizes (List(a))" do
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n  fn len(l: Lst(a)) -> Nat = match l\n" <>
        "    Cons(x, xs) -> S(len(xs))\n    Nil() -> Z()\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an uppercase name is NOT treated as a type variable" do
    # `a` generalizes, so `id(Z())` checks; `A` is a (concrete, opaque) type, so the
    # same program with an uppercase head is rejected — `Z() : Nat` is not an `A`.
    lower = @nat <> "  fn id(x: a) -> a = x\n  fn g() -> Nat = id(Z())\nend\n"
    upper = @nat <> "  fn id(x: A) -> A = x\n  fn g() -> Nat = id(Z())\nend\n"

    assert {:ok, _} = Program.elaborate(lower)
    assert {:error, _} = Program.elaborate(upper)
  end
end
