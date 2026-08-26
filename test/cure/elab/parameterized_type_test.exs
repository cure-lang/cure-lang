defmodule Cure.Elab.ParameterizedTypeTest do
  @moduledoc """
  Parameterized (polymorphic) data types — `type List(a) = Nil | Cons(a, List(a))`,
  `Maybe`, `Box` (Idris parity). Two gaps were closed:

    * `elaborate_index_telescope` did `Keyword.fetch!(pmeta, :type)`, which *crashed*
      on a bare type parameter (`{:param, [], "a"}` — no explicit kind), so even a
      parameterized GADT (`type Vec(a) indices …`) raised `KeyError`. A bare
      parameter ranges over types, so its kind now defaults to `Type`.
    * the `:enum` container elaborator ignored `type_params` entirely. A
      parameterized enum's positional variants are now synthesized into GADT
      constructor signatures (each returning the family applied to its own
      parameters) and elaborated through the shared parameterized-family path with
      an empty index telescope.

  Oracle `poly/pl01_maybe` + `poly/pl02_list` pin accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a single-parameter box constructs, matches, and runs" do
    src =
      @nat <>
        "  type Box(a) = MkBox(a)\n  fn un(b: Box(Nat)) -> Nat = match b\n    MkBox(x) -> x\n" <>
        "  fn g() -> Nat = un(MkBox(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PBox", functions: [:un, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a Maybe-shaped type with a nullary and a unary constructor runs" do
    src =
      @nat <>
        "  type Opt(a) = None | Some(a)\n  fn get(d: Nat, o: Opt(Nat)) -> Nat = match o\n" <>
        "    Some(x) -> x\n    None() -> d\n  fn g() -> Nat = get(Z(), Some(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.POpt", functions: [:get, :g])

    # get(Z, Some(S(Z))) = S(Z).
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a recursive polymorphic list constructs, matches, and runs" do
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n  fn hd(d: Nat, l: Lst(Nat)) -> Nat = match l\n" <>
        "    Cons(x, xs) -> x\n    Nil() -> d\n  fn g() -> Nat = hd(Z(), Cons(S(Z()), Nil()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PList", functions: [:hd, :g])

    # hd(Z, Cons(S(Z), Nil)) = S(Z).
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a nullary polymorphic constructor in return position solves its parameter from the goal" do
    # `None()` / `Nil()` have no argument to infer their type parameter from; the
    # declared return type is the only source, so the body is elaborated in
    # checking mode. (A nested underdetermined constructor — `Cons(Z(), Nil())` in
    # return position — is covered by the next test.)
    src =
      @nat <>
        "  type Opt(a) = None | Some(a)\n  fn empty() -> Opt(Nat) = None()\n" <>
        "  fn g() -> Nat = match empty()\n    Some(x) -> x\n    None() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PEmpty", functions: [:empty, :g])

    # `None` erases to the OTP-lowercase tag `:none` (the otp_tag rule applies
    # to the constructor name wherever it is declared, not just in the stdlib).
    assert apply(mod, :empty, []) == :none
    assert apply(mod, :g, []) == :Z
  end

  test "an underdetermined nested constructor in return position checks against the goal" do
    # `Cons(Z(), Nil())` at `-> Lst(Nat)`: the inner `Nil()` cannot be inferred, so
    # the inference path fails and the bidirectional fallback pins the parameter
    # `a = Nat` from the expected type, then checks each argument against its field
    # type (`Z()` against `Nat`, `Nil()` against `Lst(Nat)`). Nesting recurses.
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n" <>
        "  fn two() -> Lst(Nat) = Cons(Z(), Cons(S(Z()), Nil()))\n" <>
        "  fn hd(d: Nat, l: Lst(Nat)) -> Nat = match l\n    Cons(x, xs) -> x\n    Nil() -> d\n" <>
        "  fn g() -> Nat = hd(S(S(Z())), two())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PNested", functions: [:two, :hd, :g])

    # head of [Z, S(Z)] is Z.
    assert apply(mod, :g, []) == :Z
  end

  test "a nested constructor with a wrong element type is rejected" do
    assert {:error, _} =
             Program.elaborate(
               @nat <>
                 "  type Lst(a) = Nil | Cons(a, Lst(a))\n" <>
                 "  fn bad() -> Lst(Lst(Nat)) = Cons(Z(), Nil())\nend\n"
             )
  end

  test "a nested constructor infers standalone as an argument to a polymorphic call" do
    # `app(Cons(Z(), Nil()), …)`: the first argument must itself pin `app`'s
    # implicit `a` (no earlier argument does), so `Cons(Z(), Nil())` has to infer
    # standalone in inference position — `Z() : Nat` fixes the parameter, then
    # `Nil()` checks against `Lst(Nat)`. Oracle `poly/pl09_append_nested_args`.
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n" <>
        "  fn app({a}, xs: Lst(a), ys: Lst(a)) -> Lst(a) = match xs\n" <>
        "    Nil() -> ys\n    Cons(x, r) -> Cons(x, app(r, ys))\n" <>
        "  fn hd(d: Nat, l: Lst(Nat)) -> Nat = match l\n    Cons(x, xs) -> x\n    Nil() -> d\n" <>
        "  fn g() -> Nat = hd(Z(), app(Cons(S(Z()), Nil()), Cons(Z(), Nil())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AppNested", functions: [:app, :hd, :g])

    # head of app([S(Z)], [Z]) = head of [S(Z), Z] = S(Z)
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a polymorphic list's Nil constructs at an annotated return type" do
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n  fn empty_list() -> Lst(Nat) = Nil()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PNil", functions: [:empty_list])

    assert apply(mod, :empty_list, []) == :Nil
  end

  test "a bare-parameter GADT (Vec) no longer crashes the elaborator" do
    # Regression guard for the Keyword.fetch!(:type) crash on `{:param, [], \"a\"}`.
    src =
      @nat <>
        "  type Vec(a) indices (n: Nat)\n    VNil : Vec(a, Z)\n" <>
        "    VCons : a -> Vec(a, n) -> Vec(a, S(n))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
