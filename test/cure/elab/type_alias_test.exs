defmodule Cure.Elab.TypeAliasTest do
  @moduledoc """
  Type aliases (Idris parity). `type MyNat = Nat` used to be silently dropped —
  `Program.declarations/1` kept only `:container`/`:indexed_type` nodes, so the
  `:type_annotation` alias never reached the declaration elaborator and `MyNat`
  resolved to an opaque `{:global, MyNat}` that would not convert to `Nat`. The
  alias is now registered as a nullary definition `MyNat : Type := Nat`, which
  conversion δ-unfolds — so the alias is interchangeable with its right-hand side
  in any position the kernel resolves by *conversion*: parameter types, return
  types, and constructor/value arguments. Oracle `alias/al01_type_alias` pins
  accept/accept.

  Positions where an elaborator/kernel rule inspects the type's *head* without
  first weak-head-normalising it — `match` on an alias-typed scrutinee (the kernel
  `:case` rule) and applying an alias of a function type (the kernel's `ensure_pi`)
  — are NOT yet covered: those unfoldings live in the trusted kernel and are gated
  pending review. This test pins only the conversion-based surface that works today.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "an alias is accepted as a parameter type and a return type" do
    src = @nat <> "  type MyNat = Nat\n  fn f(n: MyNat) -> MyNat = S(n)\n  fn g() -> Nat = f(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AliasFG", functions: [:f, :g])

    # f(S(Z)) = S(S(Z)); the alias MyNat converts to Nat on the way in and out.
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "a value of the aliased type is accepted where the underlying type is expected" do
    # `n : MyNat` is passed to `pred : Nat -> Nat`; conversion unfolds MyNat to Nat.
    src =
      @nat <>
        "  type MyNat = Nat\n  fn pred(m: Nat) -> Nat = match m\n    S(k) -> k\n    Z() -> Z()\n" <>
        "  fn f(n: MyNat) -> Nat = pred(n)\n  fn g() -> Nat = f(S(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AliasVal", functions: [:pred, :f, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end
end
