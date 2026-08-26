defmodule Cure.Elab.UnifyWhnfTest do
  @moduledoc """
  Meta-aware weak-head normalization used by the unifier (#11, whnf-before-compare).
  `whnf_meta_aware/5` reduces a Core term to whnf while treating unsolved
  metavariables as opaque neutrals (they block a match/case scrutinee but pass
  through elsewhere), by substituting each `{:meta, id}` with a reserved opaque
  global before reusing the trusted `Normalise` reduction, then mapping back.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{MetaCtx, Program, Unify}

  # A real, totality-certified signature with `plus` defined by pattern matching.
  # `Program.elaborate/1` returns the `Core.Env` signature directly.
  @src "mod M\n" <>
         "  type Nat = Z | S(Nat)\n" <>
         "  fn plus(a: Nat, b: Nat) -> Nat = match a\n" <>
         "    Z() -> b\n" <>
         "    S(k) -> S(plus(k, b))\n" <>
         "end\n"

  defp sig_with_plus do
    {:ok, sig} = Program.elaborate(@src)
    sig
  end

  @z {:ctor, :"M#Z", []}
  defp s(t), do: {:ctor, :"M#S", [t]}
  defp plus(a, b), do: {:app, {:app, {:global, :"M#plus"}, a}, b}

  test "reduces plus(Z, ?m) to ?m — the meta passes through the Z-branch untouched" do
    assert Unify.whnf_meta_aware(plus(@z, {:meta, 0}), MetaCtx.new(), sig_with_plus()) ==
             {:meta, 0}
  end

  test "leaves plus(?m, Z) stuck — the meta is in the scrutinee position (blocks reduction)" do
    t = plus({:meta, 0}, @z)
    assert Unify.whnf_meta_aware(t, MetaCtx.new(), sig_with_plus()) == t
  end

  test "on a meta-free reducible term, reduces to the whnf head (plus(Z, S(Z)) -> S(Z))" do
    assert Unify.whnf_meta_aware(plus(@z, s(@z)), MetaCtx.new(), sig_with_plus()) == s(@z)
  end

  test "falls back to the zonked input on :fuel_exhausted (never crashes, never fabricates)" do
    # A nested redex whose whnf needs several unfolds: plus(Z, plus(Z, plus(Z, S(Z))))
    # → S(Z), but a fuel budget of 1 exhausts first, so the helper returns the
    # (zonked = identity here, meta-free) input unchanged.
    deep = plus(@z, plus(@z, plus(@z, s(@z))))
    assert Unify.whnf_meta_aware(deep, MetaCtx.new(), sig_with_plus(), 0, fuel: 1) == deep
  end
end
