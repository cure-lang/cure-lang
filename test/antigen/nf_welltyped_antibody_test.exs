defmodule Antigen.NfWellTypedAntibodyTest do
  @moduledoc """
  TCB antibody — Normalise readback preserves well-typedness for indexed
  families. The signature-less reify collapses an indexed family's param/index
  split (Equivalent 1-param/2-index → {:data,:Equivalent,[ty,a,b],[]}), which
  fails re-inference :arg_arity. B1 makes all four Normalise reify sites
  signature-aware.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context, Normalise}
  alias Cure.Elab.Program

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  @nat {:data, :"Std.Nat#Nat", [], []}
  defp z, do: {:ctor, :Z, []}

  # B4.i — nf of the FAMILY TYPE itself (not a proof of it). IMPORTANT (verified
  # by hand-trace, 2026-07-09 review — the originally-drafted construction used
  # a bare fields-only ctor term, `t = {:ctor, :reflexive, [z()]}`, as the thing
  # to `Kernel.infer`; that is REJECTED unconditionally by kernel.ex's ctor-arity
  # `cond` (`{:error, {:ctor_requires_checking_mode, :Equivalent}}`) whenever the
  # family has params (Equivalent has 1) and the ctor term is bare fields-only in
  # INFERENCE position — `{:ok, ty} = Kernel.infer(ctx, t)` crashes via MatchError
  # for that reason, BOTH before and after B1, since B1 never touches
  # `Kernel.infer`'s ctor dispatch. That construction can never go green and
  # proves nothing about the readback bug — replaced below). The flat-collapse
  # bug is specifically about reifying a `{:vdata,...}` VALUE (a family TYPE),
  # so the antibody must nf the TYPE term directly, then re-check the normal
  # form is still well-formed.
  test "B4.i: nf of an indexed-family TYPE term stays well-formed" do
    sig = base_sig()
    ctx = Context.empty(sig)
    # Equivalent(Nat, Z, Z) : Type
    ty_term = {:data, :Equivalent, [@nat], [z(), z()]}
    assert {:ok, _sort} = Kernel.infer(ctx, ty_term)
    normal = Normalise.nf(ctx, ty_term)
    # Pre-B1: reify has no signature, so params++indices (1+2=3 combined values)
    # all land in `params`; re-inferring against Equivalent's 1-param telescope
    # is an arity mismatch — `check_spine` (kernel.ex:470-475) returns
    # `{:error, :arg_arity}`. Post-B1: reify recovers the 1-param/2-index split
    # and re-inference succeeds.
    assert match?({:ok, _}, Kernel.infer(ctx, normal))
  end

  # B4.ii — idempotence retained on the same TYPE shape (regression guard: must
  # not flip under B1's signature-aware reify — same construction as B4.i, since
  # only a `:vdata` value's readback is sensitive to the split at all).
  test "B4.ii: nf is idempotent on the indexed-family TYPE shape" do
    sig = base_sig()
    ctx = Context.empty(sig)
    ty_term = {:data, :Equivalent, [@nat], [z(), z()]}
    once = Normalise.nf(ctx, ty_term)
    assert Normalise.nf(ctx, once) == once
  end

  # B4.iii — the SAME TYPE shape nested under a binder exercises quote_nf
  # (:177), a different code path than nf's top-level reify (normalise.ex:142-154
  # `nf_struct`'s `:vlam` clause reifies the body via `quote_nf`, not directly).
  # As with B4.i, the body must be a TYPE-valued term (`Equivalent(Nat,x,x)`),
  # not a ctor/proof term — a fields-only `reflexive x` body hits the identical
  # `:ctor_requires_checking_mode` crash as the original B4.i draft (same root
  # cause, same fix).
  test "B4.iii: nf of a binder body containing an indexed-family TYPE re-checks" do
    sig = base_sig()
    ctx = Context.empty(sig)
    # λx:Nat. Equivalent(Nat, x, x) : Nat -> Type
    lam = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:data, :Equivalent, [@nat], [{:var, 0}, {:var, 0}]}}
    {:ok, ty} = Kernel.infer(ctx, lam)
    normal = Normalise.nf(ctx, lam)
    assert Kernel.check(ctx, normal, ty) == :ok
  end
end
