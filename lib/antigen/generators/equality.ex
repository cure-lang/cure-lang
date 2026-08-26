defmodule Antigen.Generators.Equality do
  @moduledoc """
  Structure-directed generator for the **propositional-equality fragment** —
  the inductive identity type `{:data, :Equivalent, [ty], [a, b]}`, its
  constructor `{:ctor, :reflexive, …}` (fields-only in checking position,
  params-on-spine `[ty, a]` in inference position, K6 §E.1), and the J/subst
  `:case` transport (`{:app, {:case, proof, arrow-motive, [reflexive-branch]},
  body}`) that replaced the retired primitive `{:refl}`/`{:eq}`/`{:rewrite}`
  forms (spec 2026-07-04, Phase C). This is the reachability lever for the
  kernel's equality paths, which the mode-directed `Generators.Term` never
  emits: Equivalent formation via `infer({:data,…})`, spine-reflexive
  inference, reflexive checking (`check_ctor_app` + endpoint conversion), and
  case-transport elimination (`branch_unify` over the reflexive index pair).

  Every term is well-typed **by construction** over the v1 signature: operands
  are closed inhabitants of the numeric / menu-datatype menu, and the claimed
  `type` is exactly what `infer` returns.

  HISTORICAL (pre task #14, spec 2026-07-09-infer-check-coherence): terms used
  to stay inside the kernel's COHERENT fragment (infer(t)=A ⟹ check(t,A)=:ok)
  by construction — a bare params-on-spine reflexive was deliberately NOT
  generated at top level, because the checking-mode `{:ctor}` clause rejected
  the spine arity (`:ctor_arity`) that inference mode accepts (a known
  infer/check asymmetry; spine reflexives appeared only in inference positions,
  i.e. case scrutinees). That asymmetry is now FIXED — `check` subsumes
  `infer`+conv on the spine arity — so the spine reflexive now generates in
  BOTH positions (a top-level bare spine reflexive AND a checking-position
  embedding), and the `term/infer_check` + `term/subject_reduction` assays
  patrol the widened, no-longer-artificially-coherent space.

    * `Equivalent ty a b`                                → `Type 0`
    * `transport (reflexive ty a) (λ_. Nat) @ n`         → `Nat`
    * `transport (reflexive ty a) (λ_. Eq ty a a) @ (reflexive a)`
                                                         → `Equivalent ty a a`
    * `Equivalent ty s s` (neutral `s`, one-binder ctx)  → `Type 0`
      (the claimed-vs-inferred conversion walks `s ≡ s` through Conv's
      neutral paths: nprim / nfst / nsnd / ncase)
  """
  alias Antigen.{Gen, Challenge}

  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]
  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @bool {:data, :Bool, [], []}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(eq_term(), fn {term, type, ctx} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: ctx, type: type, term: term},
            note: "propositional equality (inductive Equivalent)"
          )
        )
      end)
    end)
  end

  # -- term + its inferred type + the context it lives in ---------------------
  defp eq_term do
    Gen.frequency([
      {3, eq_type_term()},
      {2, transport_nat_term()},
      {2, checked_refl_transport_term()},
      {2, spine_refl_term()},
      {2, checked_spine_refl_term()},
      {3, neutral_eq_prop_term()}
    ])
  end

  # Task #14: a bare params-on-spine reflexive at TOP level — the K6 inference
  # spelling that used to sit outside the coherent fragment. `infer` yields the
  # Equivalent vdata; the `term/infer_check` assay now round-trips it back
  # through `check` (previously `:ctor_arity`, now `:ok`). The claimed type uses
  # the SPLIT `params`/`indices` spelling: since B1 (signature-aware readback),
  # `Normalise.quote` recovers the 1-param/2-index split, so the claim must match.
  defp spine_refl_term do
    Gen.bind(inhabitant(), fn {a, ty} ->
      Gen.return({{:ctor, :reflexive, [ty, a]}, {:data, :Equivalent, [ty], [a, a]}, []})
    end)
  end

  # Task #14: the spine reflexive in CHECKING position — embedded as the argument
  # of an identity lambda whose domain is the Equivalent type (the check-embedding
  # idiom, `mutation.ex:141-148` precedent). `infer` on the `:app` drives
  # `check(spine_refl, vdata)` — the exact site the coherence fix repaired.
  defp checked_spine_refl_term do
    Gen.bind(inhabitant(), fn {a, ty} ->
      spine_refl = {:ctor, :reflexive, [ty, a]}
      eq_ty = {:data, :Equivalent, [ty], [a, a]}
      Gen.return({{:app, {:lam, Cure.Core.Grade.unrestricted(), eq_ty, {:var, 0}}, spine_refl}, eq_ty, []})
    end)
  end

  # Equivalent ty a b : Type 0  (a, b share the same type ty — a well-typed
  # proposition, true or false)
  defp eq_type_term do
    Gen.bind(typed_pair(), fn {a, b, ty} ->
      Gen.return({{:data, :Equivalent, [ty], [a, b]}, {:type, 0}, []})
    end)
  end

  # J/subst transport with a constant Nat motive over a spine-reflexive proof:
  # transport (reflexive ty a) (λ_:ty. Nat) @ n : Nat. Exercises spine-refl
  # inference (case scrutinee), branch unification, and app elimination.
  defp transport_nat_term do
    Gen.bind(inhabitant(), fn {a, ty} ->
      Gen.bind(nat_numeral(), fn n ->
        proof = {:ctor, :reflexive, [ty, a]}

        {{:app, transport(proof, ty, {:lam, Cure.Core.Grade.unrestricted(), ty, @nat}, a), n}, @nat, []}
        |> Gen.return()
      end)
    end)
  end

  # Same transport skeleton, but the motive's result is an Equivalent type and
  # the transported body is a CHECKING-position fields-only reflexive:
  # transport (reflexive ty a) (λ_. Eq ty a a) @ (reflexive a) : Eq ty a a.
  defp checked_refl_transport_term do
    Gen.bind(inhabitant(), fn {a, ty} ->
      proof = {:ctor, :reflexive, [ty, a]}
      eq_ty = {:data, :Equivalent, [ty], [a, a]}
      motive = {:lam, Cure.Core.Grade.unrestricted(), ty, eq_ty}
      body = {:ctor, :reflexive, [a]}
      # The claimed type uses the SPLIT `params`/`indices` spelling: since B1
      # (signature-aware readback), `Normalise.quote` recovers the split, so the
      # inferred type reads back split and the claim must match that shape.
      Gen.return({{:app, transport(proof, ty, motive, a), body}, eq_ty, []})
    end)
  end

  # An Equivalent proposition over a NEUTRAL subject (a prim / projection /
  # stuck-case of a context variable). The assay's claimed-vs-inferred
  # conversion compares `s` with itself, driving Conv's neutral machinery
  # (same_neutral_no_delta? / conv_neutral? / conv_branches?). One-binder ctx.
  @int {:data, :Int, [], []}
  @sig_nat {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}

  defp neutral_eq_prop_term do
    Gen.frequency([
      # builtin-op spine over an Int variable → conv_neutral? / same_*_no_delta?
      # generic napp spine congruence (K2 §1.8 — same judgement strength as the
      # retired :nprim clause)
      {2,
       Gen.bind(Gen.member_of([:int_add, :int_sub, :int_mul]), fn g ->
         Gen.bind(int_lit(), fn lit ->
           neutral_eq_prop({:app, {:app, {:global, g}, {:var, 0}}, lit}, @int, [@int])
         end)
       end)},
      {1, neutral_eq_prop({:app, {:global, :int_neg}, {:var, 0}}, @int, [@int])},
      # projections of a Σ variable, now single-branch ι-on-case over mk_pair
      {1,
       neutral_eq_prop(
         {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @sig_nat, @nat}, [{:mk_pair, 2, {:var, 1}}]},
         @nat,
         [@sig_nat]
       )},
      {1,
       neutral_eq_prop(
         {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @sig_nat, @nat}, [{:mk_pair, 2, {:var, 0}}]},
         @nat,
         [@sig_nat]
       )},
      # stuck case over a Bd variable → :ncase + conv_branches? + conv_branch_bodies?
      {2, neutral_case_eq_prop()}
    ])
  end

  defp neutral_eq_prop(subject, ty, ctx),
    do: Gen.return({{:data, :Equivalent, [ty], [subject, subject]}, {:type, 0}, ctx})

  defp neutral_case_eq_prop do
    Gen.bind(nat_numeral(), fn a ->
      Gen.bind(nat_numeral(), fn b ->
        cse = {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @bd, @nat}, [{:T, 0, a}, {:F, 0, b}]}
        neutral_eq_prop(cse, @nat, [@bd])
      end)
    end)
  end

  # J/subst transport for CLOSED ty/motive/l (de Bruijn shifts of closed terms
  # elided) — mirrors the elaborator's `transport_case/4`.
  defp transport(proof, ty, motive, l) do
    scrut_ty = {:data, :Equivalent, [ty], [{:var, 1}, {:var, 0}]}
    arrow = {:pi, Cure.Core.Grade.unrestricted(), {:app, motive, {:var, 2}}, {:app, motive, {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), ty, {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    {:case, proof, arrow_motive,
     [{:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, l}, {:var, 0}}}]}
  end

  # -- closed inhabitants paired with their type ------------------------------
  defp inhabitant do
    Gen.frequency([
      {3, Gen.bind(nat_numeral(), fn n -> Gen.return({n, @nat}) end)},
      {2, Gen.bind(int_lit(), fn n -> Gen.return({n, {:data, :Int, [], []}}) end)},
      {2, Gen.bind(float_lit(), fn f -> Gen.return({f, {:float_type}}) end)},
      {1, Gen.bind(Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}]), fn t -> Gen.return({t, @bd}) end)},
      {1, Gen.bind(Gen.member_of([{:ctor, :False, []}, {:ctor, :True, []}]), fn t -> Gen.return({t, @bool}) end)}
    ])
  end

  # Two inhabitants of the SAME type (for a well-formed Eq proposition).
  defp typed_pair do
    Gen.frequency([
      {3, both(nat_numeral(), @nat)},
      {2, both(int_lit(), {:data, :Int, [], []})},
      {2, both(float_lit(), {:float_type})},
      {1, both(Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}]), @bd)},
      {1, both(Gen.member_of([{:ctor, :False, []}, {:ctor, :True, []}]), @bool)}
    ])
  end

  defp both(value_gen, ty) do
    Gen.bind(value_gen, fn a -> Gen.bind(value_gen, fn b -> Gen.return({a, b, ty}) end) end)
  end

  # -- leaf value generators --------------------------------------------------
  defp nat_numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end

  defp int_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp float_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end
