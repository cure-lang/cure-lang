defmodule Antigen.Generators.Rewrite do
  @moduledoc """
  Known-label equality generator (spec 2026-07-02-antigen-eq-rewrite), retargeted
  to the inductive identity type (Phase C, spec 2026-07-04): `Equivalent`
  formation, `reflexive` typing, and the J/subst `:case` transport
  (`{:app, {:case, proof, arrow-motive, [reflexive-branch λh.h]}, body}`) that
  replaced the retired primitive `{:eq}`/`{:refl}`/`{:rewrite}` Core forms.
  Each builder hand-constructs a Core def whose `:well_typed`/`:ill_typed`
  label is correct by construction; `Assays.Rewrite` checks the kernel accepts
  iff well-typed. No elaborator, no term generator.

  The obligations are the SAME four verticals as the primitive-era file —
  formation endpoint typing, reflexive's two conversion conjuncts, the
  transport premise (proof-is-an-equality + body-at-M[a]), and transport
  result-type correctness — re-expressed on the inductive vehicle: the
  proof-not-eq guard is now the kernel's `:foreign_ctor` (a `reflexive` branch
  cannot eliminate a non-Equivalent scrutinee), and the premise/result checks
  ride the transport's Π type `(M@a) -> (M@b)`.
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.{Env, Inductive}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`) — one per obligation variant.
  The four verticals split into their argument variants (not just well/ill), because
  `refl_typing`/`rewrite_premise`/`transport_type` each carry ≥2 same-label shapes
  (e.g. `:base` and `:redex` are both well-typed). Each builder stamps its own cell.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :eq_formation_well_typed,
          :eq_formation_ill_typed,
          :refl_typing_base,
          :refl_typing_redex,
          :refl_typing_conjunct1_violation,
          :refl_typing_conjunct2_violation,
          :rewrite_premise_well_typed,
          :rewrite_premise_proof_not_eq,
          :rewrite_premise_body_mismatch,
          :transport_type_transport_correct,
          :transport_type_refl_coherence,
          :transport_type_left_at_source
        ],
        do: {"rewrite/eq", cell}
  end

  @doc """
  Uniform sampleable generator over the vertical's hand-built transport challenges
  (this vertical is otherwise curated / seed-test-fed). Used by the coverage-manifest
  gate to confirm every declared cell is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of([
      eq_formation(:well_typed),
      eq_formation(:ill_typed),
      refl_typing(:base),
      refl_typing(:redex),
      refl_typing(:conjunct1_violation),
      refl_typing(:conjunct2_violation),
      rewrite_premise(:well_typed),
      rewrite_premise(:proof_not_eq),
      rewrite_premise(:body_mismatch),
      transport_type(:transport_correct),
      transport_type(:refl_coherence),
      transport_type(:left_at_source)
    ])
  end

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @dcoupled {:ctor, :Dcoupled, []}

  # -- shared families (duplicated from Generators.Indexed; those are defp) ----
  defp dec_family,
    do: {Inductive.family(:Dec, [], [], 0), [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  # P : Dec -> Type, an empty (constructor-free) index family; `P a` is a valid
  # type whose inhabitants are only ever hypotheses (Pi domains). Used as the
  # transport motive family in 4.3/4.4.
  defp p_family, do: {Inductive.family(:P, [], [{:n, @dec}], 0), []}

  # Equivalent itself — byte-mirror of core/builtins.ex's eq_family/eq_ctors
  # (the challenge env is rebuilt from Env.empty, which has no builtins).
  defp eq_family,
    do:
      {Inductive.family(:Equivalent, [a: {:type, 0}], [x: {:var, 0}, y: {:var, 1}], 0),
       [Inductive.ctor(:reflexive, [w: {:var, 0}], [{:var, 0}, {:var, 0}], [:erased], [{:var, 1}])]}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # J/subst transport for CLOSED ty/motive/l (shifts of closed terms elided) —
  # mirrors the elaborator's `transport_case/4`.
  defp transport(proof, ty, motive, l) do
    scrut_ty = {:data, :Equivalent, [ty], [{:var, 1}, {:var, 0}]}
    arrow = {:pi, Cure.Core.Grade.unrestricted(), {:app, motive, {:var, 2}}, {:app, motive, {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), ty, {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    {:case, proof, arrow_motive,
     [{:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, l}, {:var, 0}}}]}
  end

  # -- 4.1 Equivalent formation ------------------------------------------------
  @doc """
  Formation obligation. The `Equivalent` type sits in a Pi domain so check_def's
  type-formation pass checks both endpoints against the carrier.
  """
  @spec eq_formation(:well_typed | :ill_typed) :: Challenge.t()
  def eq_formation(:well_typed) do
    eq = {:data, :Equivalent, [@dec], [@causal, @dcoupled]}

    challenge(
      :well_typed,
      [dec_family(), eq_family()],
      :eq_formation,
      {:pi, Cure.Core.Grade.unrestricted(), eq, @dec},
      {:lam, Cure.Core.Grade.unrestricted(), eq, @causal},
      "Equivalent Dec Causal Dcoupled — both endpoints : Dec",
      :eq_formation_well_typed
    )
  end

  def eq_formation(:ill_typed) do
    eq = {:data, :Equivalent, [@dec], [@causal, {:ctor, :MkFoo, []}]}

    challenge(
      :ill_typed,
      [dec_family(), foo_family(), eq_family()],
      :eq_formation,
      {:pi, Cure.Core.Grade.unrestricted(), eq, @dec},
      {:lam, Cure.Core.Grade.unrestricted(), eq, @causal},
      "ill-typed: Equivalent Dec Causal MkFoo — MkFoo : Foo, not Dec",
      :eq_formation_ill_typed
    )
  end

  # -- 4.2 reflexive typing + reflexive-conversion guard -----------------------
  @spec refl_typing(:base | :redex | :conjunct1_violation | :conjunct2_violation) :: Challenge.t()
  # base: reflexive Causal : Equivalent Dec Causal Causal, checked in a def.
  def refl_typing(:base) do
    eq = {:data, :Equivalent, [@dec], [@causal, @causal]}

    challenge(
      :well_typed,
      [dec_family(), eq_family()],
      :refl_typing,
      eq,
      {:ctor, :reflexive, [@causal]},
      "reflexive Causal : Equivalent Dec Causal Causal",
      :refl_typing_base
    )
  end

  # redex: endpoint is a redex that normalizes to Causal — conv is up-to-nf.
  def refl_typing(:redex) do
    redex = {:app, {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}, @causal}
    eq = {:data, :Equivalent, [@dec], [@causal, redex]}

    challenge(
      :well_typed,
      [dec_family(), eq_family()],
      :refl_typing,
      eq,
      {:ctor, :reflexive, [@causal]},
      "reflexive Causal against Equivalent Dec Causal ((λx.x) Causal) — conv up-to-normalization",
      :refl_typing_redex
    )
  end

  # conjunct-1 violation: endpoints not convertible (Causal vs Dcoupled).
  def refl_typing(:conjunct1_violation) do
    eq = {:data, :Equivalent, [@dec], [@causal, @dcoupled]}

    challenge(
      :ill_typed,
      [dec_family(), eq_family()],
      :refl_typing,
      eq,
      {:ctor, :reflexive, [@causal]},
      "ill-typed: reflexive Causal : Equivalent Dec Causal Dcoupled — endpoints not convertible (conjunct 1)",
      :refl_typing_conjunct1_violation
    )
  end

  # conjunct-2 violation: endpoints equal to each other (Dcoupled,Dcoupled) so
  # conjunct 1 holds, but reflexive's witness Causal isn't convertible to them.
  def refl_typing(:conjunct2_violation) do
    eq = {:data, :Equivalent, [@dec], [@dcoupled, @dcoupled]}

    challenge(
      :ill_typed,
      [dec_family(), eq_family()],
      :refl_typing,
      eq,
      {:ctor, :reflexive, [@causal]},
      "ill-typed: reflexive Causal : Equivalent Dec Dcoupled Dcoupled — conjunct 1 holds, witness≠endpoints (conjunct 2)",
      :refl_typing_conjunct2_violation
    )
  end

  # -- 4.3 transport premise discipline -----------------------------------------
  # Motive M = λx:Dec. P x; the equality proof is a hypothesis p : Equivalent
  # Dec Causal Dcoupled (no ground proof exists, so it must be assumed). de
  # Bruijn under `[p, h]`: `h`=var0, `p`=var1.
  @p_causal {:data, :P, [], [{:ctor, :Causal, []}]}
  @p_dcoupled {:data, :P, [], [{:ctor, :Dcoupled, []}]}
  @motive {:lam, Cure.Core.Grade.unrestricted(), @dec, {:data, :P, [], [{:var, 0}]}}
  @eq_cd {:data, :Equivalent, [@dec], [{:ctor, :Causal, []}, {:ctor, :Dcoupled, []}]}

  @spec rewrite_premise(:well_typed | :proof_not_eq | :body_mismatch) :: Challenge.t()
  # def : Π(p:Equivalent Dec Causal Dcoupled). Π(h:P Causal). P Dcoupled
  #     = λp.λh. transport p (λx.P x) @ h
  def rewrite_premise(:well_typed) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @eq_cd, {:pi, Cure.Core.Grade.unrestricted(), @p_causal, @p_dcoupled}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @eq_cd,
       {:lam, Cure.Core.Grade.unrestricted(), @p_causal,
        {:app, transport({:var, 1}, @dec, @motive, @causal), {:var, 0}}}}

    challenge(
      :well_typed,
      [dec_family(), p_family(), eq_family()],
      :rewrite_premise,
      dt,
      body,
      "transport p (λx.P x) h : P Dcoupled from h : P Causal",
      :rewrite_premise_well_typed
    )
  end

  # proof is `h : P Causal`, not an equality → the reflexive branch cannot
  # eliminate a P scrutinee (:foreign_ctor — the :case analog of ensure_eq).
  def rewrite_premise(:proof_not_eq) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @p_causal, @p_causal}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @p_causal, {:app, transport({:var, 0}, @dec, @motive, @causal), {:var, 0}}}

    challenge(
      :ill_typed,
      [dec_family(), p_family(), eq_family()],
      :rewrite_premise,
      dt,
      body,
      "ill-typed: transport proof is h : P Causal, not an Equivalent — reflexive branch is foreign",
      :rewrite_premise_proof_not_eq
    )
  end

  # proof IS a genuine equality (so we reach the argument check), but the body
  # `Causal : Dec` does not check at M a = P Causal.
  def rewrite_premise(:body_mismatch) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @eq_cd, @p_dcoupled}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @eq_cd,
       {:app, transport({:var, 0}, @dec, @motive, @causal), {:ctor, :Causal, []}}}

    challenge(
      :ill_typed,
      [dec_family(), p_family(), eq_family()],
      :rewrite_premise,
      dt,
      body,
      "ill-typed: transported body Causal:Dec, not P Causal — premise check fails at the app",
      :rewrite_premise_body_mismatch
    )
  end

  # -- 4.4 transport result-type correctness ----------------------------------
  @spec transport_type(:transport_correct | :refl_coherence | :left_at_source) :: Challenge.t()
  # identical body to 4.3 well-typed; the point is the DECLARED codomain P Dcoupled.
  def transport_type(:transport_correct) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @eq_cd, {:pi, Cure.Core.Grade.unrestricted(), @p_causal, @p_dcoupled}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @eq_cd,
       {:lam, Cure.Core.Grade.unrestricted(), @p_causal,
        {:app, transport({:var, 1}, @dec, @motive, @causal), {:var, 0}}}}

    challenge(
      :well_typed,
      [dec_family(), p_family(), eq_family()],
      :transport_type,
      dt,
      body,
      "declared P Dcoupled; the transport's Π moves the type to M b",
      :transport_type_transport_correct
    )
  end

  # refl coherence: transport (reflexive Causal) (λx.P x) @ h : P Causal (b = a).
  # The proof sits in inference position (case scrutinee), so it rides the
  # params-on-spine form here. NB (task #14): the spine form is no longer an
  # inference-position-only artifact — `check` now subsumes infer+conv on the
  # spine arity, so a params-on-spine reflexive is also checkable directly.
  def transport_type(:refl_coherence) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @p_causal, @p_causal}
    proof = {:ctor, :reflexive, [@dec, {:ctor, :Causal, []}]}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @p_causal, {:app, transport(proof, @dec, @motive, @causal), {:var, 0}}}

    challenge(
      :well_typed,
      [dec_family(), p_family(), eq_family()],
      :transport_type,
      dt,
      body,
      "transport (reflexive Causal) M h : P Causal — vacuous transport",
      :transport_type_refl_coherence
    )
  end

  # left-at-source: SAME transport body but declared codomain P Causal (= M a).
  # The kernel must reject: the transport yields P Dcoupled ≢ P Causal.
  def transport_type(:left_at_source) do
    dt = {:pi, Cure.Core.Grade.unrestricted(), @eq_cd, {:pi, Cure.Core.Grade.unrestricted(), @p_causal, @p_causal}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @eq_cd,
       {:lam, Cure.Core.Grade.unrestricted(), @p_causal,
        {:app, transport({:var, 1}, @dec, @motive, @causal), {:var, 0}}}}

    challenge(
      :ill_typed,
      [dec_family(), p_family(), eq_family()],
      :transport_type,
      dt,
      body,
      "ill-typed: declared P Causal but the transport yields P Dcoupled — accepting = no transport",
      :transport_type_left_at_source
    )
  end

  defp challenge(label, families, name, def_type, def_body, note, cell) do
    Challenge.new(
      kind: :rewrite_eq,
      assay: "rewrite/eq",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note,
      cover_tag: cell
    )
  end
end
