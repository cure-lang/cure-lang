defmodule Antigen.Generators.ErasureTerm do
  @moduledoc """
  Fixed catalogs of Core terms + mixed-quantity envs for the
  `Antigen.Assays.Erasure` families (spec: antigen-erasure-relevance). Mirrors the
  established fixed-catalog pattern (deterministic, no corpus banking).

    * `erase_challenges/0` — ONLY terms expected `:ok` under real ops: present-first
      ctor (idempotent, hole-free, wellformed), present-first app-head (idempotent),
      and selective (ctor + app-head, leaf args). The erased-first `:MkP`/`:g`
      terms — which surface the real `erase/2` non-idempotence bug — are NOT here;
      they are dedicated known-finding fixtures in `erasure_test.exs`.
    * `relevance_challenges/0` — the four per-site rejected bodies + a clean control.
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.{Env, Inductive}

  defp il(n), do: {:int_lit, n}

  # ctor :MkQ present-first [:unrestricted,:erased] (erase idempotent — CLEAN);
  # :MkP erased-first [:erased,:unrestricted] is declared too (used only by test fixtures).
  defp ctor_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:P, [], [], 0), [
      Inductive.ctor(:MkQ, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:unrestricted, :erased]),
      Inductive.ctor(:MkP, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:erased, :unrestricted])
    ])
  end

  defp app_env(env) do
    ty =
      {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
       {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

    env |> Env.add_def(:f, ty, {:int_lit, 0}, [:unrestricted, :erased])
  end

  defp app2(head, x0, x1), do: {:app, {:app, head, x0}, x1}

  defp runtime_case(scrutinee),
    do: {:case, scrutinee, il(0), [{:MkQ, 2, il(0)}, {:MkP, 2, il(0)}]}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). The relevance catalog's shape-
  classes are the four per-site rejected bodies (an erased binder returned, applied,
  scrutinised, or passed to a present ctor arg) plus the clean control. Only the
  `relevance/soundness` assay is onboarded here (the erase catalog is a separate
  assay family).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [:returned, :applied, :scrutinee, :present_arg, :clean_control],
        do: {"relevance/soundness", cell}
  end

  @doc """
  Uniform sampleable generator over the relevance catalog (this vertical is otherwise
  seed-test–fed). Used by the coverage-manifest gate to confirm every declared cell
  is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(relevance_challenges())
  end

  defp ch(assay, payload, seed) do
    Challenge.new(kind: :erasure_term, assay: assay, label: :positive, payload: payload, seed: seed)
  end

  @doc "V4a erase catalog — clean entries only (see moduledoc / reconciliation #1)."
  @spec erase_challenges() :: [Challenge.t()]
  def erase_challenges do
    cenv = ctor_env()
    aenv = app_env(ctor_env())
    ctor_t = {:ctor, :MkQ, [il(1), il(2)]}
    app_t = app2({:global, :f}, il(1), il(2))

    [
      ch("erasure/idempotent", %{env: cenv, term: ctor_t}, 0),
      ch("erasure/idempotent", %{env: aenv, term: app_t}, 1),
      ch("erasure/selective", %{env: cenv, term: ctor_t, surface: :ctor}, 2),
      ch("erasure/selective", %{env: aenv, term: app_t, surface: :app}, 3),
      ch("erasure/wellformed", %{env: cenv, term: ctor_t}, 4)
    ]
  end

  @doc "V4b relevance catalog — one rejected body per site + a clean control."
  @spec relevance_challenges() :: [Challenge.t()]
  def relevance_challenges do
    e = Env.empty()
    cenv = ctor_env()

    [
      rel(e, {:var, 0}, :returned, 0),
      rel(e, {:app, {:var, 0}, il(0)}, :applied, 1),
      rel(cenv, runtime_case({:var, 0}), :scrutinee, 2),
      rel(cenv, {:ctor, :MkQ, [{:var, 0}, il(0)]}, :present_arg, 3),
      Challenge.new(
        kind: :erasure_term,
        assay: "relevance/soundness",
        label: :positive,
        payload: %{env: e, name: :d, quantities: [:erased], body: il(7), site: nil},
        seed: 4,
        cover_tag: :clean_control
      )
    ]
  end

  defp rel(env, body, site, seed) do
    Challenge.new(
      kind: :erasure_term,
      assay: "relevance/soundness",
      label: :negative,
      payload: %{env: env, name: :d, quantities: [:erased], body: body, site: site},
      seed: seed,
      cover_tag: site
    )
  end
end
