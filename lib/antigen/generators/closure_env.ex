defmodule Antigen.Generators.ClosureEnv do
  @moduledoc """
  Fixed catalogs of pre-built `%Env{}` challenges for the
  `Antigen.Assays.TotalityClosureAssay` families (spec: antigen-totality-closure).
  Mirrors the elab/normalizer/unifier fixed-catalog pattern (deterministic, no
  corpus banking).

    * `soundness_challenges/0` — a diverging `:loop` in a family-index type
      position, the same in a ctor `result_indices`, and an all-total control env.
      Each def under test is `{:int_type}`-only (no `:data`) so `check_def` needs
      no family registration; the vessel family/ctor is a bare map (never
      kernel-checked by `certify_type_level`).
    * `completeness_challenges/0` — a direct type-position global and a
      transitive-callee global, for which `type_level_fns` and the independent
      reachability walk must agree (subset).
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.Env

  # -- env helpers -------------------------------------------------------------
  defp int_arrow, do: {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}

  # diverging: loop = λx. loop x   (bare unconditional self-call)
  defp loop_def(env),
    do:
      Env.add_def(
        env,
        :loop,
        int_arrow(),
        {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:app, {:global, :loop}, {:var, 0}}}
      )

  # total: total_id = λx. x   (no self-call -> terminating? fast path)
  defp total_def(env),
    do: Env.add_def(env, :total_id, int_arrow(), {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:var, 0}})

  # transitive: callee = λx. x ; loop = λx. callee x
  defp callee_def(env),
    do: Env.add_def(env, :callee, int_arrow(), {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:var, 0}})

  defp loop_calls_callee(env),
    do:
      Env.add_def(
        env,
        :loop,
        int_arrow(),
        {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:app, {:global, :callee}, {:var, 0}}}
      )

  defp with_family_index(env, fam, g),
    do: %{
      env
      | families:
          Map.put(env.families, fam, %{
            name: fam,
            params: [],
            indices: [{:i, {:app, {:global, g}, {:int_lit, 0}}}],
            level: 0
          })
    }

  defp with_ctor_index(env, ct, g),
    do: %{
      env
      | ctors:
          Map.put(env.ctors, ct, %{
            name: ct,
            args: [],
            result_indices: [{:app, {:global, g}, {:int_lit, 0}}],
            result_params: [],
            quantities: []
          })
    }

  # -- coverage manifest -------------------------------------------------------

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). Soundness names the three
  fixed catalog shapes (diverging in a family-index position, diverging in a ctor
  result-index position, and the all-total control); completeness names the direct
  vs transitive-callee type-position globals.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    [
      {"totality_closure/soundness", :diverging_family_index},
      {"totality_closure/soundness", :diverging_ctor_index},
      {"totality_closure/soundness", :all_total},
      {"totality_closure/completeness", :direct_type_global},
      {"totality_closure/completeness", :transitive_callee}
    ]
  end

  @doc """
  Uniform sampleable generator over both fixed catalogs (this vertical is otherwise
  seed-test–fed). Used by the coverage-manifest gate to confirm every declared cell
  is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(soundness_challenges() ++ completeness_challenges())
  end

  # -- catalogs ----------------------------------------------------------------

  @doc "V5a soundness catalog: diverging-in-type-position (reject) + all-total (accept)."
  @spec soundness_challenges() :: [Challenge.t()]
  def soundness_challenges do
    [
      {Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop), :reject, :diverging_family_index},
      {Env.empty() |> loop_def() |> with_ctor_index(:Wrap, :loop), :reject, :diverging_ctor_index},
      {Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id), :accept, :all_total}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{env, expect, cell}, i} ->
      Challenge.new(
        kind: :closure_env,
        assay: "totality_closure/soundness",
        label: :diverging,
        payload: %{env: env, expect: expect},
        seed: i,
        cover_tag: cell
      )
    end)
  end

  @doc "V5b completeness catalog: direct + transitive-callee type-position globals."
  @spec completeness_challenges() :: [Challenge.t()]
  def completeness_challenges do
    [
      {Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop), :direct_type_global},
      {Env.empty() |> callee_def() |> loop_calls_callee() |> with_family_index(:Vessel, :loop), :transitive_callee}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{env, cell}, i} ->
      Challenge.new(
        kind: :closure_env,
        assay: "totality_closure/completeness",
        label: :positive,
        payload: %{env: env},
        seed: i,
        cover_tag: cell
      )
    end)
  end
end
