defmodule Antigen.Assays.TotalityClosureAssayTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.TotalityClosureAssay, Challenge}
  alias Antigen.Generators.ClosureEnv
  alias Cure.Core.Env

  defp int_arrow, do: {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}

  defp loop_def(env),
    do:
      Env.add_def(
        env,
        :loop,
        int_arrow(),
        {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:app, {:global, :loop}, {:var, 0}}}
      )

  defp total_def(env),
    do: Env.add_def(env, :total_id, int_arrow(), {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:var, 0}})

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

  defp snd_ch(env, expect) do
    Challenge.new(
      kind: :closure_env,
      assay: "totality_closure/soundness",
      label: :diverging,
      payload: %{env: env, expect: expect},
      seed: 1
    )
  end

  test "reject baseline: diverging :loop in a family index — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "reject baseline: diverging :loop in a ctor result_indices — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_ctor_index(:Wrap, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "accept control: an all-total type-level env certifies (rejection is divergence-specific)" do
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    assert TotalityClosureAssay.run(snd_ch(env, :accept)) == :ok
  end

  test "negative control: an unconditional-{:ok} certify stub certifies the diverger" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    k = %{TotalityClosureAssay.__real__() | certify: fn e -> {:ok, e} end}
    assert {:violation, {:diverging_certified, _}} = TotalityClosureAssay.run(snd_ch(env, :reject), k)
  end

  test "negative control: a certify stub that errors on the all-total env is caught (:accept branch)" do
    # Every violation branch needs a negative control (V2 plan-review lesson).
    # :total_env_not_certified's `other` case is reachable under REAL ops — it is
    # exactly what a malformed accept-control env (spec §8-2(a)) or a driver
    # false-rejection would produce — unlike :unexpected_certify_result (see the
    # note after Step 3), so it gets its own dedicated stub here rather than being
    # exercised only implicitly by the accept-control test passing.
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    k = %{TotalityClosureAssay.__real__() | certify: fn _e -> {:error, {:totality_required, :total_id}} end}

    assert TotalityClosureAssay.run(snd_ch(env, :accept), k) ==
             {:violation, {:total_env_not_certified, {:error, {:totality_required, :total_id}}}}
  end

  describe "totality_closure/completeness (V5b)" do
    defp cmp_ch(env) do
      Challenge.new(
        kind: :closure_env,
        assay: "totality_closure/completeness",
        label: :positive,
        payload: %{env: env},
        seed: 1
      )
    end

    # direct: :loop in a family index. transitive: :loop's body calls :callee, both must be reached.
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

    test "baseline: direct type-position global is in type_level_fns" do
      env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
      assert TotalityClosureAssay.run(cmp_ch(env)) == :ok
    end

    test "baseline: transitive-callee global is in type_level_fns" do
      env = Env.empty() |> callee_def() |> loop_calls_callee() |> with_family_index(:Vessel, :loop)
      assert TotalityClosureAssay.run(cmp_ch(env)) == :ok
    end

    test "negative control: an empty type_level_fns stub misses everything" do
      env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
      k = %{TotalityClosureAssay.__real__() | type_level_fns: fn _e -> MapSet.new() end}
      assert {:violation, {:closure_missed, _}} = TotalityClosureAssay.run(cmp_ch(env), k)
    end

    test "negative control: a type_level_fns stub dropping the transitive callee" do
      env = Env.empty() |> callee_def() |> loop_calls_callee() |> with_family_index(:Vessel, :loop)
      # drops :callee
      k = %{TotalityClosureAssay.__real__() | type_level_fns: fn _e -> MapSet.new([:loop]) end}
      assert {:violation, {:closure_missed, missing}} = TotalityClosureAssay.run(cmp_ch(env), k)
      assert :callee in missing
    end

    test "independent walk recurses into builtin-op spine args (K2: the app chain)" do
      # a global nested in a builtin-op spine's args must be found by the
      # independent walk; this exercises reconciliation #2 in isolation, without
      # the real closure. (Re-spelled from the retired {:prim, :eq, …} row —
      # int_eq is a terminal call-graph node, :buried the payload.)
      env = %{
        Env.empty()
        | families: %{
            P: %{
              name: :P,
              params: [],
              indices: [{:i, {:app, {:app, {:global, :int_eq}, {:global, :buried}}, {:int_lit, 0}}}],
              level: 0
            }
          }
      }

      assert :buried in TotalityClosureAssay.__reachable__(env)
    end
  end

  describe "generator + runner wiring" do
    alias Antigen.Runner

    test "each catalog is non-empty and correctly tagged" do
      assert ClosureEnv.soundness_challenges() != []
      assert ClosureEnv.completeness_challenges() != []
      assert Enum.all?(ClosureEnv.soundness_challenges(), &(&1.assay == "totality_closure/soundness"))
      assert Enum.all?(ClosureEnv.completeness_challenges(), &(&1.assay == "totality_closure/completeness"))
    end

    test "runner dispatches both totality_closure/ ids and the whole clean catalog is :ok" do
      all = ClosureEnv.soundness_challenges() ++ ClosureEnv.completeness_challenges()
      assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
    end
  end
end
