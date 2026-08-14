defmodule Cure.Elab.TotalityClosureTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env}
  alias Cure.Elab.TotalityClosure

  @dec {:data, :Dec, [], []}
  @dcoupled {:ctor, :Dcoupled, []}
  @causal {:ctor, :Causal, []}
  @svdesc {:data, :SVDesc, [], []}
  @dec_motive {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}

  defp and_type, do: {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}}

  defp and_body do
    inner = {:case, {:var, 0}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]}

    {:lam, Cure.Core.Grade.unrestricted(), @dec,
     {:lam, Cure.Core.Grade.unrestricted(), @dec,
      {:case, {:var, 1}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, inner}]}}}
  end

  # SF's seq has result index and(d1,d2); `and` is registered with body `and_b`.
  defp env_with(and_b) do
    and_term = {:app, {:app, {:global, :and}, {:var, 3}}, {:var, 2}}

    seq =
      Inductive.ctor(
        :seq,
        [
          {:as, @svdesc},
          {:bs, @svdesc},
          {:cs, @svdesc},
          {:d1, @dec},
          {:d2, @dec},
          {:l, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}},
          {:r, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}}
        ],
        [{:var, 6}, {:var, 4}, and_term]
      )

    sf = Inductive.family(:SF, [], [{:as, @svdesc}, {:bs, @svdesc}, {:d, @dec}], 0)

    Env.empty()
    |> Inductive.declare(Inductive.family(:SVDesc, [], [], 0), [])
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(sf, [seq])
    |> Env.add_def(:and, and_type(), and_b)
  end

  test "and is reached as a type-level function via seq's index expression" do
    assert MapSet.member?(TotalityClosure.type_level_fns(env_with(and_body())), :and)
  end

  test "certifying type-level functions succeeds for a total and" do
    assert {:ok, env2} = TotalityClosure.certify_type_level(env_with(and_body()))
    assert Env.certified?(env2, :and)
    assert map_size(env2.totality_components) == 1
    assert is_binary(env2.totality_component_of.and)
  end

  test "a non-total function used in a type raises :totality_required naming it" do
    # and = and (non-terminating) but used in seq's index
    assert {:error, {:totality_required, :and}} =
             TotalityClosure.certify_type_level(env_with({:global, :and}))
  end

  test "a partial runtime-only def is not required to be total" do
    env = env_with(and_body()) |> Env.add_def(:rt, @dec, {:global, :rt})
    refute MapSet.member?(TotalityClosure.type_level_fns(env), :rt)
    assert {:ok, _env2} = TotalityClosure.certify_type_level(env)
  end

  test "a missing type-level callee reports its exact canonical closure path" do
    assert {:error, {:totality_closure_unresolved, %{definition: :missing, closure_path: [:and, :missing], root: :and}}} =
             TotalityClosure.certify_type_level_detailed(env_with({:global, :missing}))
  end

  test "a missing compile-time root is not silently filtered from certification" do
    assert {:error, {:totality_closure_unresolved, %{definition: :missing, closure_path: [:missing], root: :missing}}} =
             TotalityClosure.certify_roots(Env.empty(), [:missing])
  end
end
