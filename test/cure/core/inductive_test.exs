defmodule Cure.Core.InductiveTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env}

  test "stores a nullary family Dec with its constructors" do
    dec = Inductive.family(:Dec, [], [], 0)

    env =
      Env.empty()
      |> Inductive.declare(dec, [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])

    assert Inductive.family?(env, :Dec)
    assert Inductive.ctor_family(env, :Causal) == :Dec
    assert Inductive.ctor_result_indices(env, :Causal) == []
    assert Inductive.index_telescope(env, :Dec) == []
  end

  test "stores indexed family SF; seq carries the computed result index and(d1,d2)" do
    svdesc = {:data, :SVDesc, [], []}
    dec = {:data, :Dec, [], []}
    # In seq's body scope (telescope [as,bs,cs,d1,d2,l,r]): as=#6, cs=#4, d1=#3, d2=#2.
    and_term = {:app, {:app, {:global, :and}, {:var, 3}}, {:var, 2}}

    sf = Inductive.family(:SF, [], [{:as, svdesc}, {:bs, svdesc}, {:d, dec}], 0)

    seq =
      Inductive.ctor(
        :seq,
        [
          {:as, svdesc},
          {:bs, svdesc},
          {:cs, svdesc},
          {:d1, dec},
          {:d2, dec},
          {:l, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}},
          {:r, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}}
        ],
        [{:var, 6}, {:var, 4}, and_term]
      )

    env = Env.empty() |> Inductive.declare(sf, [seq])

    assert Inductive.family?(env, :SF)
    assert Inductive.ctor_family(env, :seq) == :SF
    assert Inductive.ctor_result_indices(env, :seq) == [{:var, 6}, {:var, 4}, and_term]
    assert Inductive.index_telescope(env, :SF) == [{:as, svdesc}, {:bs, svdesc}, {:d, dec}]
    assert length(Inductive.arg_telescope(env, :seq)) == 7
  end
end
