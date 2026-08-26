defmodule Cure.Core.PositivityTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env}

  defp env_with_dec_sf do
    svdesc = {:data, :SVDesc, [], []}
    dec = {:data, :Dec, [], []}

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
        [{:var, 6}, {:var, 4}, {:var, 3}]
      )

    Env.empty()
    |> Inductive.declare(Inductive.family(:SVDesc, [], [], 0), [])
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(sf, [seq])
  end

  test "Dec and SF are strictly positive" do
    env = env_with_dec_sf()
    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :Dec))
    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :SF))
  end

  test "a constructor with the family in a negative position is rejected" do
    bad = Inductive.family(:Bad, [], [], 0)
    # mk : (Bad -> Dec) -> Bad — Bad occurs to the left of an arrow (negative)
    mk =
      Inductive.ctor(
        :mk,
        [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:data, :Bad, [], []}, {:data, :Dec, [], []}}}],
        []
      )

    env = Inductive.declare(env_with_dec_sf(), bad, [mk])

    assert {:error, {:non_strictly_positive, :mk}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end
end
