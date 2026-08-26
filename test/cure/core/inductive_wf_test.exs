defmodule Cure.Core.InductiveWfTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel}

  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:SVDesc, [], [], 0), [])
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
  end

  @svdesc {:data, :SVDesc, [], []}
  @dec {:data, :Dec, [], []}

  test "accepts a well-formed indexed family and constructor" do
    sf = Inductive.family(:SF, [], [{:as, @svdesc}, {:bs, @svdesc}, {:d, @dec}], 0)

    # seq with a direct (non-computed) result index d := d1; computed `and` is M3.4.
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
        [{:var, 6}, {:var, 4}, {:var, 3}]
      )

    env = Inductive.declare(base_env(), sf, [seq])
    fam = Inductive.get_family(env, :SF)
    assert :ok == Kernel.check_family(env, fam)
    assert :ok == Kernel.check_ctor(env, fam, Inductive.get_ctor(env, :seq))
  end

  test "a Type0 field forces family level >= 1 (the two-universe rule)" do
    c = Inductive.ctor(:C, [{:t, {:type, 0}}], [])

    env1 = Inductive.declare(base_env(), Inductive.family(:Sig, [], [], 1), [c])
    assert :ok == Kernel.check_ctor(env1, Inductive.get_family(env1, :Sig), Inductive.get_ctor(env1, :C))

    env0 = Inductive.declare(base_env(), Inductive.family(:Sig, [], [], 0), [c])

    assert {:error, :universe_level} ==
             Kernel.check_ctor(env0, Inductive.get_family(env0, :Sig), Inductive.get_ctor(env0, :C))
  end

  test "negative: result-index arity mismatch" do
    sf = Inductive.family(:SF, [], [{:as, @svdesc}, {:bs, @svdesc}, {:d, @dec}], 0)
    bad = Inductive.ctor(:prim, [{:as, @svdesc}], [{:var, 0}])
    env = Inductive.declare(base_env(), sf, [bad])

    assert {:error, :index_arity} ==
             Kernel.check_ctor(env, Inductive.get_family(env, :SF), Inductive.get_ctor(env, :prim))
  end

  test "negative: a result index of the wrong type" do
    g = Inductive.family(:G, [], [{:d, @dec}], 0)
    bad = Inductive.ctor(:mk, [{:s, @svdesc}], [{:var, 0}])
    env = Inductive.declare(base_env(), g, [bad])

    assert {:error, {:conversion_failure, _, _}} =
             Kernel.check_ctor(env, Inductive.get_family(env, :G), Inductive.get_ctor(env, :mk))
  end
end
