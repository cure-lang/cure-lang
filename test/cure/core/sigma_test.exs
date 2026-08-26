defmodule Cure.Core.SigmaTest do
  @moduledoc """
  Kernel suite for the builtin inductive Sigma (D2). The primitive
  `{:sigma}`/`{:pair}`/`{:fst}`/`{:snd}` Core forms are retired; the dependent pair
  is now the seeded inductive family `Sigma(a, b)` with constructor `mk_pair` and
  projection-by-`:case`. Exercised over the file's own `Dec`/`Box` payloads.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Inductive, Env, Kernel, Context, Eval, Normalise}

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @box_d {:data, :Box, [], [{:var, 0}]}

  # The dependent Σ(d:Dec). Box(d), as the inductive `Sigma(Dec, λd. Box(d))`.
  @sigma {:data, :"Std.Sigma#Sigma", [@dec, {:lam, Cure.Core.Grade.unrestricted(), @dec, @box_d}], []}

  defp build_env do
    Builtins.seed(Env.empty())
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0), [
      Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])
    ])
  end

  test "Sigma formation: the family application is a type at level 0" do
    assert {:ok, {:vtype, 0}} == Kernel.infer(Context.empty(build_env()), @sigma)
  end

  test "mk_pair intro checks against its Sigma type" do
    e = build_env()
    ctx = Context.empty(e)
    sigma_val = Eval.eval(@sigma, Context.env(ctx))
    # (Causal, mk(Causal)) : Σ(d:Dec). Box(d)
    pair = {:ctor, :"Std.Sigma#mk_pair", [@causal, {:ctor, :mk, [@causal]}]}
    assert :ok == Kernel.check(ctx, pair, sigma_val)
  end

  test "ι-reduction: projection cases on a concrete mk_pair reduce to the components" do
    ctx = Context.empty(build_env())
    pair = {:ctor, :"Std.Sigma#mk_pair", [@causal, {:ctor, :mk, [@causal]}]}

    fst =
      {:case, pair, {:lam, Cure.Core.Grade.unrestricted(), @sigma, @dec}, [{:"Std.Sigma#mk_pair", 2, {:var, 1}}]}

    snd =
      {:case, pair, {:lam, Cure.Core.Grade.unrestricted(), @sigma, {:data, :Box, [], [@causal]}},
       [{:"Std.Sigma#mk_pair", 2, {:var, 0}}]}

    assert Normalise.nf(ctx, fst) == @causal
    assert Normalise.nf(ctx, snd) == {:ctor, :mk, [@causal]}
  end

  test "dependent second projection: snd's type is Box at the (stuck) first component" do
    e = build_env()
    # ctx: p : Σ(d:Dec). Box(d)
    ctx = Context.extend(Context.empty(e), Eval.eval(@sigma, []))

    # fst of a Σ-value, as a first-projection case. The scrutinee `{:var, 0}` is
    # read in the enclosing frame (the context `p`) when used standalone below, and
    # re-read as the motive-bound scrutinee when nested inside `snd_motive` — the
    # same de Bruijn index 0, resolved per frame.
    fst_case =
      {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @sigma, @dec}, [{:"Std.Sigma#mk_pair", 2, {:var, 1}}]}

    # snd p : Box(fst p) — the dependent motive returns Box applied to fst p.
    snd_motive = {:lam, Cure.Core.Grade.unrestricted(), @sigma, {:data, :Box, [], [fst_case]}}
    snd_p = {:case, {:var, 0}, snd_motive, [{:"Std.Sigma#mk_pair", 2, {:var, 0}}]}

    assert {:ok, {:vdata, :Box, [_stuck_fst]}} = Kernel.infer(ctx, snd_p)
    assert {:ok, {:vdata, :Dec, []}} == Kernel.infer(ctx, fst_case)
  end

  test "negative: a second component of the wrong type is rejected" do
    e = build_env()
    ctx = Context.empty(e)
    sigma_val = Eval.eval(@sigma, [])
    # (Causal, Dcoupled): Dcoupled : Dec, but Box(Causal) is expected.
    pair = {:ctor, :"Std.Sigma#mk_pair", [@causal, {:ctor, :Dcoupled, []}]}
    assert {:error, _} = Kernel.check(ctx, pair, sigma_val)
  end
end
