defmodule Cure.Core.NormaliseTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Kernel, Normalise}

  @dec {:data, :Dec, [], []}
  @dcoupled {:ctor, :Dcoupled, []}
  @causal {:ctor, :Causal, []}
  @dec_motive {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
  end

  defp id_type, do: {:pi, Cure.Core.Grade.unrestricted(), {:type, 1}, {:type, 1}}
  defp id_body, do: {:lam, Cure.Core.Grade.unrestricted(), {:type, 1}, {:var, 0}}

  test "beta normalizes applications" do
    term = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 1}, {:var, 0}}, {:type, 0}}
    assert {:type, 0} == Normalise.nf(Context.empty(), term)
  end

  test "constructor case reduces by iota" do
    branches = [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]
    term = {:case, @causal, @dec_motive, branches}

    assert @causal == Normalise.nf(Context.empty(base()), term)
  end

  test "certified globals unfold" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    term = {:app, {:global, :id}, {:type, 0}}
    assert {:type, 0} == Normalise.nf(Context.empty(env), term)
  end

  test "certified identity globals terminate on open arguments" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    ctx = Context.extend(Context.empty(env), {:vdata, :Dec, []})
    term = {:app, {:global, :id}, {:var, 0}}

    # The identity unfolds to the existing neutral variable.  Normalization
    # must return that value once, rather than treating the unchanged neutral
    # as fresh progress and re-entering the delta loop forever.
    assert {:var, 0} == Normalise.nf(ctx, term)
  end

  test "speculative over-application of a certified global stays folded" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    # Elaboration and conversion normalize open candidates before the kernel has
    # accepted them. This deliberately ill-typed candidate must be treated as a
    # stuck neutral, not executed far enough to apply the constructor result.
    term = {:app, {:app, {:global, :id}, @causal}, @dcoupled}

    assert term == Normalise.whnf(Context.empty(env), term)
    assert term == Normalise.nf(Context.empty(env), term)
  end

  test "uncertified globals stay opaque" do
    env = Env.add_def(base(), :id, id_type(), id_body())
    term = {:app, {:global, :id}, {:type, 0}}

    assert {:app, {:global, :id}, {:type, 0}} == Normalise.whnf(Context.empty(env), term)
  end

  test "delta can be disabled for certified globals" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    assert {:global, :id} == Normalise.whnf(Context.empty(env), {:global, :id}, delta: :none)
  end

  test "stuck cases are preserved through value read-back" do
    ctx = Context.extend(Context.empty(base()), {:vdata, :Dec, []})
    branches = [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]
    term = {:case, {:var, 0}, @dec_motive, branches}

    assert {:case, {:var, 0}, _motive, ^branches} = Normalise.nf(ctx, term)
  end

  test "cyclic certified delta stays folded when unfolding makes no progress" do
    env =
      base()
      |> Env.add_def(:f, @dec, {:global, :f})
      |> Env.certify(:f)

    assert {:global, :f} == Normalise.whnf(Context.empty(env), {:global, :f}, fuel: 5)
  end

  defp step_env do
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:case, {:var, 0}, @dec_motive,
        [
          {:Dcoupled, 0, @dcoupled},
          {:Causal, 0, {:app, {:global, :step}, {:var, 0}}}
        ]}}

    base()
    |> Env.add_def(:step, {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}, body)
    |> Env.certify(:step)
  end

  test "recursive certified definitions under neutral scrutinees stay FOLDED (lazy unfolding)" do
    # Reference-faithful (Idris/Lean/Agda): unfolding a pattern-matching
    # definition whose scrutinee is a neutral only exposes a matcher that is
    # itself stuck — so the definition is kept FOLDED (opaque application),
    # NOT eagerly expanded into its internal `case`. This keeps normal forms
    # canonical (a stuck recursive call has ONE shape everywhere) and keeps
    # conversion terminating on open terms.
    ctx = Context.extend(Context.empty(step_env()), {:vdata, :Dec, []})
    term = {:app, {:global, :step}, {:var, 0}}

    assert {:app, {:global, :step}, {:var, 0}} == Normalise.whnf(ctx, term, fuel: 5)
    assert {:app, {:global, :step}, {:var, 0}} == Normalise.nf(ctx, term, fuel: 5)
  end

  test "conversion relates a folded reducible call to its exposed stuck case" do
    env = step_env()
    value_env = [{:vneutral, {:nvar, 0}}]
    folded = {:app, {:global, :step}, {:var, 0}}

    exposed =
      {:case, {:var, 0}, @dec_motive,
       [
         {:Dcoupled, 0, @dcoupled},
         {:Causal, 0, {:app, {:global, :step}, {:var, 0}}}
       ]}

    assert Conv.conv?(folded, exposed, value_env, 1, env)
    assert Conv.conv?(exposed, folded, value_env, 1, env)
  end

  test "certified recursive globals still ι-reduce under constructor scrutinees" do
    # Guard against over-freezing: lazy unfolding must still fire when the
    # scrutinee IS a constructor. step(Dcoupled) selects the Dcoupled branch.
    ctx = Context.empty(step_env())
    term = {:app, {:global, :step}, @dcoupled}

    assert @dcoupled == Normalise.nf(ctx, term, fuel: 5)
    assert @dcoupled == Normalise.whnf(ctx, term, fuel: 5)
  end

  test "Kernel.normalize delegates to the shared normalizer" do
    term = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 1}, {:var, 0}}, {:type, 0}}
    assert Normalise.nf(Context.empty(), term) == Kernel.normalize(Context.empty(), term)
  end

  test "nf is idempotent on a lambda over a free context variable (index-reflection regression)" do
    # A plain depth-3 context; nf of this pure lambda depends only on the value
    # env + depth (not the types). Before the fix, nf_struct stored the reified
    # body in a closure with an EMPTY env, so the outer reify re-evaluated it in a
    # truncated env and REFLECTED the free var's de Bruijn index ({:var,1} ->
    # {:var,3}), oscillating with period 2. A well-typed normal form must be a
    # fixpoint of nf.
    ctx =
      Enum.reduce(1..3, Context.empty(base()), fn _, c ->
        Context.extend(c, {:vtype, 0})
      end)

    t = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 1}}
    nf1 = Normalise.nf(ctx, t)
    assert nf1 == t, "nf reflected the free var: #{inspect(nf1)}"
    assert Normalise.nf(ctx, nf1) == nf1, "nf is not idempotent (oscillation)"
  end
end
