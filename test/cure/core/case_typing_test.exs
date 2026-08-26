defmodule Cure.Core.CaseTypingTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context, Eval}

  @dec {:data, :Dec, [], []}

  defp build_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    # Box(d : Dec) with mk : (x : Dec) -> Box(x) — index computed from the field.
    |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0), [
      Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])
    ])
  end

  defp ctx_with(type_value), do: Context.extend(Context.empty(build_env()), type_value)

  test "checks and infers a dependent case on Dec" do
    ctx = ctx_with(Eval.eval(@dec, []))
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}
    branches = [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]
    cas = {:case, {:var, 0}, motive, branches}

    assert :ok == Kernel.check(ctx, cas, {:vdata, :Dec, []})
    assert {:ok, {:vdata, :Dec, []}} = Kernel.infer(ctx, cas)
  end

  test "checks a case with per-branch index refinement (Box)" do
    ctx = ctx_with(Eval.eval({:data, :Box, [], [{:ctor, :Causal, []}]}, []))
    # motive = λ(d:Dec). λ(bx : Box d). Dec
    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], [{:var, 0}]}, @dec}}

    # mk branch: the body is the stored value x, whose type Dec matches the motive
    # after the index d is refined to x.
    branches = [{:mk, 1, {:var, 0}}]
    cas = {:case, {:var, 0}, motive, branches}

    assert {:ok, {:vdata, :Dec, []}} = Kernel.infer(ctx, cas)
  end

  test "negative: a branch body of the wrong type" do
    ctx = ctx_with(Eval.eval(@dec, []))
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]
    cas = {:case, {:var, 0}, motive, branches}

    assert {:error, :branch_type} = Kernel.infer(ctx, cas)
  end

  test "negative: a non-exhaustive case" do
    ctx = ctx_with(Eval.eval(@dec, []))
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}
    branches = [{:Dcoupled, 0, {:ctor, :Causal, []}}]
    cas = {:case, {:var, 0}, motive, branches}

    assert {:error, :coverage} = Kernel.infer(ctx, cas)
  end

  test "successful nested cases are not re-inferred for branch diagnostics" do
    ctx = ctx_with(Eval.eval(@dec, []))
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}

    nested = fn
      _nested, 0 ->
        {:ctor, :Dcoupled, []}

      nested, depth ->
        {:case, {:var, 0}, motive,
         [
           {:Dcoupled, 0, nested.(nested, depth - 1)},
           {:Causal, 0, {:ctor, :Dcoupled, []}}
         ]}
    end

    {before_reductions, _} = :erlang.statistics(:reductions)

    assert :ok ==
             Kernel.check_with_branch_details(
               ctx,
               nested.(nested, 16),
               {:vdata, :Dec, []}
             )

    {after_reductions, _} = :erlang.statistics(:reductions)

    # Recording a successful branch's already-proven expected type is linear in
    # the nesting depth. Re-inferring every successful body here makes this
    # linear-size term exponential (and made Std.Regex.Syntax.Parser take
    # minutes and tens of billions of reductions).
    assert after_reductions - before_reductions < 250_000
  end
end
