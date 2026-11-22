defmodule Cure.Elab.TacticIntegrationTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, ProofGoal, Tactic}
  alias Cure.Elab.Tactic.Result

  defp goal do
    assert {:ok, env} =
             Program.elaborate("""
             mod TacticIntegration
               type Nat = Z | S(Nat)
               type Pair = Pair(Nat, Nat)
               fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) =
                 proof chain
                   Pair(x, x) == Pair(y, y)
                   because
                     rewrite using h all
                     simplify
             end
             """)

    %{type: type} = Env.get_def(env, :theorem)
    {context, target} = open_telescope(type, Context.empty(env))
    ProofGoal.new(target, ["h", "y", "x"], context, env)
  end

  defp open_telescope({:pi, grade, domain, body}, context) do
    open_telescope(body, Context.extend(context, Eval.eval(domain, Context.env(context)), grade))
  end

  defp open_telescope(target, context), do: {context, target}

  defp rewrite_all do
    Tactic.command({:rewrite_command, [direction: :forward, target: :all], [{:variable, [], "h"}]})
  end

  defp simplify, do: Tactic.command({:simplify_command, [], []})

  defp check_solution(result, goal) do
    assert %{evidence: evidence, trace: [_ | _]} = Map.fetch!(result.solutions, goal.id)
    assert :ok = Kernel.check(goal.context, evidence, Eval.eval(goal.expected, Context.env(goal.context)))
  end

  test "command sequencing retains evidence for the original, not rewritten, goal" do
    goal = goal()
    assert {:ok, %Result{goals: []} = result} = Tactic.seq(rewrite_all(), simplify()).(goal)
    assert Tactic.closed?({:ok, result})
    assert [] = Tactic.open_goals({:ok, result})
    check_solution(result, goal)
  end

  test "goal inspection exposes target and checked local hypothesis types" do
    goal = goal()
    assert %{target: target, hypotheses: [%{name: "h"}, %{name: "y"}, %{name: "x"}]} = ProofGoal.inspect_goal(goal)
    assert target == goal.expected
  end

  test "focus and all_goals retain independent solutions without losing siblings" do
    first = goal()
    second = %{first | id: make_ref()}
    tactic = Tactic.seq(rewrite_all(), simplify())
    assert {:ok, %Result{goals: [^first]} = partial} = Tactic.focus(tactic, 1).([first, second])
    check_solution(partial, second)
    assert {:ok, %Result{goals: []} = finished} = Tactic.all_goals(tactic).(partial)
    check_solution(finished, first)
    check_solution(finished, second)
    assert {:error, {:no_such_goal, 2}} = Tactic.focus(tactic, 2).([first])
  end

  test "repetition stops on failure without discarding earlier progress" do
    tactic = fn
      %{id: 0} = goal -> {:ok, [%{goal | id: 1}]}
      _ -> {:error, :done}
    end

    assert {:ok, [%{id: 1}]} = Tactic.repeat_until_fail(tactic).(%{id: 0})
    assert {:ok, [%{id: 0}]} = Tactic.repeat_until_fail(tactic, 0).(%{id: 0})
  end

  test "repetition stops a failing branch while another closes" do
    split = fn _ -> {:ok, [%{id: :stop}, %{id: :close}]} end

    close = fn
      %{id: :stop} -> {:error, :done}
      %{id: :close} -> {:ok, []}
    end

    assert {:ok, [%{id: :stop}]} = Tactic.seq(split, Tactic.repeat_until_fail(close)).(%{id: :start})
  end

  test "rewrite-all visits original paths only when the replacement contains its target" do
    target = {:var, 0}
    replacement = {:ctor, :successor, [target]}
    original = {:ctor, :pair, [target, target]}

    assert {:ok, _build, {:ctor, :pair, [^replacement, ^replacement]}, [_, _]} =
             Cure.Elab.Rewrite.directed_plan(
               {:var, 1},
               {:data, :nat, [], []},
               target,
               replacement,
               original,
               :forward,
               :all
             )
  end

  test "backwards rewrite-all reconstructs checked evidence in the original goal" do
    goal = goal()
    {:data, equality, carrier, [left, right]} = goal.expected
    expected = {:data, equality, carrier, [right, left]}
    goal = %{goal | expected: expected, root_expected: expected}
    rewrite = Tactic.command({:rewrite_command, [direction: :backwards, target: :all], [{:variable, [], "h"}]})
    assert {:ok, %Result{goals: []} = result} = Tactic.seq(rewrite, simplify()).(goal)
    check_solution(result, goal)
  end

  test "certified recursive unfolding closes while removing its certificate leaves a residual goal" do
    assert {:ok, env} =
             Program.elaborate("""
             mod CertifiedSimplification
               type Nat = Z | S(Nat)
               fn plus(left: Nat, right: Nat) -> Nat = match left
                 Z() -> right
                 S(previous) -> S(plus(previous, right))
             end
             """)

    nat = {:data, :"CertifiedSimplification#Nat", [], []}
    plus = :"CertifiedSimplification#plus"
    zero = {:ctor, :"CertifiedSimplification#Z", []}
    call = {:app, {:app, {:global, plus}, zero}, {:var, 0}}
    expected = Cure.Elab.Rewrite.mk_eq(nat, call, {:var, 0})
    assert Env.certified?(env, plus)
    context = Context.extend(Context.empty(env), Eval.eval(nat, []))
    assert {:ok, _evidence, [_]} = Cure.Elab.Simplifier.solve(expected, context, nil)

    uncertified = %{env | certified: MapSet.delete(env.certified, plus)}
    context = Context.extend(Context.empty(uncertified), Eval.eval(nat, []))

    assert {:error, {:simplification_failed, %{kind: :residual_goal}}} =
             Cure.Elab.Simplifier.solve(expected, context, nil)
  end

  test "have facts and rewritten hypotheses keep a shared checked scope" do
    for statements <- [
          """
          have other: Equivalent(Int, x, x) = reflexive(x)
          rewrite using h in hyp
          hyp
          """,
          """
          have saved: Equivalent(Int, x, z) = hyp
          rewrite using h in saved
          have result: Equivalent(Int, y, z) = saved
          result
          """,
          """
          rewrite using h in hyp
          have other: Equivalent(Int, y, z) = hyp
          exact other
          """
        ] do
      body = statements |> String.trim() |> String.replace("\n", "\n      ")

      source = """
      mod MixedProofScope
        fn checked(x: Int, y: Int, z: Int, h: Equivalent(Int, x, y), hyp: Equivalent(Int, x, z)) -> Equivalent(Int, y, z) = proof chain
          y == z
          because
            #{body}
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def(env, :"MixedProofScope#checked")
    end
  end

  test "facts materialized after a goal transport are reconstructed inside that transport" do
    assert {:ok, env} =
             Program.elaborate("""
             mod MaterializedTransportOrder
               fn checked(x: Int, y: Int, z: Int, h: Equivalent(Int, x, y), hyp: Equivalent(Int, x, z), q: Equivalent(Int, x, z)) -> Equivalent(Int, y, z) = proof chain
                 y == z
                 because
                   have other: Equivalent(Int, x, x) = reflexive(x)
                   rewrite backwards using h
                   rewrite using h in hyp
                   q
             end
             """)

    assert :ok = Kernel.check_def(env, :"MaterializedTransportOrder#checked")
  end
end
