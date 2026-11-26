defmodule Cure.Elab.Tactic.Script do
  @moduledoc """
  Run a classified tactic script against a goal.

  This is the bridge Phase 3 needs: a `tactic` macro rule expands to surface
  syntax, `Cure.Elab.Tactic.Step` classifies that syntax against a closed
  vocabulary, and this module turns the classified steps into `Tactic`
  combinators.

  ## Why composition is `seq` and nothing else

  `Cure.Elab.Tactic` offers `or_else`, `repeat`, `try_`, `focus` and
  `all_goals`. None of them is exposed to a user tactic, deliberately:

    * `or_else` and `try_` swallow a failure. A tactic that silently does
      nothing looks identical to one that worked, and the proof then fails
      later with a diagnostic pointing at the wrong line.
    * `repeat` is a fixpoint loop. Exposing it to authored source would make
      "how many steps did this proof take" depend on the simplifier's internal
      progress heuristic.
    * `focus`/`all_goals` are explicit host controls rather than implicit
      broadcasts over the premises of an authored proof.

  A script sequences checked commands using `Tactic.run_focused/2`. A failed step
  fails the script. Unlike goal-list sequencing, a source statement after
  closure is an unreachable-statement error, just as in a justification block.
  Open goals are returned for the caller's next command to finish.

  ## Evidence

  Each primitive step is `Tactic.command/1`, which retains the checked solution keyed by
  the ORIGINAL goal identity and re-checks it against the original goal. A
  script therefore inherits Phase 2's guarantee without adding a rule: the
  tactic cannot produce evidence the kernel has not verified.
  """

  alias Cure.Elab.Tactic
  alias Cure.Elab.Tactic.Step

  @doc """
  Run a classified step against a goal.

  Returns the `Tactic` result shape: `{:ok, %Result{}}` with remaining goals and
  checked solutions, or `{:error, reason}`.
  """
  @spec run(Step.step(), Tactic.goal()) :: Tactic.result()
  def run({:command, node}, goal), do: Tactic.command(node).(goal)

  def run({:sequence, steps}, goal) do
    Cure.Elab.ProofState.with_session(fn ->
      run_steps(steps, %Tactic.Result{goals: [goal]}, goal)
    end)
  end

  defp run_steps(_steps, %Tactic.Result{goals: [], pending: pending}, goal)
       when map_size(pending) > 0,
       do: Cure.Elab.ProofGoal.pending_application(goal)

  defp run_steps([], result, _goal), do: {:ok, result}

  defp run_steps([step | _rest], %Tactic.Result{goals: [], solutions: solutions}, goal) do
    trace = solutions |> Map.fetch!(goal.id) |> Map.fetch!(:trace)
    Cure.Elab.ProofGoal.unreachable_statement(first_command(step), goal.source, trace)
  end

  defp run_steps([step | rest], result, goal) do
    statement = first_command(step)
    Cure.Elab.ProofState.observe_session(:before, statement, goal, result.goals)

    executed =
      Cure.Elab.ProofState.within_statement(statement, fn ->
        Tactic.run_focused(&run(step, &1), result)
      end)

    case executed do
      {:ok, next} ->
        Cure.Elab.ProofState.observe_session(:after, statement, goal, next.goals)
        run_steps(rest, next, goal)

      {:error, _} = error ->
        Cure.Elab.ProofState.observe_session(:failed, statement, goal, result.goals)
        error
    end
  end

  defp first_command({:command, node}), do: node
  defp first_command({:sequence, [step | _]}), do: first_command(step)

  @doc """
  Run a step over a whole result, threading remaining goals.

  This is an explicit host broadcast. Authored source sequences instead use
  `Tactic.run_focused/2`, preserving siblings and settling pending parents.
  """
  @spec run_all(Step.step(), [Tactic.goal()] | Tactic.Result.t()) :: Tactic.result()
  def run_all(step, goals_or_result), do: Tactic.run_all(&run(step, &1), goals_or_result)
end
