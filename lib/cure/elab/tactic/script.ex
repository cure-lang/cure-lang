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
    * `focus`/`all_goals` only mean something once a command produces more than
      one goal. Today every Cure command is single-goal, so they would be
      vacuous vocabulary.

  So a script runs its steps in order with `seq`, and the first failure is the
  tactic's failure. That is the smallest composition that is useful and the
  only one whose semantics are already pinned by the Phase 2 tests.

  ## Evidence

  Each step is `Tactic.command/1`, which retains the checked solution keyed by
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
    Enum.reduce_while(steps, {:ok, %Tactic.Result{goals: [goal]}}, fn step, {:ok, result} ->
      case run_all(step, result) do
        # `Tactic.run_all/2` collapses to `{:ok, []}` when the goal list empties,
        # dropping the solutions it accumulated. A script must KEEP them: the
        # evidence is what closes the proof. Re-wrap the empty case so the
        # caller always sees a `Result` carrying the checked solutions.
        {:ok, []} -> {:halt, {:ok, %{result | goals: []}}}
        {:ok, next} -> {:cont, {:ok, next}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  @doc """
  Run a step over a whole result, threading remaining goals.

  A script is single-goal in practice, but the result shape is a list, and
  `Tactic.run_all/2` is what keeps a future multi-goal command honest.
  """
  @spec run_all(Step.step(), [Tactic.goal()] | Tactic.Result.t()) :: Tactic.result()
  def run_all(step, goals_or_result), do: Tactic.run_all(&run(step, &1), goals_or_result)
end
