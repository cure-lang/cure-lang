defmodule Cure.Elab.Tactic do
  @moduledoc """
  The tactic monad: a uniform result shape for proof commands, and the
  combinators that compose them.

  This is the goal API described in `docs/PATH_TO_LEAN4.md` Phase 2.
  It adds **no** Core constructors and
  **no** kernel rules: every tactic returns ordinary evidence that the kernel
  re-checks, exactly as a hand-written proof term would.

  ## The result shape

  A tactic transforms a goal and reports what remains:

  Proof commands return `{:ok, %Cure.Elab.Tactic.Result{}}`, containing the
  remaining goals and checked closure evidence keyed by original goal identity.
  An empty `goals` list means closed. Goal-list-only results remain supported
  for scheduling and legacy callers, but cannot reconstruct proofs.

  A list rather than a single goal is deliberate. Today every Cure command is
  single-goal, so the list is always zero or one element; but a `case`/`split`
  tactic produces several subgoals, and the shape must not need changing when
  that lands.

  ## Why this module exists

  Before it, each proof command lived as a private clause of
  `Cure.Elab.ProofGoal.command/2` with its own private result convention. That
  made the vocabulary closed: a library could not add a command, and the
  combinators (`seq`, `or_else`, `repeat`) had nowhere to live.

  Extracting the shape here is a **pure refactor**: `ProofGoal` keeps its
  behaviour and its diagnostics byte-for-byte, and simply routes through this
  module. The acceptance gate for Phase 2 is exactly that — every existing
  `E109`–`E115` test passes unchanged.

  ## Scope

  This module defines the MONAD and its combinators. It does not yet expose a
  public registration point for user tactics; that is Phase 4 (`tactic` macro
  rules), which expands to these combinators rather than to Core terms.
  """

  alias Cure.Elab.ProofGoal
  alias Cure.Elab.Tactic.Result

  @typedoc """
  A goal is `Cure.Elab.ProofGoal`'s checked state: an expected type, the local
  names in scope, the kernel context, and the accumulated proof trace.
  """
  @type goal :: ProofGoal.t()

  @typedoc "A tactic failure carries the structured diagnostic to report."
  @type error :: term()

  @typedoc """
  The result of running a tactic.

    * `{:ok, []}` — the goal is closed.
    * `{:ok, [goal]}` — the goal remains open (possibly transformed).
    * `{:error, reason}` — the tactic failed.
  """
  @type result :: {:ok, [goal()] | Result.t()} | {:error, error()}

  @typedoc "A tactic: a function from a goal to the remaining goals."
  @type t :: (goal() -> result())

  @doc """
  Legacy goal-list projection for inspection only.

  Use `command/1` for proof-producing execution: it retains evidence and checks
  it against the original goal. Discarding evidence is not a trust firewall.
  """
  @spec of_command_result(ProofGoal.command_result(), goal()) :: result()
  def of_command_result({:closed, _evidence, _trace}, _goal), do: {:ok, []}
  def of_command_result({:open, next_goal}, _goal), do: {:ok, [next_goal]}
  def of_command_result({:error, reason}, _goal), do: {:error, reason}

  @doc "Lift an existing proof command into a checked, evidence-preserving tactic."
  @spec command(term()) :: t()
  def command(statement) do
    fn goal ->
      case ProofGoal.command(statement, goal) do
        {:open, next} ->
          {:ok, %Result{goals: [next]}}

        {:closed, evidence, trace} ->
          context = goal.root_context || goal.context
          expected = goal.root_expected || goal.expected

          case Cure.Core.Kernel.check(context, evidence, Cure.Core.Eval.eval(expected, Cure.Core.Context.env(context))) do
            :ok -> {:ok, %Result{solutions: %{goal.id => %{evidence: evidence, trace: trace}}}}
            {:error, _} = error -> error
          end

        {:error, _} = error ->
          error
      end
    end
  end

  @doc """
  Run `t1`, then `t2` on each goal `t1` leaves open.

  Sequencing is the fundamental combinator: `simplify` then `rewrite` is
  `seq(simplify, rewrite)`. If `t1` closes the goal, `t2` never runs — which is
  what makes "commands after the goal is closed" an *unreachable* error rather
  than a silent no-op (`docs/PROOFS.md` §3.3).
  """
  @spec seq(t(), t()) :: t()
  def seq(t1, t2) do
    fn goal ->
      with {:ok, goals} <- t1.(goal) do
        run_all(t2, goals)
      end
    end
  end

  defp merge_result(left, right) when is_list(left) and is_list(right), do: left ++ right
  defp merge_result(left, %Result{} = right) when is_list(left), do: %{right | goals: left ++ right.goals}
  defp merge_result(%Result{} = left, right) when is_list(right), do: %{left | goals: left.goals ++ right}

  defp merge_result(%Result{} = left, %Result{} = right),
    do: %Result{goals: left.goals ++ right.goals, solutions: Map.merge(left.solutions, right.solutions)}

  @doc "Run a tactic on all remaining goals, retaining checked solutions."
  def all_goals(tactic), do: fn goals -> run_all(tactic, goals) end

  @doc "Run a tactic on one goal, leaving its siblings untouched."
  def focus(tactic, index \\ 0) when is_integer(index) and index >= 0 do
    fn
      %Result{} = result ->
        with {:ok, next} <- focus(tactic, index).(result.goals) do
          {:ok, merge_result(%{result | goals: []}, next)}
        end

      goals when is_list(goals) ->
        case Enum.split(goals, index) do
          {before, [goal | siblings]} ->
            with {:ok, remaining} <- tactic.(goal) do
              {:ok, merge_result(merge_result(before, remaining), siblings)}
            end

          _ ->
            {:error, {:no_such_goal, index}}
        end
    end
  end

  @doc "Repeat until failure, closure, no progress, or the step bound."
  def repeat_until_fail(tactic, max_steps \\ 100), do: repeat(tactic, max_steps)

  @doc """
  Run `t1`; if it fails, run `t2` on the ORIGINAL goal.

  Backtracking. `t2` never sees a partially-applied `t1`, because a failed
  tactic must not leave the goal half-transformed — that would make failure
  order-dependent and the proof state unsound to inspect.
  """
  @spec or_else(t(), t()) :: t()
  def or_else(t1, t2) do
    fn goal ->
      case t1.(goal) do
        {:ok, _} = ok -> ok
        {:error, _} -> t2.(goal)
      end
    end
  end

  @doc """
  Apply `tactic` to every goal in the list, threading results.

  Fails on the first error, preserving that error rather than masking it with a
  later one.
  """
  @spec run_all(t(), [goal()] | Result.t()) :: result()
  def run_all(_tactic, []), do: {:ok, []}

  def run_all(tactic, %Result{} = result) do
    with {:ok, next} <- run_all(tactic, result.goals) do
      {:ok, merge_result(%{result | goals: []}, next)}
    end
  end

  def run_all(tactic, goals) do
    Enum.reduce_while(goals, {:ok, []}, fn goal, {:ok, acc} ->
      case tactic.(goal) do
        {:ok, remaining} -> {:cont, {:ok, merge_result(acc, remaining)}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  @doc """
  Run `tactic` repeatedly until it fails or closes every goal.

  Bounded by `max_steps` so a tactic that makes no progress cannot loop. The
  bound is a structural guard, not a fuel model: exhausting it returns the goals
  still open rather than an error, because "stopped making progress" is a
  legitimate outcome for `repeat` in every reference implementation.
  """
  @spec repeat(t(), non_neg_integer()) :: t()
  def repeat(tactic, max_steps \\ 100) when is_integer(max_steps) and max_steps >= 0 do
    fn goal -> repeat_loop(tactic, [goal], max_steps) end
  end

  defp repeat_loop(_tactic, goals, 0), do: {:ok, goals}

  defp repeat_loop(tactic, goals, steps) do
    case run_all(try_(tactic), goals) do
      {:ok, []} -> {:ok, []}
      {:ok, %Result{goals: []} = closed} -> {:ok, closed}
      {:ok, ^goals} -> {:ok, goals}
      {:ok, next} -> repeat_loop(tactic, next, steps - 1)
      {:error, _} -> {:ok, goals}
    end
  end

  @doc """
  Run `tactic`, converting a failure into "no change".

  The tactic equivalent of Lean's `try`. Useful inside a `seq` where a step is
  optional.
  """
  @spec try_(t()) :: t()
  def try_(tactic) do
    fn goal ->
      case tactic.(goal) do
        {:ok, _} = ok -> ok
        {:error, _} -> {:ok, [goal]}
      end
    end
  end

  @doc """
  Keep only the goals that remain open.

  `{:ok, []}` stays `{:ok, []}`; a single open goal passes through unchanged.
  Present so callers can normalise a result before inspecting it.
  """
  @spec open_goals(result()) :: [goal()]
  def open_goals({:ok, %Result{goals: goals}}), do: goals
  def open_goals({:ok, goals}), do: goals
  def open_goals({:error, _}), do: []

  @doc """
  Whether a result closed the goal.
  """
  @spec closed?(result()) :: boolean()
  def closed?({:ok, %Result{goals: []}}), do: true
  def closed?({:ok, []}), do: true
  def closed?(_other), do: false
end
