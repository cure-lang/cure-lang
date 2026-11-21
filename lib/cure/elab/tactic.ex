defmodule Cure.Elab.Tactic do
  @moduledoc """
  The tactic monad: a uniform result shape for proof commands, and the
  combinators that compose them.

  This is the `Lean.Elab.Tactic` analogue described in
  `docs/PATH_TO_LEAN4_PLAN.md` Phase 2. It adds **no** Core constructors and
  **no** kernel rules: every tactic returns ordinary evidence that the kernel
  re-checks, exactly as a hand-written proof term would.

  ## The result shape

  A tactic transforms a goal and reports what remains:

      @type result :: {:ok, [Goal.t()]} | {:ok, []} | {:error, Diagnostic.t()}

  `{:ok, []}` means the goal is CLOSED. `{:ok, [goal]}` means it is still open,
  with the (possibly transformed) goal returned. This is Lean's shape: a tactic
  returns the *remaining* goals, so `[]` is the success condition.

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
  public registration point for user tactics; that is Phase 3 (`tactic` macro
  rules), which expands to these combinators rather than to Core terms.
  """

  alias Cure.Elab.ProofGoal

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
  @type result :: {:ok, [goal()]} | {:error, error()}

  @typedoc "A tactic: a function from a goal to the remaining goals."
  @type t :: (goal() -> result())

  @doc """
  Lift a `ProofGoal` command result into the tactic result shape.

  `ProofGoal` reports `{:closed, evidence, trace}` for a closed goal; the tactic
  shape reports `{:ok, []}`. The evidence and trace are deliberately NOT carried
  in the tactic result: `ProofGoal` already holds them in its own trace, and a
  tactic returning evidence would let a caller assemble a proof without the
  kernel re-checking it. Keeping the tactic result free of terms is what makes
  every tactic untrusted-but-checked.
  """
  @spec of_command_result(ProofGoal.command_result(), goal()) :: result()
  def of_command_result({:closed, _evidence, _trace}, _goal), do: {:ok, []}
  def of_command_result({:open, next_goal}, _goal), do: {:ok, [next_goal]}
  def of_command_result({:error, reason}, _goal), do: {:error, reason}

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
  @spec run_all(t(), [goal()]) :: result()
  def run_all(_tactic, []), do: {:ok, []}

  def run_all(tactic, goals) do
    Enum.reduce_while(goals, {:ok, []}, fn goal, {:ok, acc} ->
      case tactic.(goal) do
        {:ok, remaining} -> {:cont, {:ok, acc ++ remaining}}
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
  @spec repeat(t(), pos_integer()) :: t()
  def repeat(tactic, max_steps \\ 100) do
    fn goal -> repeat_loop(tactic, [goal], max_steps) end
  end

  defp repeat_loop(_tactic, goals, 0), do: {:ok, goals}

  defp repeat_loop(tactic, goals, steps) do
    case run_all(tactic, goals) do
      {:ok, []} -> {:ok, []}
      {:ok, ^goals} -> {:ok, goals}
      {:ok, next} -> repeat_loop(tactic, next, steps - 1)
      {:error, _} = error -> error
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
  def open_goals({:ok, goals}), do: goals
  def open_goals({:error, _}), do: []

  @doc """
  Whether a result closed the goal.
  """
  @spec closed?(result()) :: boolean()
  def closed?({:ok, []}), do: true
  def closed?(_other), do: false
end
