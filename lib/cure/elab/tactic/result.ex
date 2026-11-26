defmodule Cure.Elab.Tactic.Result do
  @moduledoc """
  Remaining goals and checked solutions produced by a tactic.

  Solutions are keyed by original goal identity, so sequencing and focusing
  retain the evidence needed to reconstruct a closed proof.
  """

  defstruct goals: [], solutions: %{}, pending: %{}

  @type t :: %__MODULE__{
          goals: [Cure.Elab.ProofGoal.t()],
          solutions: %{reference() => %{evidence: term(), trace: [term()]}},
          pending: map()
        }

  @doc false
  def settle(%__MODULE__{} = result, previous \\ nil) do
    ranks = (previous || result.goals) |> Enum.with_index() |> Map.new(fn {goal, index} -> {goal.id, index} end)

    ranks =
      Enum.reduce(Map.keys(result.pending), ranks, fn id, ranks ->
        Map.put(ranks, id, rank(id, result.pending, ranks))
      end)

    settle_ranked(result, ranks)
  end

  defp rank(id, pending, ranks) do
    case Map.fetch(ranks, id) do
      {:ok, index} ->
        index

      :error ->
        case Map.get(pending, id) do
          nil -> 1_000_000
          frame -> frame.children |> Map.keys() |> Enum.map(&rank(&1, pending, ranks)) |> Enum.min(fn -> 1_000_000 end)
        end
    end
  end

  defp settle_ranked(result, ranks) do
    Enum.reduce_while(result.pending, {:ok, result}, fn {id, frame}, {:ok, current} ->
      child_ids = Map.keys(frame.children)

      if Map.has_key?(current.pending, id) and Enum.any?(child_ids, &Map.has_key?(current.solutions, &1)) do
        case Cure.Elab.Tactic.Apply.advance(frame, current.solutions) do
          {:ok, next_frame, goals, solution} ->
            old_ids = MapSet.new(if solution, do: descendants(child_ids, current.pending), else: child_ids)
            remaining = Enum.reject(current.goals, &MapSet.member?(old_ids, &1.id))

            pending =
              if solution,
                do: Map.drop(current.pending, [id | MapSet.to_list(old_ids)]),
                else: Map.put(current.pending, id, next_frame)

            solutions = if solution, do: Map.put(current.solutions, id, solution), else: current.solutions
            frontier = Map.new(current.goals, &{&1.id, &1})

            goals =
              goals
              |> Enum.reject(&Map.has_key?(pending, &1.id))
              |> Enum.map(&Map.get(frontier, &1.id, &1))

            ordered =
              Enum.sort_by(goals ++ remaining, fn goal -> Map.get(ranks, goal.id, Map.get(ranks, id, 1_000_000)) end)

            {:cont, {:ok, %{current | goals: ordered, pending: pending, solutions: solutions}}}

          {:error, _} = error ->
            {:halt, error}
        end
      else
        {:cont, {:ok, current}}
      end
    end)
    |> case do
      {:ok, ^result} -> {:ok, result}
      {:ok, next} -> settle_ranked(next, ranks)
      error -> error
    end
  end

  defp descendants(ids, pending) do
    Enum.flat_map(ids, fn id ->
      case Map.get(pending, id) do
        nil -> [id]
        frame -> [id | descendants(Map.keys(frame.children), pending)]
      end
    end)
  end
end
