defmodule Antigen.Triage do
  @moduledoc """
  Infection triage: minimize a reified `Challenge` to a joint fixpoint of
  structural bisect (whole name-referenced element drops) and value shrink
  (term rewrites + de-Bruijn ctx-drop), under one same-violation-shape predicate
  and one shared step budget. Deterministic, monotone (size strictly decreases on
  each accepted step), budget-bounded, `safe_pred`-guarded. Bisect candidates are
  tried before shrink candidates each round so structural cuts precede term
  rewrites (spec §7).
  """
  alias Antigen.{Challenge, Shrink, Bisect}

  @type stats :: %{
          orig_size: non_neg_integer(),
          min_size: non_neg_integer(),
          bisect_drops: non_neg_integer(),
          shrink_rewrites: non_neg_integer()
        }

  @spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer()) ::
          {Challenge.t(), stats}
  def minimize(%Challenge{} = ch, pred, budget) do
    orig = size(ch)
    {out, counts, _b} = sweep(ch, pred, budget, %{bisect: 0, shrink: 0})
    {out, %{orig_size: orig, min_size: size(out), bisect_drops: counts.bisect, shrink_rewrites: counts.shrink}}
  end

  # One accepted step at a time; restart the combined list on every acceptance.
  defp sweep(ch, pred, budget, counts) do
    cur = size(ch)

    cands =
      Enum.map(Bisect.candidates(ch), &{:bisect, &1}) ++
        Enum.map(Shrink.candidates(ch), &{:shrink, &1})

    case first_accepted(cands, pred, budget, cur) do
      {:accepted, tag, ch2, b2} ->
        sweep(Shrink.reseed(ch2), pred, b2, Map.update!(counts, tag, &(&1 + 1)))

      {:none, _b2} ->
        {ch, counts, budget}
    end
  end

  defp first_accepted(_cands, _pred, 0, _cur), do: {:none, 0}
  defp first_accepted([], _pred, b, _cur), do: {:none, b}

  defp first_accepted([{tag, cand} | rest], pred, b, cur) do
    cond do
      # no budget spent
      not Shrink.well_formed?(cand) -> first_accepted(rest, pred, b, cur)
      # non-reducing: skip
      size(cand) >= cur -> first_accepted(rest, pred, b, cur)
      safe_pred(pred, cand) -> {:accepted, tag, cand, b - 1}
      true -> first_accepted(rest, pred, b - 1, cur)
    end
  end

  defp safe_pred(pred, c) do
    pred.(c)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  @doc "Kind-agnostic size: term nodes across all pieces + count of list elements."
  @spec size(Challenge.t()) :: non_neg_integer()
  def size(%Challenge{payload: p} = ch) do
    {_scaffold, pieces} = Challenge.to_pieces(ch)

    term_size =
      Enum.reduce(pieces, 0, fn {_id, t}, acc ->
        acc + node_count(t) + numeral_magnitude(t)
      end)

    term_size + list_elements(p)
  end

  # Read each list-structured component defensively (absent ⇒ 0). No kind carries
  # all five; :elab_program carries none (its list_elements is always 0).
  defp list_elements(p) do
    len(p, :ctx) + len(p, :defs) + len(p, :ctors) + len(p, :families) + len(p, :focus)
  end

  defp len(p, key) do
    case Map.get(p, key) do
      l when is_list(l) -> length(l)
      _ -> 0
    end
  end

  # local copies of Shrink's structural measures (kept private there); identical math
  defp node_count(t) when is_tuple(t),
    do: 1 + (t |> Tuple.to_list() |> tl() |> Enum.map(&node_count/1) |> Enum.sum())

  defp node_count(l) when is_list(l), do: l |> Enum.map(&node_count/1) |> Enum.sum()
  defp node_count(_), do: 0

  defp numeral_magnitude({:ctor, :S, [n]}), do: 1 + numeral_magnitude(n)

  defp numeral_magnitude(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&numeral_magnitude/1) |> Enum.sum()

  defp numeral_magnitude(l) when is_list(l), do: l |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(_), do: 0
end
