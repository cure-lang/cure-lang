defmodule Cure.Core.Universe do
  @moduledoc """
  The fixed, small, predicative universe hierarchy `Type 0 : Type 1 : Type 2`
  with cumulativity (`Type i <: Type i+1`).

  This is deliberately not `Type : Type` (which is Girard-inconsistent and
  non-normalizing) and not full universe polymorphism — just the two-level
  separation the FRP port needs (`SigDesc : Type 1`), per design spec §3/§4.3.
  """

  @ceiling 2

  @doc "The highest universe level (inclusive)."
  @spec ceiling() :: non_neg_integer()
  def ceiling, do: @ceiling

  @doc "The level of `Π`/`Σ` over domains at `l1` and `l2` — the larger of the two."
  @spec max(non_neg_integer(), non_neg_integer()) :: non_neg_integer()
  def max(l1, l2), do: Kernel.max(l1, l2)

  @doc "Cumulative ordering: true when `Type l1` is included in `Type l2` (`l1 ≤ l2`)."
  @spec le?(non_neg_integer(), non_neg_integer()) :: boolean()
  def le?(l1, l2), do: l1 <= l2

  @doc """
  The universe that `Type level` itself inhabits: `Type level : Type (level+1)`.

  Returns `{:error, :universe_ceiling}` when that successor would exceed the
  fixed ceiling (a program needing `Type #{@ceiling + 1}`).
  """
  @spec succ(non_neg_integer()) :: {:ok, non_neg_integer()} | {:error, :universe_ceiling}
  def succ(level) when level + 1 <= @ceiling, do: {:ok, level + 1}
  def succ(_level), do: {:error, :universe_ceiling}
end
