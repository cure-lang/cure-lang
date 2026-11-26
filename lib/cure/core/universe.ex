defmodule Cure.Core.Universe do
  @moduledoc """
  Unbounded predicative closed-level arithmetic helpers.

  The fixed three-level ceiling (`Type0 : Type1 : Type2`) has been retired by
  the Agda-style universe-polymorphism specification (Phase 5 U3). Canonical
  open/finite/limit universe sorting lives in `Cure.Core.UniverseLevel` and
  `Cure.Core.Sort`.
  """

  @doc "The level of `Π`/`Σ` over closed domains at `l1` and `l2` — the larger of the two."
  @spec max(non_neg_integer(), non_neg_integer()) :: non_neg_integer()
  def max(l1, l2) when is_integer(l1) and l1 >= 0 and is_integer(l2) and l2 >= 0,
    do: Kernel.max(l1, l2)

  @doc "Cumulative ordering on closed levels: true when `l1 <= l2`."
  @spec le?(non_neg_integer(), non_neg_integer()) :: boolean()
  def le?(l1, l2) when is_integer(l1) and l1 >= 0 and is_integer(l2) and l2 >= 0,
    do: l1 <= l2

  @doc "The successor of a closed level (`Type level : Type (level+1)`). Total — no ceiling."
  @spec succ(non_neg_integer()) :: {:ok, non_neg_integer()}
  def succ(level) when is_integer(level) and level >= 0, do: {:ok, level + 1}
end
