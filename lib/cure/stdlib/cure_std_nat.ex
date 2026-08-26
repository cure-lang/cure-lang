defmodule :cure_std_nat do
  @moduledoc """
  Runtime helper for `Std.Nat`.

  Target of the `@extern` bridge `Std.Nat.of_int`. A `Nat` erases to a
  non-negative native integer (`Z -> 0`, `S(n) -> n + 1`, matched by
  peel-on-demand: `N > 0 -> N - 1`), so casting an `Int` to a `Nat` is `max(i, 0)`
  at run time. The cast cannot be written as structural recursion — a primitive
  `Int` is not well-founded — so it is an asserted primitive boundary, exactly
  where Idris marks `integerToNat` total. Clamping negatives to `0` keeps the
  erased value a valid `Nat`: a negative integer would match neither the `Z`
  (== 0) nor the `S` (> 0) branch and would crash `range_from`.
  """

  @doc "Clamp an Int to a Nat (== max(i, 0)); Nat erases to a non-negative integer."
  def of_int(i) when is_integer(i), do: max(i, 0)
end
