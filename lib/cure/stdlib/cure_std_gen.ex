defmodule :cure_std_gen do
  @moduledoc """
  Runtime helpers for `Std.Gen` property-based testing shrinkers (v0.23.0).

  Exposes the shrink strategies used by `Std.Test.forall/3` when a
  property fails. The shrinker's job is to narrow the failing input
  from whatever random value the generator produced down to the
  smallest value that still fails the property.

  ## Strategies shipped here

  - `shrink_int/1` -- halves toward zero (`n, n div 2, n div 4, ..., 0`)
    and also emits `n - 1` so the shrinker can probe \"one step smaller\".
  - `shrink_list/1` -- drops elements. The single most useful list
    shrink: shorter lists come first so the shrinker converges fast on
    the minimum failing length.
  - `shrink/1` -- polymorphic entry point. Dispatches on the runtime
    shape of the value (int, list, tuple) to pick the right strategy.

  User-defined shrinkers can still be passed explicitly to `forall/3`;
  this module only provides the defaults.
  """

  @doc "Shrink an integer toward zero."
  def shrink_int(0), do: []

  def shrink_int(n) when is_integer(n) and n > 0 do
    Enum.uniq(candidates_pos(n)) |> Enum.reject(&(&1 == n))
  end

  def shrink_int(n) when is_integer(n) and n < 0 do
    Enum.uniq([-n | Enum.map(candidates_pos(-n), &(-&1))])
    |> Enum.reject(&(&1 == n))
  end

  defp candidates_pos(n) do
    halves =
      Stream.iterate(div(n, 2), &div(&1, 2))
      |> Stream.take_while(&(&1 > 0))
      |> Enum.to_list()

    [0 | halves] ++ [n - 1]
  end

  @doc "Shrink a list by dropping elements, shortest first."
  def shrink_list([]), do: []

  def shrink_list(xs) when is_list(xs) do
    len = length(xs)

    drop_candidates =
      for take <- 0..(len - 1) do
        Enum.take(xs, take)
      end

    single_drops =
      for idx <- 0..(len - 1) do
        List.delete_at(xs, idx)
      end

    (drop_candidates ++ single_drops)
    |> Enum.uniq()
    |> Enum.reject(&(&1 == xs))
  end

  @doc """
  Runtime-shape dispatch, used internally by `:cure_std_test`'s shrink loop.

  **Not part of the axiom surface.** No `@extern` points here. It used to be
  postulated as `Std.Gen.shrink : ∀t. t -> List(t)`, which no parametric
  function inhabits — the free theorem requires `shrink(g x) == map(g, shrink x)`
  and this violates it. The Cure-visible shrinker is now the `Shrink(t)`
  interface in `lib/std/gen.cure`, whose method may legitimately dispatch on `t`.

  Erlang has no types to erase, so dispatching here is fine; the lie was in the
  Cure signature, not in this code.
  """
  def shrink(n) when is_integer(n), do: shrink_int(n)
  def shrink(xs) when is_list(xs), do: shrink_list(xs)

  def shrink(tuple) when is_tuple(tuple) do
    # Shrink each element of the tuple independently; combine.
    list = Tuple.to_list(tuple)

    for {_v, idx} <- Enum.with_index(list), cand <- shrink(Enum.at(list, idx)) do
      List.replace_at(list, idx, cand) |> List.to_tuple()
    end
  end

  def shrink(_), do: []
end
