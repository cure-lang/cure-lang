defmodule Antigen.Generators.SeedPool do
  @moduledoc """
  Corpus-backed fillers (spec §3): reuse *closed* banked `:typed_term` seeds as
  well-typed fillers, indexed by their kernel-checked recorded type. Only
  `:typed_term` seeds qualify — a `:mutant_term`'s `type` is a nominal fault-site
  goal its term does NOT actually inhabit. Backend-free (no sampling backend named
  directly): `load/1` reads via `Antigen.Corpus`, `pool_gen/2` builds via the
  `Antigen.Gen` DSL, and closedness delegates to `Cure.Core.Term.closed?/1`.
  """
  alias Antigen.{Corpus, Gen}
  alias Cure.Core.Term

  @spec load(String.t()) :: %{Term.t() => [Term.t()]}
  def load(path) do
    Corpus.stream(path)
    |> Enum.flat_map(fn
      {:ok, %{kind: :typed_term, payload: %{ctx: [], type: type, term: term}}} ->
        if Term.closed?(term), do: [{type, term}], else: []

      _ ->
        []
    end)
    |> Enum.group_by(fn {type, _} -> type end, fn {_, term} -> term end)
  end

  @spec pool_gen(%{Term.t() => [Term.t()]}, Term.t()) :: Gen.t() | :none
  def pool_gen(pool, goal) do
    case Map.get(pool, goal) do
      nil -> :none
      [] -> :none
      terms -> Gen.member_of(terms)
    end
  end
end
