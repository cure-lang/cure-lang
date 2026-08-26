defmodule Antigen.Bisect do
  @moduledoc """
  Structural delta-debugging (ddmin) over a challenge's **name-referenced** list
  components — `defs` (def_group/forcing_pair/stuck_elim), `ctors` (family),
  `families` (indexed_case/rewrite_eq). Each candidate removes one whole element
  (a pure `List.delete_at` on the decoded payload — no de-Bruijn reindexing,
  since members are referenced by `{:global, name}`, not by index) and prunes any
  now-dangling `focus` entry naming a removed def. The orchestrator
  (`Antigen.Triage`) tests each candidate under the same violation-shape
  predicate shrink uses; safety is the predicate, not static analysis (spec §6).
  """
  alias Antigen.Challenge

  @def_kinds [:def_group, :forcing_pair, :stuck_elim]

  @spec candidates(Challenge.t()) :: [Challenge.t()]
  def candidates(%Challenge{kind: k, payload: %{defs: defs} = p} = ch) when k in @def_kinds do
    for i <- index_range(defs) do
      dropped = Enum.at(defs, i).name
      %{ch | payload: %{p | defs: List.delete_at(defs, i), focus: Map.get(p, :focus, []) -- [dropped]}}
    end
  end

  def candidates(%Challenge{kind: :family, payload: %{ctors: ctors} = p} = ch) do
    for i <- index_range(ctors), do: %{ch | payload: %{p | ctors: List.delete_at(ctors, i)}}
  end

  def candidates(%Challenge{kind: k, payload: %{families: fams} = p} = ch)
      when k in [:indexed_case, :rewrite_eq] do
    for i <- index_range(fams), do: %{ch | payload: %{p | families: List.delete_at(fams, i)}}
  end

  def candidates(%Challenge{}), do: []

  # `0..(n-1)//1` — the `//1` avoids the `0..-1` phantom-range footgun when n=0.
  defp index_range(list), do: 0..(length(list) - 1)//1
end
