defmodule Antigen.IndexedSeedTest do
  @moduledoc """
  Banks the indexed/case vertical's permanent stores (spec §7) and guards that
  every banked record replays through the kernel to `:ok`. Idempotent: on a fresh
  checkout the committed records are already present, so `Corpus.append/3` finds
  them via its `seen?` dedup and writes nothing (keeping `mix test` git-clean).
  Run in isolation first to generate the files, then commit them.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Indexed

  @seeds "test/antigen/seeds.sexp"
  @corpus "test/antigen/corpus.sexp"

  # Confirmed 4.1 regression guard: a Dec case with a foreign `MkFoo` (Foo) branch.
  # Post-fix the kernel rejects it, so it replays :ok; if the family-scoping fix
  # regresses, it replays {:wrongly_accepted, _} and the invariant test goes red.
  # discharge(:ill_typed): a REACHABLE wrap branch with an ill-typed body. The
  # kernel must reject it; if impossible-branch discharge ever over-fires on a
  # live branch it would be {:wrongly_accepted, _} — a soundness regression.
  # injectivity(:ill_typed): a branch demanding an equation the match never
  # entails (IW(MkWr Dcoupled) when injectivity can only give n := Causal). The
  # kernel must reject it; if injectivity ever fabricates a false equation it
  # would be {:wrongly_accepted, _} — a soundness regression.
  # deletion(:ill_typed): a branch REACHABLE via the deletion rule (equal
  # literal indices, 3 ~ 3 ⇒ consistent, no refinement) with an ill-typed body.
  # The kernel must reject it; if deletion ever degrades to :impossible (or
  # skips the body check) it would be {:wrongly_accepted, _} — a soundness
  # regression (W3, roadmap A2/#23).
  # motive_indexed_domain: the convoy motive `λs. Π(SNat s). Dec` (indexed family
  # as a Π domain). The :well_typed record is a permanent guard that the
  # completeness fix (value-recursion in infer_type_value_sort) is not reverted —
  # if it regresses it replays {:wrongly_rejected, {_, :bad_motive}}. The :ill_typed
  # record is the mandatory NEGATIVE CONTROL: a Π domain that is a Dec VALUE
  # (Dcoupled), not a type; if the value-recursion ever starts accepting a non-type
  # domain (a false positive / soundness bug) it replays {:wrongly_accepted, _}.
  @antibodies [
    Indexed.branch_family(:ill_typed),
    Indexed.discharge(:ill_typed),
    Indexed.injectivity(:ill_typed),
    Indexed.deletion(:ill_typed),
    Indexed.motive_indexed_domain(:well_typed),
    Indexed.motive_indexed_domain(:ill_typed),
    # Convoy soundness guards (indexed with-clause LHS re-match). The elaborator
    # convoy leans on these kernel properties; the negative controls go red if
    # either regresses. data_split: the kernel validates a {:data} slot split
    # against the signature (a wrong split is rejected, never mis-accepted).
    # reify_distinct: the reify {:vdata} collapse never lets conv equate two
    # distinct indexed types (incompleteness, not unsoundness).
    Indexed.data_split_validation(:well_typed),
    Indexed.data_split_validation(:ill_typed),
    Indexed.reify_collapse_distinct(:well_typed),
    Indexed.reify_collapse_distinct(:ill_typed)
  ]

  # Known-good-behavior seeds: every indexed/case challenge the kernel handles
  # correctly. `refinement(:well_typed)` is now included — the 4.3 incompleteness
  # (a dropped ground result index) is closed by unify_indices/4, so it replays
  # :ok and is a legitimate known-good seed.
  @seed_candidates [
    Indexed.branch_family(:well_typed),
    Indexed.coverage(:well_typed),
    Indexed.coverage(:ill_typed),
    Indexed.refinement(:well_typed),
    Indexed.refinement(:ill_typed),
    Indexed.motive_wf(:well_typed),
    Indexed.motive_wf(:ill_typed),
    Indexed.discharge(:well_typed),
    Indexed.injectivity(:well_typed),
    Indexed.deletion(:well_typed)
  ]

  test "indexed/case antibodies + seeds are banked and every one replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    for s <- @seed_candidates, Assays.Indexed.run(s) == :ok do
      Corpus.append(@seeds, s, Corpus.dedup_key(s, :seed))
    end

    reg = %{"indexed/case" => Assays.Indexed}
    results = Runner.replay([@corpus, @seeds], reg)

    indexed = Enum.filter(results, fn r -> match?(%Antigen.Challenge{assay: "indexed/case"}, r.entry) end)
    refute indexed == []

    assert Enum.all?(indexed, fn r -> r.verdict == :ok end),
           "indexed/case replay produced a non-:ok verdict: " <>
             inspect(indexed |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
