defmodule Antigen.CorpusReplayTest do
  @moduledoc """
  The permanent regression harness (spec §7, §8 replayer). Decodes the two
  committed, never-pruned stores and re-runs each entry's assay **through the
  kernel** — read-only, non-fail-fast, never mutating the files (so `mix test`
  stays git-clean).

  The mutual-recursion hole has since been **fixed** in `Cure.Core.Certificate`
  (mutual-cycle detection), so every committed entry now satisfies its invariant
  and the invariant-check test below is GREEN. The two antibodies remain in the
  corpus as **permanent regression guards** (never pruned, spec §7.1): if the hole
  is ever reintroduced, `totality/diverging` and `reflexivity` replay to a
  violation again and this test goes red.
  """
  use ExUnit.Case, async: true
  alias Antigen.Runner

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"

  # The single source of truth for assay dispatch — the same registry `mix antigen`
  # replays through (`Runner.replay_registry/0`, built from every registered assay).
  # A previous hand-maintained subset here silently drifted: valid seeds banked for
  # newer assays (kernel/beta_subst, elab/shift_agrees, serialize/*, delta/nf,
  # forcing/dot, …) replayed to `{:violation, {:unknown_assay, _}}` — a false
  # regression from a stale test fixture, not a real kernel defect.
  @registry Runner.replay_registry()

  test "both committed corpora decode without error (structural integrity)" do
    for path <- [@corpus, @seeds], File.exists?(path) do
      results = Runner.replay([path], @registry)
      refute results == []
      assert Enum.all?(results, fn r -> not match?({:decode_error, _, _}, r.verdict) end)
    end
  end

  test "replay does not mutate the committed corpora (git-clean for CI)" do
    for path <- [@corpus, @seeds], File.exists?(path) do
      before = File.read!(path)
      Runner.replay([path], @registry)
      assert File.read!(path) == before
    end
  end

  test "every committed entry satisfies its assay invariant (regression guard)" do
    failing =
      Runner.replay([@corpus, @seeds], @registry)
      |> Enum.reject(fn r -> r.verdict == :ok end)

    assert failing == [],
           "#{length(failing)} committed entr(y/ies) fail their invariant — the " <>
             "mutual-recursion hole may have regressed: " <>
             inspect(Enum.map(failing, & &1.verdict))
  end

  test "the replay registry dispatches broad assays the old hardcoded subset lacked" do
    # Red-green guard for the stale-fixture finding: these assays all have banked
    # seeds but were absent from the hand-maintained subset, so replay misreported
    # them as `unknown_assay`. The shared registry must dispatch every one.
    for assay <-
          ~w(kernel/beta_subst kernel/zeta_subst kernel/grade_conv elab/shift_agrees serialize/roundtrip serialize/decode
             conv/decision check/verdict branchunify/verdict delta/nf forcing/dot term/rejection) do
      assert Map.has_key?(@registry, assay), "replay registry does not dispatch #{assay}"
    end
  end

  test "banked :mutant_term seeds replay as correct rejections" do
    seeds = Antigen.Corpus.stream(@seeds) |> Enum.map(fn {:ok, c} -> c end)
    mutants = Enum.filter(seeds, &(&1.kind == :mutant_term))
    assert mutants != [], "no :mutant_term seeds banked yet"
    for c <- mutants, do: assert(Antigen.Assays.Mutation.run(c) == :ok)
  end
end
