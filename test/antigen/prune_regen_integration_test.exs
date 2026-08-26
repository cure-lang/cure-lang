defmodule Antigen.PruneRegenIntegrationTest do
  @moduledoc """
  End-to-end: prune a mixed corpus and regenerate a seed pool on tmp copies, then
  replay both through the live kernel exactly as `corpus_replay_test` does. Prune's
  keep-criterion IS that gate's criterion, so the post-run stores must be all-green
  by construction. The committed stores are never touched.
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Prune, Regen, Runner}

  @tmp "tmp/antigen_prune_regen_integration_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "after prune + regen, corpus and seeds both replay all-:ok (gate green by construction)" do
    corpus = Path.join(@tmp, "corpus.sexp")
    seeds = Path.join(@tmp, "seeds.sexp")
    retired = Path.join(@tmp, "retired.sexp")

    keep = Corpus.encode_record(Challenge.stub({:type, 0}))

    bad =
      Regex.replace(~r/pieces=.*$/, Corpus.encode_record(Challenge.stub({:type, 1})), "pieces=t::(zzz_unknown_node 1)")

    File.write!(corpus, keep <> "\n" <> bad <> "\n")

    assert %{kept: 1, retired: 1} = Prune.prune(corpus, retired)

    assert %{seeds_banked: n} =
             Regen.regenerate_seeds(
               seeds_path: seeds,
               count: 60,
               gen: Antigen.Generators.Totality.gen()
             )

    assert n > 0

    # the replay gate's own check: every remaining record decodes and replays :ok
    results = Runner.replay([corpus, seeds], Runner.replay_registry())
    assert results != []

    assert Enum.all?(results, &(&1.verdict == :ok)),
           "post-prune/regen stores are not all-green: " <>
             inspect(Enum.reject(results, &(&1.verdict == :ok)))
  end
end
