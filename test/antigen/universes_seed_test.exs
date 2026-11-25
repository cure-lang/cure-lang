defmodule Antigen.UniversesSeedTest do
  @moduledoc """
  Replays the committed universes stores and exercises idempotent banking only
  on temporary copies. Coverage-equivalent positive seeds may coalesce; every
  high-level candidate is independently assayed before banking regardless.
  Exactly two misbanked current-format ceiling claims are archived verbatim in
  the retirement inventory. Historical-format preimages remain verbatim in the
  explicit migration archive; active stores use the current format and identity.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Universes

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"
  @retirements "test/antigen/fixtures/universe_ceiling_retirements.json"
  @preimage "test/antigen/fixtures/pre_universe_corpus_v2/corpus.sexp"
  @levels [0, 37, 10 ** 40]

  @antibodies [Universes.type_in_type(:ill_typed), Universes.indexed_ctor(:ill_typed)] ++
                for(
                  level <- @levels,
                  challenge <- [
                    Universes.finite_successor(:ill_typed, level),
                    Universes.ctor_field(:ill_typed, level),
                    Universes.family_formation(:ill_typed, level)
                  ],
                  do: challenge
                )

  @seed_candidates [
                     Universes.cumulativity(:well_typed),
                     Universes.stratification(:well_typed),
                     Universes.indexed_ctor(:well_typed)
                   ] ++
                     for(
                       level <- @levels,
                       challenge <- [
                         Universes.finite_successor(:well_typed, level),
                         Universes.ctor_field(:well_typed, level),
                         Universes.family_formation(:well_typed, level)
                       ],
                       do: challenge
                     )

  @tag :tmp_dir
  test "universes antibodies and seeds bank idempotently on temporary copies and replay", %{tmp_dir: root} do
    before = {File.read!(@corpus), File.read!(@seeds)}
    corpus = Path.join(root, "corpus.sexp")
    seeds = Path.join(root, "seeds.sexp")
    File.cp!(@corpus, corpus)
    File.cp!(@seeds, seeds)

    for a <- @antibodies do
      assert :ok = Assays.Universes.run(a)
      assert Corpus.append(corpus, a, Corpus.dedup_key(a, :antibody)) in [:appended, :duplicate]
      assert :duplicate = Corpus.append(corpus, a, Corpus.dedup_key(a, :antibody))
    end

    for s <- @seed_candidates do
      assert :ok = Assays.Universes.run(s)
      assert Corpus.append(seeds, s, Corpus.dedup_key(s, :seed)) in [:appended, :duplicate]
      assert :duplicate = Corpus.append(seeds, s, Corpus.dedup_key(s, :seed))
    end

    for paths <- [[@corpus, @seeds], [corpus, seeds]] do
      uni =
        paths
        |> Runner.replay(%{"universes" => Assays.Universes})
        |> Enum.filter(&match?(%Antigen.Challenge{assay: "universes"}, &1.entry))

      assert length(uni) >= 7

      assert Enum.all?(uni, &(&1.verdict == :ok)),
             inspect(uni |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
    end

    assert before == {File.read!(@corpus), File.read!(@seeds)}
  end

  test "the retirement inventory preserves exact original claims and their reviewed replacements" do
    inventory = @retirements |> File.read!() |> :json.decode()
    assert [%{"id" => "def_ceiling"}, %{"id" => "family_ceiling"}] = inventory["retirements"]
    assert %{"tag" => "family_ceiling", "replacement_tag" => "family_formation"} = inventory["retired_kernel_probe"]
    active = Corpus.record_lines(@corpus)
    assert Enum.all?(active, &String.contains?(&1, "\tformat=2\t"))
    archived = Corpus.record_lines(@preimage)
    historical = Enum.reject(archived, &String.contains?(&1, "\tformat=2\t"))
    assert length(historical) == inventory["historical_record_count"]
    assert length(historical) == 49
    assert digest(Enum.join(historical, "\n") <> "\n") == inventory["historical_records_sha256"]

    for retired <- inventory["retirements"] do
      original = retired["record"]
      assert digest(original) == retired["sha256"]
      refute original in active
      assert {:ok, challenge} = Corpus.decode_record(original)
      assert challenge.label == :ill_typed
      assert {:violation, {:wrongly_accepted, _}} = Assays.Universes.run(challenge)
      assert :ok = Assays.Universes.run(%{challenge | label: :well_typed})
    end

    active_keys = MapSet.new(active, &Corpus.raw_key/1)

    for key <- inventory["replacement_antibody_keys"] do
      assert [record] = Enum.filter(archived, &(Corpus.raw_key(&1) == key))
      assert {:ok, challenge} = Corpus.decode_record(record)
      assert :ok = Assays.Universes.run(challenge)
      assert MapSet.member?(active_keys, Corpus.dedup_key(challenge, :antibody))
    end
  end

  defp digest(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
end
