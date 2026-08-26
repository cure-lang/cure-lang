defmodule Antigen.UniversesSeedTest do
  @moduledoc """
  Banks the W5 universes vertical (pre-port banking spec §4 W5; roadmap A4 —
  first Antigen coverage of the universe rules). Ill-typed probes are antibodies
  (corpus.sexp); well-typed probes are known-good seeds (seeds.sexp). Idempotent.

  Store deltas: corpus +3 antibodies, seeds +2 (NOT +3). `stratification(:well_typed)`
  and `ctor_field(:well_typed)` are coverage-equivalent under the plateauing seed
  key (`ctors=[type]|depth=b0_2|flags=[]|label=well_typed`), so only the first
  banks as a seed — by design, one seed per coverage cell (the coverage key IS the
  seed store's identity; making it finer would orphan every stored key).
  `ctor_field(:well_typed)`'s acceptance remains guarded on every run by the assay
  test in `universes_test.exs`.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Universes

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"

  @antibodies [
    Universes.type_in_type(:ill_typed),
    Universes.ceiling(:ill_typed),
    Universes.ctor_field(:ill_typed),
    Universes.indexed_ctor(:ill_typed),
    # family-level ceiling: check_family must range-check the declared level, not
    # only the telescopes. Regresses to {:wrongly_accepted, :Over} if it doesn't.
    Universes.family_ceiling(:ill_typed)
  ]

  @seed_candidates [
    Universes.cumulativity(:well_typed),
    Universes.stratification(:well_typed),
    Universes.ctor_field(:well_typed),
    Universes.indexed_ctor(:well_typed)
  ]

  test "universes antibodies + seeds are banked and every one replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    for s <- @seed_candidates, Assays.Universes.run(s) == :ok do
      Corpus.append(@seeds, s, Corpus.dedup_key(s, :seed))
    end

    results = Runner.replay([@corpus, @seeds], %{"universes" => Assays.Universes})

    uni =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "universes"}, r.entry)
      end)

    # 4 antibodies + 3 seeds: stratification(:well_typed) and ctor_field(:well_typed)
    # share one coverage cell (see moduledoc), so the seed store holds one of them;
    # indexed_ctor(:well_typed) banks a distinct cell (Int-indexed result index).
    assert length(uni) >= 7

    assert Enum.all?(uni, &(&1.verdict == :ok)),
           inspect(uni |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
