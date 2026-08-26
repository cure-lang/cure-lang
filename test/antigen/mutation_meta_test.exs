defmodule Antigen.MutationMetaTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Corpus, Challenge}

  @seeds_path "test/antigen/seeds.sexp"
  test "banked :mutant_term seed corpus meets the diversity floor (static replay)" do
    banked =
      Corpus.stream(@seeds_path)
      |> Enum.flat_map(fn
        {:ok, %Challenge{kind: :mutant_term} = c} -> [c]
        _ -> []
      end)

    assert banked != [], "no :mutant_term seeds banked yet"
    m = Runner.mutation_metrics(banked)
    assert m.reason_diversity >= 5, "banked reason_diversity #{m.reason_diversity} below floor"
  end

  test "banked :mutant_term corpus meets depth + wrapper-diversity floors (static replay)" do
    banked =
      Corpus.stream(@seeds_path)
      |> Enum.flat_map(fn
        {:ok, %Challenge{kind: :mutant_term} = c} -> [c]
        _ -> []
      end)

    m = Runner.mutation_metrics(banked)
    assert m.max_depth >= 4, "banked max_depth #{m.max_depth} below floor"
    assert m.wrap_diversity >= 4, "banked wrap_diversity #{m.wrap_diversity} below floor"
  end

  test "banked conversion corpus: both polarities present, replay to correct verdicts" do
    banked =
      Corpus.stream(@seeds_path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c]
        _ -> []
      end)

    m = Runner.conversion_metrics(banked)
    assert m.conv_carrier_diversity >= 2, "banked conv carriers #{m.conv_carrier_diversity} < 2"
    assert m.conv_both_polarities, "banked conversion missing a polarity"

    for c <- banked, c.kind == :mutant_term, Map.get(c.payload.fault, :witness) == :conv do
      # reject seeds are correctly rejected
      assert Antigen.Assays.Mutation.run(c) == :ok
    end

    for c <- banked, Runner.conv_carrier_of(c) != nil do
      # accept seeds are correctly accepted
      assert Antigen.Assays.Term.run(c) == :ok
    end
  end
end
