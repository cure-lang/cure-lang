defmodule Antigen.UniverseHistoricalInferenceControlsTest do
  use ExUnit.Case, async: false
  alias Antigen.{Challenge, Runner}
  alias Antigen.Corpus.{LegacyImport, Migration}

  @preimage "test/antigen/fixtures/pre_universe_corpus_v2/seeds.sexp"
  @rows [43, 87, 107, 178, 234]

  test "five reviewed invalid positives retain exact inference inputs in distinct negative controls" do
    lines = Antigen.Corpus.record_lines(@preimage)

    for row <- @rows do
      assert {:ok, %{challenge: original}} =
               LegacyImport.decode_record(Enum.at(lines, row - 1), from: :fixed_ceiling_v1)

      {negative, positive, checks} = Migration.inference_controls(original)
      assert %Challenge{kind: :malformed, assay: "term/rejection", label: :ill_typed} = negative
      assert negative.payload == Map.take(original.payload, [:sig, :ctx, :term])
      assert positive.assay == original.assay
      assert positive.payload.ctx == original.payload.ctx
      assert positive.payload.type != original.payload.type
      assert checks["context_prefixes"] == 4
      assert checks["motives_checked"] > 0
      assert checks["cases_checked"] > 0
      assert checks["positive_claim"] == "ok"
      assert :ok = Runner.replay_one(negative)
      assert :ok = Runner.replay_one(positive)
    end
  end
end
