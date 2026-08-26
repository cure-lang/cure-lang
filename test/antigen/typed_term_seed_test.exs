defmodule Antigen.TypedTermSeedTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Coverage}
  alias Antigen.Generators.SigMenu

  defp sample_challenge do
    Challenge.new(
      kind: :typed_term,
      assay: "term/infer_check",
      label: :well_typed,
      payload: %{sig: :v1, ctx: [SigMenu.nat()], type: SigMenu.nat(), term: {:var, 0}}
    )
  end

  test "to_pieces / from_pieces round-trip preserves the challenge" do
    c = sample_challenge()
    {scaffold, pieces} = Challenge.to_pieces(c)
    rebuilt = Challenge.from_pieces(:typed_term, c.assay, c.label, c.seed, c.note, scaffold, pieces)
    assert rebuilt.payload == c.payload
    assert rebuilt.kind == :typed_term
  end

  test "corpus encode → decode is identity" do
    c = sample_challenge()
    line = Corpus.encode_record(c)
    assert {:ok, decoded} = Corpus.decode_record(line)
    assert decoded.kind == :typed_term
    assert decoded.payload == c.payload
  end

  test "terms_of returns type, term, and ctx entries" do
    assert Coverage.terms_of(sample_challenge()) == [SigMenu.nat(), {:var, 0}, SigMenu.nat()]
  end
end
