defmodule Antigen.CorpusAtomsTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  @corpora ~w(seeds.sexp corpus.sexp coverage.sexp reach.sexp)
           |> Enum.map(&Path.join("test/antigen", &1))

  test "every active committed record reconstructs its whitelisted scaffold symbols" do
    for path <- @corpora, line <- Corpus.record_lines(path) do
      assert {:ok, challenge} = Corpus.decode_record(line),
             "#{path}: current record failed to reconstruct"

      assert challenge.kind in Challenge.__known_atoms__()
      assert challenge.label in Challenge.__known_atoms__()
      assert {:ok, reconstructed} = Corpus.decode_record(Corpus.encode_record(challenge))
      assert Corpus.semantic_descriptor(reconstructed) == Corpus.semantic_descriptor(challenge)
    end
  end

  test "every active store uses current framed Core pieces and separate diagnostic JSON" do
    for path <- @corpora, line <- Corpus.record_lines(path) do
      fields =
        line
        |> String.split("\t")
        |> tl()
        |> Map.new(fn field -> field |> String.split("=", parts: 2) |> List.to_tuple() end)

      assert fields["format"] == "2"
      assert fields["universe"] == Corpus.universe_epoch()
      refute Map.has_key?(fields, "pieces") or Map.has_key?(fields, "fault")

      for [_id, body] <- fields["pieces64"] |> Base.decode64!() |> :json.decode() do
        assert String.starts_with?(body, "(cure-core 2 ")
        assert {:ok, _} = Cure.Core.Serialize.decode(body)
      end

      if fields["fault64"], do: assert(is_map(fields["fault64"] |> Base.decode64!() |> :json.decode()))
    end
  end
end
