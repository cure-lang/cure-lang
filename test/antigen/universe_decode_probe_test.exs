defmodule Antigen.UniverseDecodeProbeTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Runner}
  alias Antigen.Generators.DecodeProbe
  alias Cure.Core.Serialize

  defp challenge(input, label),
    do: Challenge.new(kind: :decode_probe, assay: "serialize/decode", label: label, payload: %{input: input})

  test "every advertised valid sample passes the current decoder and real assay" do
    _ = Challenge.__known_atoms__()

    for input <- DecodeProbe.valid_samples() do
      assert String.starts_with?(input, "(cure-core 2 ")
      assert {:ok, _} = Serialize.decode(input)
      assert :ok = Runner.replay_one(challenge(input, :valid_sexp))
    end

    assert Enum.any?(DecodeProbe.valid_samples(), &String.contains?(&1, "(level-nf 999)"))
  end

  test "nested negatives test inner parser/shape failures, not just missing framing" do
    for input <- DecodeProbe.invalid_samples() do
      assert String.starts_with?(input, "(cure-core 2 ")
      assert {:error, reason} = Serialize.decode(input)
      refute reason == :incompatible_core_format
      assert :ok = Runner.replay_one(challenge(input, :invalid_sexp))
    end

    assert {:error, {:ill_formed_term, _}} =
             Serialize.decode("(cure-core 2 (case (var 0) (type (finite (level-nf 0))) (branch Z -3 (var 0))))")
  end

  test "framing negatives remain separately inventoried without changing existing cells" do
    for input <- DecodeProbe.framing_samples() do
      assert {:error, _} = Serialize.decode(input)
      assert :ok = Runner.replay_one(challenge(input, :invalid_sexp))
    end

    assert DecodeProbe.cover_cells() == [{"serialize/decode", :valid_sexp}, {"serialize/decode", :invalid_sexp}]
  end
end
