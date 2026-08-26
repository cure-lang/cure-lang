defmodule Antigen.Generators.CheckModeTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.CheckMode
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays, Corpus}

  @sample 200

  test "every sampled check-mode probe's verdict agrees with the live kernel" do
    for %Challenge{} = c <- B.interp(CheckMode.gen()) |> Enum.take(@sample) do
      assert c.kind == :check_mode
      assert c.label in [:accept, :reject]

      assert Assays.CheckMode.run(c) == :ok,
             "verdict oracle disagreed on #{c.note} (#{c.label})"
    end
  end

  test "the menu spans both verdicts and each checking-mode arm" do
    labels = CheckMode.cases() |> Enum.map(fn t -> elem(t, 3) end) |> MapSet.new()
    assert MapSet.equal?(labels, MapSet.new([:accept, :reject]))

    notes = CheckMode.cases() |> Enum.map(fn t -> elem(t, 4) end)

    for frag <- ["parameter-bearing ctor", "hole", "Σ-introduction", "sigma_mismatch", "index_mismatch"] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end

  test "every case round-trips through the corpus with its payload intact" do
    for {n, term, ty, label, note} <- CheckMode.cases() do
      chal =
        Challenge.new(
          kind: :check_mode,
          assay: "check/verdict",
          label: label,
          payload: %{ctx_vars: n, term: term, type: ty},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.kind == :check_mode
      assert c2.label == label
      assert c2.payload == chal.payload
    end
  end
end
