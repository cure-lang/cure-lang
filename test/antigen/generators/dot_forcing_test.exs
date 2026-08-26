defmodule Antigen.Generators.DotForcingTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.DotForcing
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays, Corpus}

  @sample 200

  test "every sampled dot-forcing probe's verdict agrees with the live elaborator/kernel" do
    for %Challenge{} = c <- B.interp(DotForcing.gen()) |> Enum.take(@sample) do
      assert c.kind == :dot_forcing
      assert c.label in [:accept, :reject, :unforced]

      assert Assays.DotForcing.run(c) == :ok,
             "verdict oracle disagreed on #{c.note} (#{c.label})"
    end
  end

  test "the case menu spans all three labels and every arm of the check" do
    labels = DotForcing.cases() |> Enum.map(fn t -> elem(t, 6) end) |> MapSet.new()
    assert MapSet.equal?(labels, MapSet.new([:accept, :reject, :unforced]))

    notes = DotForcing.cases() |> Enum.map(fn t -> elem(t, 7) end)

    for frag <- [
          "syntactic match",
          "convertible, non-syntactic",
          "rigid ctor clash",
          "distinct field var",
          "non-pinned field",
          "absent from telescope",
          "multi-index"
        ] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end

  test "every case round-trips through the corpus with its payload intact" do
    for {n, fam, c, idx, name, written, label, note} <- DotForcing.cases() do
      chal =
        Challenge.new(
          kind: :dot_forcing,
          assay: "forcing/dot",
          label: label,
          payload: %{ctx_vars: n, family: fam, cname: c, indices: idx, name: name, written: written},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.kind == :dot_forcing
      assert c2.label == label
      assert c2.payload == chal.payload
    end
  end
end
