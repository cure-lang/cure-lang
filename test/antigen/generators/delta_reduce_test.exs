defmodule Antigen.Generators.DeltaReduceTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.DeltaReduce
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays, Corpus}

  @sample 200

  test "every sampled probe (reduces/fuel_probe/opts_reject) agrees with the live kernel" do
    for %Challenge{} = c <- B.interp(DeltaReduce.gen()) |> Enum.take(@sample) do
      assert c.kind == :delta_reduce
      assert c.label in [:reduces, :fuel_probe, :opts_reject]

      assert Assays.DeltaReduce.run(c) == :ok,
             "oracle disagreed on #{c.note}"
    end
  end

  test "the menu spans both δ+β application unfolds and δ+ι projection unfolds" do
    notes = DeltaReduce.cases() |> Enum.map(fn t -> elem(t, 2) end)
    # Projection arms now emit inductive ι-on-case (mk_pair) rather than the retired
    # primitive nfst/nsnd (D2); the menu still spans both projections + nested.
    for frag <- ["δ+β", "project first", "project second", "nested"] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end

  test "every :reduces case round-trips through the corpus with its payload intact" do
    for {term, expected, note} <- DeltaReduce.cases() do
      chal =
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :reduces,
          payload: %{term: term, expected: expected},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.kind == :delta_reduce
      assert c2.payload == chal.payload
    end
  end

  test "every fuel_probe case round-trips through the corpus with its payload intact" do
    for {term, opts, want, expected, note} <- DeltaReduce.fuel_cases() do
      chal =
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :fuel_probe,
          payload: %{term: term, expected: expected, opts: opts, want: want},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.kind == :delta_reduce
      assert c2.label == :fuel_probe
      assert c2.payload == chal.payload
    end
  end

  test "every opts_reject case round-trips through the corpus with its payload intact" do
    for {opts, note} <- DeltaReduce.opts_reject_cases() do
      chal =
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :opts_reject,
          payload: %{opts: opts},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.kind == :delta_reduce
      assert c2.label == :opts_reject
      assert c2.payload == chal.payload
    end
  end
end
