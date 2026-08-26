defmodule Antigen.Generators.ConvPairTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.ConvPair
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}
  alias Cure.Core.Term

  @sample 500

  test "every sampled conv pair is well-formed and the oracle agrees with the kernel" do
    for %Challenge{} = c <- B.interp(ConvPair.gen()) |> Enum.take(@sample) do
      assert c.kind == :conv_pair
      assert c.assay == "conv/decision"
      assert c.label in [:convertible, :distinct]
      assert Term.term?(c.payload.t1) and Term.term?(c.payload.t2)

      assert Assays.Conv.run(c) == :ok,
             "conv oracle disagreed on #{inspect(c.payload)} — #{c.note}"
    end
  end

  test "the sample spans convertible and distinct verdicts and the key shapes" do
    sample = B.interp(ConvPair.gen()) |> Enum.take(@sample)
    notes = sample |> Enum.map(& &1.note) |> MapSet.new()

    assert Enum.any?(sample, &(&1.label == :convertible))
    assert Enum.any?(sample, &(&1.label == :distinct))

    # Σ projections/pairs are now ι-on-`:case` / `mk_pair` (D2); the note wording
    # tracks that (was nfst/nsnd/pair). The former :nprim rows are builtin-op
    # global spines compared by generic napp congruence (K2 §1.8).
    for frag <- [
          "first component",
          "second component",
          "builtin-op spine",
          "η",
          "mk_pair",
          "refl",
          "app-arg vint",
          "app-arg vλ"
        ] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing shape: #{frag}"
    end
  end
end
