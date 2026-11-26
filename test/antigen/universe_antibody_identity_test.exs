defmodule Antigen.UniverseAntibodyIdentityTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.Sort

  defp key(challenge), do: Corpus.dedup_key(challenge, :antibody)

  defp probe(input),
    do: Challenge.new(kind: :decode_probe, assay: "serialize/decode", label: :invalid_sexp, payload: %{input: input})

  test "antibody generation changes without changing record framing or seed identity" do
    challenge = Challenge.stub({:type, Sort.finite_closed(0)})
    assert Corpus.format_version() == 2
    assert Corpus.antibody_version() == 3
    assert key(challenge) =~ "|antibody/3|"

    assert Corpus.dedup_key(challenge, :seed) ==
             "antigen/2|#{Corpus.universe_epoch()}|" <> Antigen.Coverage.key_string(Antigen.Coverage.key(challenge))
  end

  test "actual pending-sibling setup/target differs from the full mutual-pair guard" do
    pending = Antigen.Generators.Totality.diverging_pending_sibling()
    mutual = Antigen.Generators.Totality.diverging_mutual_pair()
    assert elem(Challenge.to_pieces(pending), 1) == elem(Challenge.to_pieces(mutual), 1)
    refute elem(Challenge.to_pieces(pending), 0) == elem(Challenge.to_pieces(mutual), 0)
    refute key(pending) == key(mutual)
    assert :ok = Antigen.Assays.Totality.run(pending)
    assert :ok = Antigen.Assays.Totality.run(mutual)
  end

  test "zero-piece decoder inputs and recipes have distinct semantic identities" do
    refute key(probe("(zzz)")) == key(probe("(var -1)"))
    a = Challenge.new(kind: :kernel_probe, assay: "kernel/probe", label: :probe, payload: %{probe: :infer_absurd})
    b = %{a | payload: %{probe: :check_ctor_arity}}
    refute key(a) == key(b)
    assert {_, []} = Challenge.to_pieces(a)
    assert {_, []} = Challenge.to_pieces(b)
  end

  test "only top-level seed, note and cover_tag are excluded" do
    challenge = probe("(zzz)")
    assert key(challenge) == key(%{challenge | seed: 42, note: "capture", cover_tag: :invalid_sexp})
    refute key(challenge) == key(%{challenge | label: :valid_sexp})
    refute key(challenge) == key(%{challenge | assay: "different/assay"})
  end

  test "semantic setup preserves atom/string and tuple/list distinctions" do
    challenge = Challenge.new(kind: :delta_reduce, assay: "delta/nf", label: :opts_reject, payload: %{opts: [fuel: 1]})

    for opts <- [[{"fuel", 1}], [["fuel", 1]], [fuel: 2]] do
      refute key(challenge) == key(%{challenge | payload: %{opts: opts}})
    end
  end

  test "contexts, fault metadata and Core pieces contribute independently" do
    fault = %{kind: :head_swap, witness: :head, expected_head: :Nat, injected_head: :Bd, scope: nil}

    base =
      Challenge.new(
        kind: :mutant_term,
        assay: "mutation/rejection",
        label: :ill_typed,
        payload: %{sig: :v1, ctx: [], type: {:data, :Nat, [], []}, term: {:ctor, :T, []}, fault: fault}
      )

    refute key(base) == key(%{base | payload: %{base.payload | ctx: [{:data, :Bd, [], []}]}})
    refute key(base) == key(%{base | payload: %{base.payload | fault: Map.put(fault, :depth, 1)}})
    refute key(base) == key(%{base | payload: %{base.payload | term: {:ctor, :F, []}}})
    assert {:ok, decoded} = Corpus.decode_record(Corpus.encode_record(base))
    assert key(base) == key(decoded)
  end
end
