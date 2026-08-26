defmodule Antigen.RewriteSeedTest do
  @moduledoc """
  Banks the rewrite/eq vertical's permanent seed store (spec §7) and guards that
  every banked record replays through the kernel to `:ok`. Idempotent: on a fresh
  checkout the committed records are already present, so `Corpus.append/3` finds
  them via its `seen?` dedup and writes nothing (keeping `mix test` git-clean).
  Run in isolation first to generate the file, then commit it.

  Every rewrite/eq obligation is correctly handled by the kernel (the
  `:left_at_source` transport probe is properly rejected — no soundness hole), so
  the vertical banks known-good seeds only, with no antibodies.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Rewrite

  @seeds "test/antigen/seeds.sexp"

  @variants [
    {:eq_formation, [:well_typed, :ill_typed]},
    {:refl_typing, [:base, :redex, :conjunct1_violation, :conjunct2_violation]},
    {:rewrite_premise, [:well_typed, :proof_not_eq, :body_mismatch]},
    {:transport_type, [:transport_correct, :refl_coherence, :left_at_source]}
  ]

  test "every rewrite/eq obligation is correctly handled and its seed replays :ok" do
    challenges = for {f, vs} <- @variants, v <- vs, do: apply(Rewrite, f, [v])

    for c <- challenges do
      assert :ok == Assays.Rewrite.run(c),
             "assay must be :ok on correctly-labelled #{c.note}"

      Corpus.append(@seeds, c, Corpus.dedup_key(c, :seed))
    end

    reg = %{"rewrite/eq" => Assays.Rewrite}
    results = Runner.replay([@seeds], reg)

    rewrites = Enum.filter(results, fn r -> match?(%Antigen.Challenge{assay: "rewrite/eq"}, r.entry) end)
    refute rewrites == []

    assert Enum.all?(rewrites, fn r -> r.verdict == :ok end),
           "rewrite/eq replay produced a non-:ok verdict: " <>
             inspect(rewrites |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
