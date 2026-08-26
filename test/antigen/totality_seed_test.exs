defmodule Antigen.TotalitySeedTest do
  @moduledoc """
  Banks the W1 adversarial diverging antibodies (pre-port banking spec §4 W1) and
  guards that every banked totality record replays through the kernel to `:ok`.
  Idempotent: on a fresh checkout the committed records are already present, so
  `Corpus.append/3` dedups and writes nothing (keeping `mix test` git-clean).
  These five must keep replaying `:ok` FOREVER — including after the P1
  size-change port makes the certifier more permissive; that transition is the
  only moment they can go red, and catching it is their entire purpose.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Totality

  @corpus "test/antigen/corpus.sexp"

  @antibodies [
    Totality.diverging_three_cycle(),
    Totality.diverging_mediated_cycle(),
    Totality.diverging_permuting_pair(),
    Totality.diverging_regrowing_self(),
    Totality.diverging_one_leg_pair(),
    # premature-certification guard: an earlier mutual member must not be certified
    # while a sibling body is still a pending placeholder. Regresses to
    # {:wrongly_certified, [:f]} if the deferral is lost.
    Totality.diverging_pending_sibling()
  ]

  test "W1 diverging antibodies are banked and every totality record replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    reg = %{"totality/diverging" => Assays.Totality, "totality/terminating" => Assays.Totality}
    results = Runner.replay([@corpus], reg)

    tot =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "totality/" <> _}, r.entry)
      end)

    # the pre-existing mutual-pair antibody + the five W1 records + pending-sibling
    assert length(tot) >= 7

    assert Enum.all?(tot, &(&1.verdict == :ok)),
           "totality replay produced a non-:ok verdict: " <>
             inspect(tot |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
