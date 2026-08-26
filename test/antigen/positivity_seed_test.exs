defmodule Antigen.PositivitySeedTest do
  @moduledoc """
  Banks the W4 positivity escape-hatch antibodies (pre-port banking spec §4 W4)
  and guards that every banked positivity record replays to `:ok`. Idempotent
  via Corpus.append dedup. These three guard the deep-positivity kernel walk:
  if it ever regresses to the shallow pre-fix walk, through-constructor and
  sigma replay to {:wrongly_accepted, :Bad} and this goes red.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Positivity

  @corpus "test/antigen/corpus.sexp"

  @antibodies [
    Positivity.double_negation_family(),
    Positivity.sigma_negative_family(),
    Positivity.through_constructor_negative(),
    # S8: subject buried under app/lam-headed field types (strictly_positive?
    # catch-all). If the catch-all ever regresses to fail-open these replay to
    # {:wrongly_accepted, :Pgen} and this goes red.
    Positivity.app_head_negative(),
    Positivity.lam_head_negative()
  ]

  test "W4 positivity antibodies are banked and every positivity record replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    results = Runner.replay([@corpus], %{"positivity" => Assays.Positivity})

    pos =
      Enum.filter(results, fn r ->
        match?(%Antigen.Challenge{assay: "positivity"}, r.entry)
      end)

    assert length(pos) >= 5

    assert Enum.all?(pos, &(&1.verdict == :ok)),
           inspect(pos |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
