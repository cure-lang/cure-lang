defmodule Antigen.ReachPinTest do
  @moduledoc """
  Banks + replays `test/antigen/reach.sexp` (pre-port banking spec D2): challenges
  whose ground-truth label the checker does not yet achieve. Each entry's replay
  is pinned to its DOCUMENTED current violation, so drift in EITHER direction is
  loud: an accidental acceptance (permissiveness appearing without P1) and an
  accidental new rejection shape both fail this test.

  MIGRATION CONTRACT (spec D2): the port run that achieves an entry (P1 for all
  initial entries) appends the byte-identical record line to corpus.sexp, removes
  it here, and deletes the matching pin below — in the same commit. Records are
  never edited in place.

  ALL initial reach pins have now been ACHIEVED and migrated to corpus.sexp:
  `wellfounded_ackermann` by #14 (single-function size-change + reconstruct-equal),
  and the two MUTUAL pins (`wellfounded_even_odd`, `wellfounded_permuted_pair`) by
  #13 (cross-function / mutual size-change). `reach.sexp` is therefore empty and
  `@pins` is `[]`; new reach pins (checker not-yet-achieving a labelled truth) get
  added here, banked to `reach.sexp`, and pinned to their current violation.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Assays}

  @reach "test/antigen/reach.sexp"

  # No outstanding reach pins (all migrated to corpus.sexp — see moduledoc).
  @pins []

  # keyed by focus — the pinned CURRENT verdict for each banked entry. Add
  # entries to the map literal below.
  @spec expected_verdicts() :: map()
  defp expected_verdicts, do: %{}

  # The map flows in as an untyped param so the 1.20 checker sees term(), not
  # the empty-map singleton it would fold `expected_verdicts()` to — otherwise
  # Map.fetch!/2 in the currently-dead (pins empty) replay loop is flagged as
  # always-raising. Missing key still raises at runtime (drift detection).
  defp pinned_verdict!(pins, focus), do: Map.fetch!(pins, focus)

  test "reach pins are banked and replay to their documented conservative rejection" do
    for c <- @pins, do: Corpus.append(@reach, c, Corpus.dedup_key(c, :antibody))

    decoded =
      if File.exists?(@reach),
        do: @reach |> Corpus.stream() |> Enum.map(fn {:ok, c} -> c end),
        else: []

    assert length(decoded) == map_size(expected_verdicts())

    for c <- decoded do
      assert Assays.Totality.run(c) == pinned_verdict!(expected_verdicts(), c.payload.focus),
             "reach pin #{inspect(c.payload.focus)} drifted from its pinned verdict"
    end
  end
end
