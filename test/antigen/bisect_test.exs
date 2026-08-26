defmodule Antigen.BisectTest do
  use ExUnit.Case, async: true
  alias Antigen.{Bisect, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}

  defp def_group(names_bodies, focus) do
    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: Enum.map(names_bodies, fn {n, b} -> d(n, b) end), focus: focus},
      seed: 1
    )
  end

  test "candidates drop each def and prune its focus entry" do
    ch = def_group([{:f, {:global, :h}}, {:g, {:ctor, :Z, []}}, {:h, {:ctor, :Z, []}}], [:f, :h])
    cands = Bisect.candidates(ch)
    # 3 defs → 3 drop candidates
    assert length(cands) == 3
    # dropping :h removes it from defs AND from focus
    dropped_h = Enum.find(cands, fn c -> Enum.map(c.payload.defs, & &1.name) == [:f, :g] end)
    assert dropped_h.payload.focus == [:f]
  end

  test "dropping a def does NOT reindex/alter a surviving def's body term" do
    body_f = {:global, :h}
    ch = def_group([{:f, body_f}, {:g, {:ctor, :Z, []}}, {:h, {:ctor, :Z, []}}], [:f])

    drop_g =
      Enum.find(Bisect.candidates(ch), fn c ->
        Enum.map(c.payload.defs, & &1.name) == [:f, :h]
      end)

    surviving_f = Enum.find(drop_g.payload.defs, &(&1.name == :f))
    # byte-identical, no de-Bruijn shift
    assert surviving_f.body == body_f
  end

  test "family candidates drop each ctor" do
    fam = Cure.Core.Inductive.family(:F, [], [], 0)
    c0 = Cure.Core.Inductive.ctor(:A, [], [], [], [])
    c1 = Cure.Core.Inductive.ctor(:B, [], [], [], [])

    ch =
      Challenge.new(
        kind: :family,
        assay: "positivity",
        label: :well_typed,
        payload: %{family: fam, ctors: [c0, c1]},
        seed: 1
      )

    cands = Bisect.candidates(ch)
    assert length(cands) == 2
    assert Enum.any?(cands, fn c -> Enum.map(c.payload.ctors, & &1.name) == [:B] end)
  end

  test "kinds with no name-referenced list yield no candidates" do
    tt =
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: @nat, term: {:ctor, :Z, []}},
        seed: 1
      )

    assert Bisect.candidates(tt) == []
  end
end
