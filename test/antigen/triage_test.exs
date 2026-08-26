defmodule Antigen.TriageTest do
  use ExUnit.Case, async: true
  alias Antigen.{Triage, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}

  # bloated in BOTH dimensions: 3 defs (2 droppable) + an S-tower body to shrink
  defp both_dims_ch do
    tower = {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}]}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [d(:f, tower), d(:g, {:ctor, :Z, []}), d(:h, {:ctor, :Z, []})], focus: [:f]},
      seed: 1
    )
  end

  test "size/1 is kind-agnostic and counts pieces + list elements" do
    ch = both_dims_ch()
    assert Triage.size(ch) > 0
    # dropping a def strictly lowers size
    smaller = %{ch | payload: %{ch.payload | defs: tl(ch.payload.defs), focus: []}}
    assert Triage.size(smaller) < Triage.size(ch)
  end

  test "combined fixpoint reduces in BOTH bisect and shrink, reports stats" do
    ch = both_dims_ch()
    # synthetic same-shape predicate: a def_group whose :f-body is an S-tower over Z
    pred = fn c ->
      match?(%Challenge{kind: :def_group}, c) and
        Enum.any?(c.payload.defs, fn dd -> dd.name == :f and s_tower?(dd.body) end)
    end

    {out, stats} = Triage.minimize(ch, pred, 2000)
    assert pred.(out)
    # g and/or h dropped
    assert stats.bisect_drops >= 1
    # S-tower reduced
    assert stats.shrink_rewrites >= 1
    assert stats.min_size < stats.orig_size
    assert stats.orig_size == Triage.size(ch)
  end

  test "budget bound + determinism" do
    ch = both_dims_ch()
    pred = fn c -> match?(%Challenge{kind: :def_group}, c) end
    # tiny budget → partial but safe
    {a, _} = Triage.minimize(ch, pred, 3)
    {b, _} = Triage.minimize(ch, pred, 3)
    # deterministic
    assert a == b
  end

  test "safe_pred: a raising predicate is treated as no-progress, never crashes" do
    ch = both_dims_ch()
    {out, _stats} = Triage.minimize(ch, fn _ -> raise "boom" end, 100)
    # nothing accepted; original returned
    assert out == ch
  end

  test "elab_program is a triage no-op" do
    ch =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: 1, src: "module M do end"},
        seed: 1
      )

    {out, stats} = Triage.minimize(ch, fn _ -> true end, 100)
    assert out == ch
    assert stats.bisect_drops == 0 and stats.shrink_rewrites == 0
  end

  defp s_tower?({:ctor, :S, [n]}), do: s_tower?(n)
  defp s_tower?({:ctor, :Z, []}), do: true
  defp s_tower?(_), do: false
end
