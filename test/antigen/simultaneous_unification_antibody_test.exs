defmodule Antigen.SimultaneousUnificationAntibodyTest do
  @moduledoc """
  E-layer antibody (E6-residual — the deferred simultaneous-unification refactor,
  spec `2026-07-02-idris-parity-roadmap.md` §2). A constructor whose result carries
  a COMPUTED index (`ATimes : ... -> Acc(PTimes(l, r), add(m1, m2))`) is applied
  INLINE at a goal that also carries an IMPLICIT the present arguments determine.
  Position 0 of the index (the `PTimes` spine) fixes the implicit structurally;
  position 1 (`add m1 m2`) stays STUCK until the present fields pin `m1`, `m2`.

  Cure previously solved the deferred domain by all-or-nothing unification of the
  ctor result template against the goal, so the stuck computed component aborted the
  whole unify and the sibling implicit never solved → spurious
  `:unsolved_metavariables`. The fix (`unify_data_components`) unifies the data
  template COMPONENT-WISE, tolerating a stuck component so the determined parts
  solve; present-field elaboration then pins the stuck measure and its deferred
  equation retries.

  The oracle probes `e6simuni01`/`e6simuni02` pin the ACCEPT/REJECT directions
  against Idris. This antibody pins that the component-wise TOLERANCE is SOUND — it
  makes progress possible without making an unsound program typecheck:

    * REACH — the computed-index ctor at an implicit goal is accepted: the implicit
      `a` solves from position 0 while the measure `add(m1, m2)` is tolerated stuck,
      then satisfied once `m1`, `m2` are pinned.

    * CONTROL measure-checked — the tolerated component is NOT discarded. With both
      present arguments forcing a CONCRETE measure `add(S(Z), S(Z)) = S(S(Z))`
      against a goal measure `S(Z)`, index unification rejects the mismatch. A
      component tolerated as stuck is still fully checked once determined.

    * CONTROL no-fabrication — tolerance solves only what is DETERMINED. A goal
      whose implicit `a` appears in NO index position (every index concrete) leaves
      `a` genuinely underdetermined; the component-wise unify must reject with an
      unsolved metavariable rather than inventing a value.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Shared: Nat measure `add`, patterns, and the computed-index family `Acc`.
  defp defs do
    """
      type Tag = TA | TB
      fn add(m: Nat, n: Nat) -> Nat = match m
        Z()  -> n
        S(k) -> S(add(k, n))
      type Pat = PA(Tag) | PStar(Pat) | PTimes(Pat, Pat)
      type Acc indices (p: Pat, n: Nat)
        AAtomA : Acc(PA(TA), S(Z))
        AStar  : Acc(PStar(q), Z)
        ATimes : Acc(l, m1) -> Acc(r, m2) -> Acc(PTimes(l, r), add(m1, m2))
    """
  end

  # REACH: implicit `a` solved from position 0; measure tolerated stuck, then met.
  defp reach_src do
    "mod SimUniReach\n" <>
      defs() <>
      "  fn star_fold({a: Tag}, x: Acc(PTimes(PA(a), PStar(PA(a))), S(Z))) -> Unit = unit()\n" <>
      "  fn use() -> Unit = star_fold(ATimes(AAtomA(), AStar()))\nend\n"
  end

  test "REACH: computed-index ctor at an implicit goal elaborates" do
    assert {:ok, _} = Program.elaborate(reach_src())
  end

  # REACH: the same constructor at a fully concrete goal exercises the checked
  # application path's reification of the callee domain. Reification flattens a
  # data family's params and indices, so that boundary must restore the split
  # before bidirectional constructor elaboration compares result and goal.
  defp concrete_goal_src do
    "mod SimUniConcreteGoal\n" <>
      defs() <>
      "  fn star_fold(x: Acc(PTimes(PA(TA), PStar(PA(TA))), S(Z))) -> Unit = unit()\n" <>
      "  fn use() -> Unit = star_fold(ATimes(AAtomA(), AStar()))\nend\n"
  end

  test "REACH: computed-index ctor at a concrete goal preserves the data index split" do
    assert {:ok, _} = Program.elaborate(concrete_goal_src())
  end

  # CONTROL: concrete measure `S(S(Z))` vs goal `S(Z)` — the tolerated component is
  # still checked, so index unification rejects the mismatch.
  defp measure_src do
    "mod SimUniMeasure\n" <>
      defs() <>
      "  fn star_fold({a: Tag}, x: Acc(PTimes(PA(a), PA(a)), S(Z))) -> Unit = unit()\n" <>
      "  fn use() -> Unit = star_fold(ATimes(AAtomA(), AAtomA()))\nend\n"
  end

  test "CONTROL measure-checked: a tolerated-then-determined measure mismatch is rejected" do
    assert {:error, {:source_context, {:index_mismatch, _}, _}} = Program.elaborate(measure_src())
  end

  # CONTROL: `a` occurs in no index position (all indices concrete) — underdetermined.
  defp unsolvable_src do
    "mod SimUniUnsolv\n" <>
      defs() <>
      "  fn star_fold({a: Tag}, x: Acc(PTimes(PA(TA), PStar(PA(TA))), S(Z))) -> Unit = unit()\n" <>
      "  fn use() -> Unit = star_fold(ATimes(AAtomA(), AStar()))\nend\n"
  end

  test "CONTROL no-fabrication: an underdetermined implicit rejects, not fabricated" do
    assert {:error, {:source_context, {:unsolved_metavariables, _}, _}} = Program.elaborate(unsolvable_src())
  end
end
