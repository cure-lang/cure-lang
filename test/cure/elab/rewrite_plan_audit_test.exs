defmodule Cure.Elab.RewritePlanAuditTest do
  @moduledoc """
  Behavioral deltas found auditing `Cure.Elab.Elaborator.rewrite_plan/5` and its
  helpers (`motive_for/3`, `abstract_term/3`) against Idris' `elabRewrite`
  (`reference/idris2/src/TTImp/Elab/Rewrite.idr`) — transliteration P0, Task 5.

  Audit outcome (see the closing report for full traces):

    * Candidate 1 (error vocabulary): NO DELTA. Cure already distinguishes
      `:rewrite_proof_not_equality` (≈ Idris `NotRewriteRule`, from `eq_parts/1`)
      from `{:rewrite_no_match, ...}` (≈ `RewriteNoChange`, from `rewrite_plan/5`).
      Guarded below so the parity claim is regression-checked.

    * Candidate 3 (motive abstraction under a `:case` binder): REAL, in-scope bug
      in `abstract_term/3`. The generic tuple clause recursed into `:case` branch
      bodies at the same `depth` as the scrutinee, so a branch that binds `arity`
      de Bruijn variables had those branch-bound variables spuriously shifted by
      the `{:var, i} when i >= depth` clause, corrupting the synthesised motive
      (kernel then rejects with `:rewrite_premise`/`:ctor_arity`). Fixed by adding
      an explicit `:case` clause mirroring `Cure.Core.Term.shift/3` (abstract each
      branch body at `depth + arity`). Red-green test below.

  A stuck `:case` term reaches `abstract_term/3` because `Kernel.normalize`
  preserves neutral `case`s: a certified-total recursive function (`plus`) applied
  to a neutral argument (`k`) normalizes to a live `{:case, scrut, motive,
  branches}`, whose `S` branch binds one variable.

  Candidates 2 (occurrence-up-to-conversion, rw07) and the corpus probe
  rw04_plus_comm are NOT closed here: both require changes outside the
  `rewrite_plan/5..abstract_term/3` region (Task 5 scope guard / HARD STOP) and
  are reported to the orchestrator. This suite asserts only the in-scope,
  charter-D2-local fix.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @nat "type Nat = Z | S(Nat)"
  @plus """
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
  """

  # Candidate 1 — parity guard (no delta). A non-equality rewrite proof and a
  # rewrite that changes nothing must classify as *different* error families,
  # exactly as Idris separates `NotRewriteRule` from `RewriteNoChange`.
  test "a non-equality rewrite proof is a distinct error family from a no-op rewrite" do
    non_eq = "mod M\n  #{@nat}\n  fn f(n: Nat, m: Nat) -> Equivalent(Nat, m, m) = rewrite n in reflexive(m)\nend\n"

    no_change =
      "mod M\n  #{@nat}\n  fn g(p: Equivalent(Nat, Z, Z), m: Nat) -> Equivalent(Nat, m, m) = rewrite p in reflexive(m)\nend\n"

    assert {:error, e1} = Program.elaborate(non_eq)
    assert {:error, e2} = Program.elaborate(no_change)
    assert error_tag(Program.semantic_error(e1)) == :rewrite_proof_not_equality
    assert error_tag(Program.semantic_error(e2)) == :rewrite_no_match
    refute error_tag(Program.semantic_error(e1)) == error_tag(Program.semantic_error(e2))
  end

  # Candidate 3 — in-scope fix (red-green). The rewrite goal reifies a stuck
  # `:case` (the neutral `plus k n`) whose `S` branch binds one variable; the
  # motive synthesised by `abstract_term/3` must keep that branch-bound variable
  # intact. Before the fix the corrupted motive was rejected by the kernel; after
  # the fix it type-checks. The `refl` value `S(S(plus(k, n)))` is the post-rewrite
  # common value (Cure's `rewrite`, when the goal contains the proof's left
  # endpoint, checks the body under the goal with that endpoint replaced by the
  # right endpoint — mirrored by the working `plus_zero_right` probe).
  test "motive abstraction descends correctly under a :case branch binder" do
    src =
      "mod M\n  #{@nat}\n#{@plus}\n" <>
        "  fn plus_succ_right(m: Nat, n: Nat) -> Equivalent(Nat, plus(m, S(n)), S(plus(m, n))) = match m\n" <>
        "    Z() -> reflexive(S(n))\n" <>
        "    S(k) -> rewrite plus_succ_right(k, n) in reflexive(S(S(plus(k, n))))\n" <>
        "end\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  # Candidate 2 — bridge-lemma rewrite step (rw07, red-green). The proof
  # `plus_zero_right(n) : Equivalent(Nat, plus(n, Z), n)` has left endpoint `plus(n, Z)`,
  # which does NOT appear syntactically in the goal
  # `Equivalent(Nat, plus(plus(Z, n), Z), n)`: the trusted normalizer freezes the goal's
  # LHS as a stuck `case` whose scrutinee is the UNREDUCED `plus(Z, n)` (never
  # δ-reduced to `n`), so the syntactic occurrence match misses. Idris matches up
  # to conversion and accepts.
  #
  # Fix (elaborator only, no TCB change): the reducible sub-occurrence `plus(Z, n)`
  # normalizes to `n` at top level, and replacing it by `n` in the goal exposes
  # `plus(n, Z)`. Synthesize an inline refl-bodied bridge proof
  # `Equivalent(Nat, n, plus(Z, n))` (checked, not the blocked scrutinee conversion) and
  # emit it as an OUTER rewrite wrapping the original, whose residual goal
  # `Equivalent(Nat, plus(n, Z), n)` is exactly the rw01 pattern. Every conversion the
  # kernel then sees is either top-level-decidable or structurally identical.
  test "bridge-lemma rewrite closes a definitional (non-syntactic) occurrence (rw07)" do
    src =
      "mod M\n  #{@nat}\n#{@plus}\n" <>
        "  fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n\n" <>
        "    Z() -> reflexive(Z)\n" <>
        "    S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))\n" <>
        "  fn conv_occurrence(n: Nat) -> Equivalent(Nat, plus(plus(Z, n), Z), n) = rewrite plus_zero_right(n) in reflexive(n)\n" <>
        "end\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  defp error_tag(err) when is_atom(err), do: err
  defp error_tag(err) when is_tuple(err), do: elem(err, 0)
end
