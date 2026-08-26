defmodule Cure.Elab.PositivitySolverTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # These fixtures drive the SYNTAX-DIRECTED positivity solver — the second entry
  # in ProofSearch's ordered solver seam. It covers the arithmetic-sign fragment
  # that the shipped stdlib leaves UNTAGGED: `Std.Proof.Math.successor_is_positive`
  # (goal `IsPositive(S(n))`) and the two overlapping addition lemmas
  # `adding_a_positive_number_is_positive` / `adding_to_a_positive_number_is_positive`
  # (goal `IsPositive(plus(a, b))`). None of these carry `@lemma`, so the primary
  # tagged-lemma solver returns :none for their goals — the hole would survive and
  # block codegen. The positivity solver reaches them via VIRTUAL lemma entries
  # (built from the stdlib defs by name) fed to the same `try_lemma` machinery.
  #
  # The addition case is the reason the procedure is syntax-directed rather than a
  # tag pool: both add lemmas conclude `IsPositive(plus(a, b))`, so when both
  # summands are positive both apply. A naive lemma pool would see two distinct
  # proof terms and raise `:ambiguous_proof_search`. The positivity solver instead
  # tries the curated lemmas in a fixed order and takes the FIRST that discharges
  # — a deterministic decision, never an ambiguity.

  # A refinement whose proof obligation is `IsPositive(S(refined_value(value)))`.
  # `successor_is_positive` (untagged) is the ONLY thing that proves it.
  @successor """
  mod SuccessorPositivity
    use Std.Proof.Math
    use Std.Refine

    fn demo(value: PositiveNatural) -> PositiveNatural =
      refine(S(refined_value(value)), ?)
  end
  """

  # A refinement whose proof obligation is
  # `IsPositive(plus(refined_value(left), refined_value(right)))`. Both summands
  # are positive, so BOTH addition lemmas apply — the determinism test.
  @plus """
  mod PlusPositivity
    use Std.Proof.Math
    use Std.Refine

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(plus(refined_value(left), refined_value(right)), ?)
  end
  """

  test "IsPositive(S(n)) is discharged by the untagged successor lemma via positivity" do
    assert {:ok, env} = Program.elaborate(@successor)

    assert :ok = Program.check_codegen_ready(env),
           "the successor positivity rule must fill the hole so codegen is ready"
  end

  test "IsPositive(plus(a, b)) is discharged deterministically despite two applicable add lemmas" do
    assert {:ok, env} = Program.elaborate(@plus)
    # If the two overlapping add lemmas were pooled, this would be an
    # :ambiguous_proof_search decline and the hole would survive. A ready codegen
    # gate proves the solver picked one deterministically.
    assert :ok = Program.check_codegen_ready(env),
           "the addition positivity rule must discharge the hole with a single, ordered choice"
  end
end
