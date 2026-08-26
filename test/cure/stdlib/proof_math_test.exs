defmodule Cure.Stdlib.ProofMathTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "positive multiplication is proved by reusable Cure evidence" do
    source = """
    mod ProofMathConsumer
      use Std.Proof.Math

      fn two_is_positive() -> IsPositive(S(S(Z))) = PositiveSuccessor()

      fn four_is_positive() -> IsPositive(multiply(S(S(Z)), S(S(Z)))) =
        multiplying_positive_numbers_is_positive(two_is_positive(), two_is_positive())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "positivity decisions carry checked evidence" do
    source = """
    mod ProofMathDecisionConsumer
      use Std.Proof.Math
      use Std.Decision

      fn successor_is_positive(natural: Nat) -> IsPositive(S(natural)) =
        match decide_is_positive(S(natural))
          Yes(proof) -> proof
          No(disproof) -> match disproof(PositiveSuccessor())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "less-than-or-equal proofs compose transitively" do
    source = """
    mod ProofMathOrderConsumer
      use Std.Proof.Math

      fn compose(
        {left: Nat},
        {middle: Nat},
        {right: Nat},
        first: IsLessThanOrEqual(left, middle),
        second: IsLessThanOrEqual(middle, right)
      ) -> IsLessThanOrEqual(left, right) =
        less_than_or_equal_is_transitive(first, second)
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "natural-number order decisions and preservation carry evidence" do
    source = """
    mod ProofMathOrderBattery
      use Std.Proof.Math
      use Std.Decision

      fn two_is_at_most_three() -> Decision(IsLessThanOrEqual(S(S(Z)), S(S(S(Z))))) =
        decide_is_less_than_or_equal(S(S(Z)), S(S(S(Z))))

      fn three_is_not_less_than_two() -> Decision(IsLessThan(S(S(S(Z))), S(S(Z)))) =
        decide_is_less_than(S(S(S(Z))), S(S(Z)))

      fn zero_is_less_than_one() -> IsLessThan(Z, S(Z)) = ZeroIsLessThanSuccessor()

      fn shifted_strict_order() -> IsLessThan(S(S(Z)), S(S(S(Z)))) =
        adding_the_same_number_preserves_less_than(S(S(Z)), zero_is_less_than_one())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "boolean-valued Nat comparisons reduce correctly" do
    source = """
    mod NatComparisonClient
      use Std.Bool
      use Std.Nat
      use Std.Proof.IntMath
      use Std.Proof.Math

      # Confirmed() only type-checks if each comparison reduces to True().
      fn lte_true() -> IsTrue(natural_is_less_than_or_equal(S(Z()), S(S(Z())))) = Confirmed()
      fn lt_true() -> IsTrue(natural_is_less_than(S(Z()), S(S(Z())))) = Confirmed()
      fn positive_true() -> IsTrue(natural_is_positive(S(Z()))) = Confirmed()
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "Nat reflection lemmas round-trip between boolean and inductive forms" do
    source = """
    mod NatReflectionClient
      use Std.Bool
      use Std.Nat
      use Std.Proof.IntMath
      use Std.Proof.Math

      # 1 < 2 obtained through the boolean surface, then reflected back.
      fn lt_from_bool() -> IsLessThan(S(Z()), S(S(Z()))) =
        less_than_holds_when_boolean_comparison_is_true(S(Z()), S(S(Z())), Confirmed())

      fn bool_from_lt(proof: IsLessThan(S(Z()), S(S(Z())))) -> IsTrue(natural_is_less_than(S(Z()), S(S(Z())))) =
        boolean_comparison_is_true_when_less_than_holds(proof)

      fn positive_from_bool() -> IsPositive(S(Z())) =
        positive_holds_when_boolean_comparison_is_true(S(Z()), Confirmed())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end
end
