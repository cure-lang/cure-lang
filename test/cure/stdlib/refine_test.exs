defmodule Cure.Stdlib.RefineTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a refined value carries kernel-checked evidence" do
    source = """
    mod ProofBackedRefinement
      use Std.Proof.Math
      use Std.Refine

      type PositiveNatural = {value: Nat | IsPositive(value)}

      fn one() -> PositiveNatural = refine(S(Z), PositiveSuccessor())

      fn value_is_positive(value: PositiveNatural) -> IsPositive(refined_value(value)) =
        refinement_proof(value)

      fn multiply_positive_values(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
        refine(
          multiply(refined_value(left), refined_value(right)),
          multiplying_positive_numbers_is_positive(refinement_proof(left), refinement_proof(right))
        )

    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "a false refinement cannot be constructed without evidence" do
    source = """
    mod RejectedRefinement
      use Std.Proof.Math
      use Std.Refine

      type PositiveNatural = {value: Nat | IsPositive(value)}

      fn zero() -> PositiveNatural = refine(Z, PositiveSuccessor())
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "transitive proof imports and positive arithmetic preserve refinements" do
    source = """
    mod PositiveNaturalArithmetic
      use Std.Refine

      fn two() -> PositiveNatural = positive_natural_from_successor(S(Z))
      fn four_by_addition() -> PositiveNatural = add_positive_natural_numbers(two(), two())
      fn four_by_multiplication() -> PositiveNatural = multiply_positive_natural_numbers(two(), two())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end
end
