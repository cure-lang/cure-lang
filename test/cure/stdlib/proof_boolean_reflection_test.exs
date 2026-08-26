defmodule Cure.Stdlib.ProofBooleanReflectionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @moduletag :stdlib

  # A client module that USES each connective lemma, so the whole file only
  # elaborates if every signature and proof term kernel-checks.
  @client """
  mod BooleanReflectionClient
    use Std.Bool
    use Std.Decision
    use Std.Proof.IntMath
    use Std.Proof.BooleanReflection

    fn split_left(both: IsTrue(`and`(True(), True()))) -> IsTrue(True()) =
      left_operand_is_true_from_true_conjunction(True(), True(), both)

    fn split_right(both: IsTrue(`and`(True(), True()))) -> IsTrue(True()) =
      right_operand_is_true_from_true_conjunction(True(), True(), both)

    fn combine(l: IsTrue(True()), r: IsTrue(True())) -> IsTrue(`and`(True(), True())) =
      conjunction_is_true_when_both_operands_are(l, r)

    fn from_left(l: IsTrue(True())) -> IsTrue(`or`(True(), False())) =
      disjunction_is_true_from_left_operand(False(), l)

    fn from_right(r: IsTrue(True())) -> IsTrue(`or`(False(), True())) =
      disjunction_is_true_from_right_operand(False(), r)

    fn contradiction(neg: IsTrue(`not`(True())), pos: IsTrue(True())) -> Empty =
      true_negation_contradicts_truth(True(), neg, pos)
  end
  """

  test "the boolean-connective algebra elaborates and every lemma kernel-checks" do
    assert {:ok, _env} = Program.elaborate(@client)
  end
end
