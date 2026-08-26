defmodule Cure.Stdlib.LinearArithmeticComputeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Emit, Program}

  @source """
  mod LiaComputeRuntime
    use Std.Nat
    use Std.Int
    use Std.Proof.LinearArithmetic

    fn zero() -> Int = FromNat(Z())
    fn neg_one() -> Int = NegativeSuccessor(Z())
    fn neg_two() -> Int = NegativeSuccessor(S(Z()))
    fn neg_three() -> Int = NegativeSuccessor(S(S(Z())))
    fn one() -> Int = FromNat(S(Z()))
    fn two() -> Int = FromNat(S(S(Z())))
    fn three() -> Int = FromNat(S(S(S(Z()))))

    fn a_nonnegative() -> LinearAtom = LinearAtom{coefficients: [neg_one(), zero()], constant: zero(), relation: LessOrEqual()}
    fn b_nonnegative() -> LinearAtom = LinearAtom{coefficients: [zero(), neg_one()], constant: zero(), relation: LessOrEqual()}
    fn goal() -> LinearAtom = LinearAtom{coefficients: [neg_two(), neg_three()], constant: zero(), relation: LessOrEqual()}

    fn accepted() -> Bool = check_lia_candidate([a_nonnegative(), b_nonnegative()], goal(), [S(S(Z())), S(S(S(Z()))), S(Z())])
    fn forged() -> Bool = check_lia_candidate([a_nonnegative(), b_nonnegative()], goal(), [S(Z()), S(Z()), S(Z())])
    fn short_witness() -> Bool = check_lia_candidate([a_nonnegative(), b_nonnegative()], goal(), [S(S(Z())), S(S(S(Z())))])
    fn wrong_dimension() -> Bool = check_lia_candidate([LinearAtom{coefficients: [neg_one()], constant: zero(), relation: LessOrEqual()}], goal(), [S(Z()), S(Z())])
    fn short_valuation() -> Option(Bool) = evaluate_atom_checked(goal(), [one()])
    fn valid_evaluation() -> Option(Bool) = evaluate_atom_checked(a_nonnegative(), [two(), three()])

    ## 2n=1 is an integer-only inconsistency. This rejects one candidate and
    ## deliberately does not assert completeness of finite certificate search.
    fn boundary_sample() -> Bool = check_lia_candidate([
      LinearAtom{coefficients: [two()], constant: one(), relation: LessOrEqual()},
      LinearAtom{coefficients: [neg_two()], constant: neg_one(), relation: LessOrEqual()}
    ], LinearAtom{coefficients: [zero()], constant: neg_one(), relation: LessOrEqual()}, [S(Z()), S(Z()), S(Z())])
  end
  """

  test "candidate checker accepts the Farkas witness and rejects forged/malformed inputs" do
    assert {:ok, env} = Program.elaborate(@source)

    roots = [
      :accepted,
      :forged,
      :short_witness,
      :wrong_dimension,
      :short_valuation,
      :valid_evaluation,
      :boundary_sample
    ]

    functions = Program.reachable_def_names(env, roots)
    assert {:ok, module} = Emit.compile_and_load(env, module: :"Cure.LiaComputeRuntime", functions: functions)

    assert apply(module, :accepted, []) == true
    assert apply(module, :forged, []) == false
    assert apply(module, :short_witness, []) == false
    assert apply(module, :wrong_dimension, []) == false
    assert apply(module, :short_valuation, []) == :none
    assert apply(module, :valid_evaluation, []) == {:some, true}
    assert apply(module, :boundary_sample, []) == false
  end
end
