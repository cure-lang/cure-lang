defmodule Cure.Elab.IntOrderTotalityTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.{Program, TotalityClosure}

  @proofs [
    :add_int_commutative_from_nat,
    :add_int_commutative_negative_successor,
    :add_int_associative_from_nat,
    :add_int_associative_negative_successor,
    :add_int_commutative,
    :add_int_left_succ,
    :add_int_left_pred,
    :add_int_associative,
    :add_int_rearrange_four,
    :scale_nat_int_distributes_over_add,
    :add_int_left_inverse,
    :scale_nat_int_add_scalars,
    :add_int_right_inverse_is_unique,
    :negate_distributes_over_add,
    :add_value_to_negated_successor_scale,
    :multiply_int_successor_coefficient,
    :multiply_int_predecessor_coefficient,
    :multiply_int_distributes_over_from_nat_add,
    :multiply_int_distributes_over_negative_add,
    :multiply_int_distributes_over_coefficient_add,
    :multiply_int_scale_nat_coefficient,
    :add_int_is_monotone_first,
    :add_int_is_monotone_both,
    :adding_preserves_less_than_or_equal,
    :scale_nat_int_is_monotone
  ]

  test "structural Nat helper proofs and their full dependent cone certify through the ordinary checker" do
    path = Path.expand("../../../lib/std/proof_int_order.cure", __DIR__)
    assert {:ok, env} = Program.elaborate(File.read!(path), file: path)

    names = Enum.map(@proofs, &Cure.Elab.Name.qualify("Std.Proof.IntOrder", &1))

    for name <- names do
      assert :ok = Kernel.check_def(env, name)
      assert Env.total?(env, name), "uncertified arithmetic proof: #{name}"
    end

    assert {:ok, certified} = TotalityClosure.certify_roots(env, names)
    assert Enum.all?(names, &Env.total?(certified, &1))
  end

  test "the refactor does not certify nondecreasing recursion or alter runtime partiality" do
    assert {:ok, env} =
             Program.elaborate("""
             mod IntOrderPartialControl
               fn loop(n: Int) -> Int = loop(n)
             end
             """)

    refute Env.total?(env, :"IntOrderPartialControl#loop")

    assert {:error, {:compile_time_totality, _, _}} =
             TotalityClosure.certify_roots(env, [:"IntOrderPartialControl#loop"])
  end
end
