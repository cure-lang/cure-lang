defmodule Cure.Core.IntFoldTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "int_to_ctor_if peels a nonneg compact Int to FromNat" do
    assert Eval.int_to_ctor_if({:vint, 3}) == {:vctor, :FromNat, [{:vnat, 3}]}
    assert Eval.int_to_ctor_if({:vint, 0}) == {:vctor, :FromNat, [{:vnat, 0}]}
  end

  test "int_to_ctor_if peels a negative compact Int to NegativeSuccessor" do
    assert Eval.int_to_ctor_if({:vint, -1}) == {:vctor, :NegativeSuccessor, [{:vnat, 0}]}
    assert Eval.int_to_ctor_if({:vint, -4}) == {:vctor, :NegativeSuccessor, [{:vnat, 3}]}
  end

  test "int_to_ctor_if passes non-Int values through unchanged" do
    assert Eval.int_to_ctor_if({:vnat, 2}) == {:vnat, 2}
    assert Eval.int_to_ctor_if({:vneutral, {:nvar, 0}}) == {:vneutral, {:nvar, 0}}
  end

  test "case on a compact Int selects the matching constructor arm" do
    # case {:vint, 5} of FromNat(n) -> n | NegativeSuccessor(n) -> n
    # (body {:var,0} returns the bound field)
    branches = [{:FromNat, 1, {:var, 0}}, {:NegativeSuccessor, 1, {:var, 0}}]
    scrut = {:int_lit, 5}
    assert Eval.eval({:case, scrut, {:var, 0}, branches}, []) == {:vnat, 5}

    scrut_neg = {:int_lit, -2}
    assert Eval.eval({:case, scrut_neg, {:var, 0}, branches}, []) == {:vnat, 1}
  end
end
