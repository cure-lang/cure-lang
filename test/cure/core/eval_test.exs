defmodule Cure.Core.EvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "beta-reduces an application" do
    assert {:vtype, 0} ==
             Eval.eval({:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}}, [])
  end

  test "iota-reduces mk_pair projections via a single-branch case" do
    # Inductive Sigma (D2): projection is a `:case` over the `mk_pair` ctor.
    pair = {:ctor, :mk_pair, [{:type, 0}, {:type, 1}]}
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}
    assert {:vtype, 0} == Eval.eval({:case, pair, motive, [{:mk_pair, 2, {:var, 1}}]}, [])
    assert {:vtype, 1} == Eval.eval({:case, pair, motive, [{:mk_pair, 2, {:var, 0}}]}, [])
  end

  test "a free variable evaluates to a neutral var" do
    assert {:vneutral, {:nvar, _}} = Eval.eval({:var, 0}, [])
  end

  test "an uncertified global evaluates to a neutral global (opaque until delta)" do
    assert {:vneutral, {:nglobal, :and}} == Eval.eval({:global, :and}, [])
  end

  test "a stuck projection on a neutral stays neutral" do
    # Inductive Sigma (D2): a projection case on a neutral scrutinee is a stuck ncase.
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}

    assert {:vneutral, {:ncase, {:nvar, 0}, _, _}} =
             Eval.eval({:case, {:var, 0}, motive, [{:mk_pair, 2, {:var, 1}}]}, [{:vneutral, {:nvar, 0}}])
  end

  test "apply extends the environment with the argument at index 0" do
    vlam = Eval.eval({:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, [])
    assert {:vtype, 1} == Eval.apply(vlam, {:vtype, 1})
  end

  test "iota: a case on a constructor selects that constructor's branch" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, {:type, 2}}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 1}}]
    cas = {:case, {:ctor, :Causal, []}, motive, branches}
    assert {:vtype, 1} == Eval.eval(cas, [])
  end

  test "iota: a case binds the constructor's arguments in the branch body" do
    # case (mk Type0) of { mk x -> x } ⇝ Type0
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], []}, {:type, 1}}
    branches = [{:mk, 1, {:var, 0}}]
    cas = {:case, {:ctor, :mk, [{:type, 0}]}, motive, branches}
    assert {:vtype, 0} == Eval.eval(cas, [])
  end

  test "iota: a case on a neutral scrutinee stays a neutral case" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, {:type, 0}}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]
    cas = {:case, {:var, 0}, motive, branches}
    assert {:vneutral, {:ncase, {:nvar, 0}, _m, _b}} = Eval.eval(cas, [{:vneutral, {:nvar, 0}}])
  end
end
