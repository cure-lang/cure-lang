defmodule Cure.Core.ConvTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Conv

  test "beta: (λ.#0) Type0 ≡ Type0" do
    assert Conv.conv?(
             {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}},
             {:type, 0},
             [],
             0
           )
  end

  test "reflexivity of a lambda" do
    assert Conv.conv?(
             {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}},
             {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}},
             [],
             0
           )
  end

  test "eta: f ≡ λ. (f #0) at a function type" do
    # context: f is var 0 (a neutral). env binds it; depth = 1.
    env = [{:vneutral, {:nvar, 0}}]
    f = {:var, 0}
    eta = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:var, 1}, {:var, 0}}}
    assert Conv.conv?(f, eta, env, 1)
    assert Conv.conv?(eta, f, env, 1)
  end

  test "negative: Type0 ≢ Type1" do
    refute Conv.conv?({:type, 0}, {:type, 1}, [], 0)
  end

  test "negative: distinct constructors are not convertible" do
    refute Conv.conv?({:ctor, :Dcoupled, []}, {:ctor, :Causal, []}, [], 0)
  end

  test "Pi types compare domain and codomain" do
    assert Conv.conv?(
             {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}},
             {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}},
             [],
             0
           )

    refute Conv.conv?(
             {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}},
             {:pi, Cure.Core.Grade.unrestricted(), {:type, 1}, {:var, 0}},
             [],
             0
           )
  end

  test "a stuck case on a neutral scrutinee is convertible to itself" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, {:type, 0}}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]
    cas = {:case, {:var, 0}, motive, branches}
    assert Conv.conv?(cas, cas, [{:vneutral, {:nvar, 0}}], 1)
  end

  test "stuck cases with different branch bodies are not convertible" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, {:type, 0}}
    b1 = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]
    b2 = [{:Dcoupled, 0, {:type, 1}}, {:Causal, 0, {:type, 0}}]

    refute Conv.conv?(
             {:case, {:var, 0}, motive, b1},
             {:case, {:var, 0}, motive, b2},
             [{:vneutral, {:nvar, 0}}],
             1
           )
  end

  test "stuck case branch bodies compare under fresh constructor binders" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], []}, {:type, 0}}
    lhs_branches = [{:mk, 1, {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:var, 0}}}]
    rhs_branches = [{:mk, 1, {:var, 0}}]

    assert Conv.conv?(
             {:case, {:var, 0}, motive, lhs_branches},
             {:case, {:var, 0}, motive, rhs_branches},
             [{:vneutral, {:nvar, 0}}],
             1
           )
  end
end
