defmodule Cure.Elab.SubstTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Subst

  test "instantiates a family application's binders in telescope order" do
    # SF(#2, #1, #0) with [a, b, c]  ⇒  SF(a, b, c)   (a is the outermost binder #2)
    type = {:data, :SF, [], [{:var, 2}, {:var, 1}, {:var, 0}]}
    a = {:ctor, :SVNil, []}
    b = {:ctor, :SVCons, []}
    c = {:ctor, :Causal, []}
    assert Subst.instantiate(type, [a, b, c]) == {:data, :SF, [], [a, b, c]}
  end

  test "substitutes metavariables as telescope values" do
    type = {:data, :SF, [], [{:var, 1}, {:var, 0}]}

    assert Subst.instantiate(type, [{:meta, 7}, {:ctor, :Causal, []}]) ==
             {:data, :SF, [], [{:meta, 7}, {:ctor, :Causal, []}]}
  end

  test "strengthens free variables past the instantiated telescope" do
    # #3 is one past a 3-binder telescope ⇒ becomes #0 after dropping the 3 binders
    assert Subst.instantiate({:var, 3}, [{:var, 9}, {:var, 8}, {:var, 7}]) == {:var, 0}
  end

  test "leaves a metavariable untouched (closed) under substitution" do
    assert Subst.instantiate({:meta, 3}, [{:ctor, :Causal, []}]) == {:meta, 3}
  end

  test "respects inner binders when instantiating a Pi codomain" do
    # Π(Dec). #1   with [a]   ⇒   the telescope var #1 becomes a (shifted over the Π binder)
    type = {:pi, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, {:var, 1}}
    a = {:ctor, :Causal, []}
    assert Subst.instantiate(type, [a]) == {:pi, Cure.Core.Grade.unrestricted(), {:data, :Dec, [], []}, a}
  end

  test "shift lifts free variables above the cutoff" do
    assert Subst.shift({:app, {:var, 0}, {:var, 2}}, 2, 1) == {:app, {:var, 0}, {:var, 4}}
  end
end
