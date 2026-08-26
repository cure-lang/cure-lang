defmodule Cure.Elab.UnifyTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}

  test "solves a metavariable against a constructor term" do
    m = MetaCtx.new()
    {m, id} = MetaCtx.fresh(m)
    assert {:ok, m2} = Unify.unify({:meta, id}, {:ctor, :Causal, []}, m)
    assert MetaCtx.solution(m2, id) == {:ctor, :Causal, []}
  end

  test "unifies two data applications, solving nested metavariables" do
    # SF(?a, ?b, Causal) ~ SF(SVNil, SVNil, Causal)  ⇒  ?a := SVNil, ?b := SVNil
    m = MetaCtx.new()
    {m, a} = MetaCtx.fresh(m)
    {m, b} = MetaCtx.fresh(m)

    lhs = {:data, :SF, [], [{:meta, a}, {:meta, b}, {:ctor, :Causal, []}]}
    rhs = {:data, :SF, [], [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}, {:ctor, :Causal, []}]}

    assert {:ok, m2} = Unify.unify(lhs, rhs, m)
    assert Unify.zonk({:meta, a}, m2) == {:ctor, :SVNil, []}
    assert Unify.zonk({:meta, b}, m2) == {:ctor, :SVNil, []}
  end

  test "solves a metavariable transitively through another" do
    m = MetaCtx.new()
    {m, a} = MetaCtx.fresh(m)
    {m, b} = MetaCtx.fresh(m)
    {:ok, m} = Unify.unify({:meta, a}, {:meta, b}, m)
    {:ok, m} = Unify.unify({:meta, b}, {:ctor, :Causal, []}, m)
    assert Unify.zonk({:meta, a}, m) == {:ctor, :Causal, []}
  end

  test "occurs check prevents an infinite solution" do
    m = MetaCtx.new()
    {m, a} = MetaCtx.fresh(m)
    assert {:error, _} = Unify.unify({:meta, a}, {:ctor, :C, [{:meta, a}]}, m)
  end

  test "rejects mismatched constructor heads" do
    m = MetaCtx.new()
    assert {:error, _} = Unify.unify({:ctor, :Causal, []}, {:ctor, :Dcoupled, []}, m)
  end

  test "unifies an applied global (computed index) structurally" do
    m = MetaCtx.new()
    {m, a} = MetaCtx.fresh(m)
    lhs = {:app, {:app, {:global, :andd}, {:meta, a}}, {:ctor, :Causal, []}}
    rhs = {:app, {:app, {:global, :andd}, {:ctor, :Dcoupled, []}}, {:ctor, :Causal, []}}
    assert {:ok, m2} = Unify.unify(lhs, rhs, m)
    assert Unify.zonk({:meta, a}, m2) == {:ctor, :Dcoupled, []}
  end

  test "zonk leaves an unsolved metavariable in place" do
    m = MetaCtx.new()
    {m, a} = MetaCtx.fresh(m)
    assert Unify.zonk({:data, :SF, [], [{:meta, a}]}, m) == {:data, :SF, [], [{:meta, a}]}
  end
end
