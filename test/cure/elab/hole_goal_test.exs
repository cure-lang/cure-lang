defmodule Cure.Elab.HoleGoalTest do
  @moduledoc """
  Hole goal reporting (design spec §10/§11): a hole typechecks and reports its
  goal type plus the local context, so the programmer sees what must fill it.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  fn sketch({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = ?body
  """

  test "the sketch hole reports its goal type (an SF) and a non-empty local context" do
    {:ok, env} = Program.elaborate(@src)

    assert [%{function: :"Main#sketch", goal: goal, context: context}] = Program.hole_goals(env)

    # The goal is the declared return type: an SF(...) family application.
    assert {:data, :"Main#SF", _params, _indices} = goal

    # The local context is every parameter in scope (5 implicit + l + r).
    assert length(context) == 7
  end

  test "a program with no holes reports no goals" do
    hole_free = String.replace(@src, "= ?body", "= seq(l, r)")
    {:ok, env} = Program.elaborate(hole_free)
    assert Program.hole_goals(env) == []
  end
end
