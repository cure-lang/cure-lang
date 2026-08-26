defmodule Cure.Core.EvalBoundedCoverageTest do
  @moduledoc """
  Regression: the `:vbounded` ι-site must fail as loudly as the `:vctor` one.

  `eval({:case, ...})` has two ι-sites for constructor-shaped scrutinees: the generic
  `{:vctor, cname, args}` arm, and a separate `{:vbounded, _}` arm that peels a compact
  `Bounded` literal to `First`/`Next` first. The `:vctor` arm looks the branch up with
  `Enum.find/2` and raises a descriptive coverage-violation error on `nil`. The
  `:vbounded` arm destructured the same `Enum.find/2` result directly, so an uncovered
  constructor crashed with a bare `MatchError` instead.

  This is a TCB fail-loud discipline issue, not a soundness hole — coverage is checked
  before eval — but a trusted evaluator that reports "no match of right hand side value
  nil" for an ill-typed term it was handed is one refactor away from reporting nothing
  at all. Agda/Idris/Lean report a uniform impossible-reduction failure regardless of
  which built-in family the stuck elimination came from.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Eval

  test "First/Next constructor values normalize to the compact Bounded representation" do
    tower =
      {:ctor, :"Std.Bounded#Next",
       [
         {:nat_lit, 2},
         {:ctor, :"Std.Bounded#Next", [{:nat_lit, 1}, {:ctor, :"Std.Bounded#First", [{:nat_lit, 0}]}]}
       ]}

    assert Eval.eval(tower, []) == {:vbounded, 2}
  end

  test "case-ι on a Bounded scrutinee with no matching branch raises the descriptive coverage error" do
    # {:bounded_lit, 1} peels to :Next; the branches only cover :First.
    case_term = {:case, {:bounded_lit, 1}, {:type, 0}, [{:First, 1, {:bounded_lit, 42}}]}

    assert_raise RuntimeError, ~r/ι: no branch for constructor :Next/, fn ->
      Eval.eval(case_term, [])
    end
  end

  test "case-ι on a Bounded scrutinee whose branch IS covered still reduces" do
    case_term =
      {:case, {:bounded_lit, 0}, {:type, 0}, [{:First, 1, {:bounded_lit, 42}}, {:Next, 2, {:bounded_lit, 99}}]}

    assert Eval.eval(case_term, []) == {:vbounded, 42}
  end

  test "compact Bounded literals select owner-qualified branches" do
    case_term =
      {:case, {:bounded_lit, 1}, {:type, 0},
       [
         {:"Std.Bounded#First", 1, {:bounded_lit, 42}},
         {:"Std.Bounded#Next", 2, {:var, 0}}
       ]}

    assert Eval.eval(case_term, []) == {:vbounded, 0}
  end
end
