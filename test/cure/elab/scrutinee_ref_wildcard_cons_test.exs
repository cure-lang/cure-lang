defmodule Cure.Elab.ScrutineeRefWildcardConsTest do
  @moduledoc """
  Referencing the SCRUTINEE variable itself inside a non-nullary constructor
  branch whose sub-patterns are WILDCARDS (`[_ | _]`) must elaborate.

  `refine_scrutinee_in_body/5` rewrites free occurrences of the scrutinee name
  in the branch body to the branch pattern rendered as an expression (Lean's
  `subst.insert majorFVarId ctorApp`). A pattern like `[h | t]` is a valid
  expression, so `MkBox(list)` → `MkBox([h | t])` typechecks. But `[_ | _]`
  is NOT expressible — a wildcard has no value — and rendering it into term
  position resolved both `_`s to the head element binder, so the tail slot
  received an element (`var 3`) where `List(t)` was expected:
  `{:index_mismatch, {:cannot_unify, {:data, :List, [var: 3], []}, {:var, 3}}}`.

  When the pattern is not expressible, the surface refinement is skipped: the
  scrutinee variable is still in branch scope with its original type, so the
  body elaborates against it directly. This is the residual blocker that kept
  `Std.Iter` (`cycle`'s `[_ | _] -> cstep(list, list)`) off the dependent
  pipeline.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "scrutinee referenced in a wildcard cons branch elaborates" do
    src = """
    mod M
      type Box(a) = MkBox(a)
      fn cyc(list: List(t)) -> Box(List(t)) =
        match list
          []      -> MkBox([])
          [_ | _] -> MkBox(list)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "scrutinee referenced in a named cons branch still elaborates" do
    src = """
    mod M
      type Box(a) = MkBox(a)
      fn cyc(list: List(t)) -> Box(List(t)) =
        match list
          []      -> MkBox([])
          [h | t] -> MkBox(list)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
