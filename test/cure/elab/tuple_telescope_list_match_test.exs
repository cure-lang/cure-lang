defmodule Cure.Elab.TupleTelescopeListMatchTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  # REGRESSION (#23 value-surface parity) — was a reach-pinned elaborator-
  # completeness gap, now FIXED. A Σ-telescope tuple RETURN type of arity >= 3
  # that contains a `List(_)` component failed to elaborate when the function body
  # produced it from a `match` on a `List` scrutinee: the inner `[]`'s `Nil`
  # element metavar was left unsolved (`{:error, {:unsolved_metavariables, :Nil}}`).
  #
  # ROOT CAUSE (2026-07-11): `elaborate_branch_body` (elaborator.ex) routed only
  # a 2-element tuple `{:tuple, _, [_a, _b]}` through the CHECKING path (against the
  # index-refined branch goal); a flat n-ary tuple (arity >= 3, the #35 telescope)
  # fell through to the default clause, which DISCARDS `expected` and elaborates in
  # INFER mode — so an inner bare `[]` never received the goal's `List(_)` and its
  # `Nil` element metavar stayed unsolved. The bug was NOT in the motive/branch
  # machinery: the SAME tuple built without a match elaborates (checking-mode there
  # flows through `check_tuple_against/5`), and a Bool-scrutinee match with the
  # same body works only because its arm bodies don't hit the infer default. Fix:
  # generalize the tuple clause to any arity >= 2 so flat telescopes check against
  # the goal identically to bare pairs. Std.Match's `first_two` Option-wrap
  # workaround is now unnecessary (kept as-is; behavioral tests are immutable).
  test "3-ary tuple with a List component built from a List-scrutinee match elaborates" do
    src = """
    mod Probe
      fn f(list: List(a), d: a) -> Tuple(a, a, List(a)) =
        match list
          [h | t] -> %[h, d, t]
          []      -> %[d, d, []]
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
