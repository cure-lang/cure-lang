defmodule Cure.Elab.UnifyAbstractCaseIncompletenessRedTest do
  @moduledoc """
  FINDING A (erasure-unify cluster): `Cure.Elab.Unify`'s single-argument
  flex-rigid solver (`flex_rigid_solve/5`, lib/cure/elab/unify.ex:201) builds its
  abstraction with a SECOND, less complete walker — `abstract_exact_term/3`
  (unify.ex:236) — instead of the general-purpose `mabs/5` (unify.ex:320) used by
  Miller-pattern solving. `mabs/5` has explicit clauses for `:case`,
  `:effect_type`, `:effect_pure`, and `:effect_bind`; `abstract_exact_term/3` has
  none of them and falls through to its identity catch-all, silently failing to
  abstract an occurrence that sits INSIDE one of those forms.

  `contains_term?/2` (the guard that gates `flex_rigid_solve`) is a fully
  generic structural walker with NO such gap — it finds the target occurrence
  wherever it is, including nested inside a `:case`. So the precondition passes,
  `flex_rigid_solve` commits to building a solution, and `abstract_exact_term`
  then silently leaves the nested occurrence unabstracted: the "solution" is a
  constant lambda that literally embeds the original argument term instead of
  referencing its own bound parameter.

  This test hand-builds the minimal flex-rigid equation
  `?predicate(argument) =?= Family(case argument-embedding-scrutinee { … })`
  directly at the `Cure.Elab.Unify` unit level (bypassing surface syntax and
  full elaboration, which cannot easily steer a real program into this exact
  precondition combination within reasonable effort) and shows the produced
  solution differs from the correctly-abstracted one `mabs/5` would have
  produced.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Grade
  alias Cure.Elab.{MetaCtx, Unify}

  test "flex-rigid solving abstracts an occurrence nested inside a :case, not just the whole node" do
    domain = {:data, :Whatever, [], []}
    pi_type = {:pi, Grade.unrestricted(), domain, {:type, 0}}

    m = MetaCtx.new()
    {m, id} = MetaCtx.fresh(m, pi_type)

    argument = {:global, :x}

    # `argument` occurs nested INSIDE a `:case` node's single branch body — not
    # as the case node itself, and not as a whole element of `Family`'s index
    # list either.
    case_term = {:case, {:global, :scrut}, {:global, :motive}, [{:SomeCtor, 0, argument}]}

    lhs = {:app, {:meta, id}, argument}
    rhs = {:data, :Family, [], [case_term]}

    assert {:ok, m2} = Unify.unify(lhs, rhs, m)

    solution = MetaCtx.solution(m2, id)

    # DESIRED POST-FIX BEHAVIOR: the solution abstracts EVERY occurrence of
    # `argument`, including the one nested inside the `:case` branch body, into
    # the lambda's own bound variable — exactly as `mabs/5` already does for the
    # Miller-pattern path.
    expected_case = {:case, {:global, :scrut}, {:global, :motive}, [{:SomeCtor, 0, {:var, 0}}]}
    expected = {:lam, Grade.unrestricted(), domain, {:data, :Family, [], [expected_case]}}

    assert solution == expected
  end
end
