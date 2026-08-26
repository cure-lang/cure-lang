defmodule Cure.Elab.UnifyScopeCheckTest do
  @moduledoc """
  Regression: `Unify.solve/4`'s scope check must be fail-CLOSED.

  Before recording `?m := t`, `strengthen/2` asks `escapes?/3` whether `t` mentions
  any of the binders being stripped away — the Miller-pattern SCOPE CHECK, dual to
  the occurs check. A `false` answer authorizes `Subst.shift(t, -depth, 0)`.

  `escapes?/3` was a hand-enumerated walk (var/meta/pi/lam/app/data/ctor) whose
  catch-all answered `false` — "does not escape" — for every shape it had not been
  taught, including `{:case, scrut, motive, branches}`. `Subst.shift/3` DOES walk
  `:case` correctly, so it faithfully shifted the escaping variable rather than
  crashing: `{:var, 0}` became `{:var, -1}`, and `unify/3` returned `{:ok, _}`.

  A negative de Bruijn index is not inert the way an unsolved `{:meta, _}` is — that
  has a `has_meta?` firewall. It is a syntactically well-formed `{:var, k}` that
  shift/subst/zonk keep processing until something finally indexes an environment
  with it. On the BEAM many lookups accept negative indices as "count from the end",
  so the failure mode is a silent, wrong variable substitution.

  The catch-all is now `true` (assume escape). Note that a generic structural walk
  would be WRONG here: `escapes?` must bump `local` at every binder, and a walk that
  did not would under-estimate the free-index threshold and MISS escapes. Binders
  stay explicit; only the unknown-shape default flipped.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{MetaCtx, Unify}

  @dom {:type, 0}

  test "a metavariable solved against a :case whose branch references a crossed binder is rejected" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new())

    # (x: Type) -> case _ { C() -> x } — the branch body is the Pi's own binder.
    case_term =
      {:case, {:global, :dummy_scrutinee}, {:lam, Cure.Core.Grade.unrestricted(), @dom, @dom}, [{:C, 0, {:var, 0}}]}

    assert {:error, {:escaping_variable, ^id}} =
             Unify.unify(
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:meta, id}},
               {:pi, Cure.Core.Grade.unrestricted(), @dom, case_term},
               ctx
             )
  end

  test "the scope check also fires on a :case scrutinee referencing a crossed binder" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new())

    case_term = {:case, {:var, 0}, {:type, 0}, [{:some_ctor, 0, {:var, 0}}]}

    assert {:error, {:escaping_variable, ^id}} =
             Unify.unify(
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:meta, id}},
               {:pi, Cure.Core.Grade.unrestricted(), @dom, case_term},
               ctx
             )
  end

  test "the scope check fires when the :case is nested inside a constructor argument" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new())

    case_term =
      {:case, {:global, :dummy_scrutinee}, {:lam, Cure.Core.Grade.unrestricted(), @dom, @dom}, [{:C, 0, {:var, 0}}]}

    assert {:error, {:escaping_variable, ^id}} =
             Unify.unify(
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:meta, id}},
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:ctor, :Wrap, [case_term]}},
               ctx
             )
  end

  test "a :case branch body referencing only its OWN pattern binders does not escape" do
    # The branch binds `ar` variables, so {:var, 0} inside a 1-ary branch body is the
    # branch's own binder, not the crossed Pi binder. `escapes?` must bump `local` by
    # the branch arity or it would reject this legitimate solution.
    {ctx, id} = MetaCtx.fresh(MetaCtx.new())

    case_term =
      {:case, {:global, :dummy_scrutinee}, {:lam, Cure.Core.Grade.unrestricted(), @dom, @dom}, [{:C, 1, {:var, 0}}]}

    assert {:ok, ctx} =
             Unify.unify(
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:meta, id}},
               {:pi, Cure.Core.Grade.unrestricted(), @dom, case_term},
               ctx
             )

    assert {:case, _, _, [{:C, 1, {:var, 0}}]} = MetaCtx.solution(ctx, id)
  end

  test "an unrecognized term shape is assumed to escape rather than silently shifted" do
    # Fail-closed default: a shape `escapes?` has never been taught must not be
    # waved through as scope-clean. This is what makes the walk safe as the Core
    # grammar grows.
    {ctx, id} = MetaCtx.fresh(MetaCtx.new())

    assert {:error, {:escaping_variable, ^id}} =
             Unify.unify(
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:meta, id}},
               {:pi, Cure.Core.Grade.unrestricted(), @dom, {:some_future_node, {:var, 0}}},
               ctx
             )
  end
end
