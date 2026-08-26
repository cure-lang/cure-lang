defmodule Cure.Elab.MillerUnifyTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}

  # Higher-order (Miller) pattern unification: `?m x̄ := λx̄. t`. Exercised through
  # the public `unify/4` by unifying two Π types, so the metavariable-applied-to-a-
  # bound-variable constraint arises under the binder (depth 1). The abstraction
  # domains come from the metavariable's recorded type.

  @nat {:data, :Nat, [], []}
  # ?m : (Nat) -> Type
  defp fam_ctx, do: MetaCtx.fresh(MetaCtx.new(), {:pi, Cure.Core.Grade.unrestricted(), @nat, {:type, 0}})
  # ?m : (Nat) -> Nat — for solutions that are Nat *values* (index inference)
  defp fam_ctx_nn, do: MetaCtx.fresh(MetaCtx.new(), {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat})

  # `Vec (?m n) =? Vec <rhs>` under a binder: the index arg forces `?m(n) =? rhs`,
  # so mabs abstracts a Nat-VALUED rhs — the dependent index-inference path.
  defp solve_index(m_ctx, m, rhs) do
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:data, :Vec, [], [{:app, {:meta, m}, {:var, 0}}]}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:data, :Vec, [], [rhs]}}
    {:ok, ctx2} = Unify.unify(t1, t2, m_ctx, nil)
    Unify.zonk({:meta, m}, ctx2)
  end

  test "constant solution: ?m(n) =? Nat  ⇒  ?m := λ_:Nat. Nat" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat} == Unify.zonk({:meta, m}, ctx2)
  end

  test "identity solution: ?m(n) =? n  ⇒  ?m := λn:Nat. n" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "escape: ?m() applied to no bound var is not a Miller pattern (falls through)" do
    # A bare metavariable (no application) uses the ordinary first-order solve.
    {ctx, m} = fam_ctx()
    assert {:ok, ctx2} = Unify.unify({:meta, m}, @nat, ctx, nil)
    assert @nat == Unify.zonk({:meta, m}, ctx2)
  end

  test "no metavariable type recorded ⇒ Miller falls through (no crash, no solve)" do
    # fresh/1 records nil type; peel_pi_domains cannot supply domains, so the
    # higher-order case falls through to the first-order rules and fails cleanly.
    {ctx, m} = MetaCtx.fresh(MetaCtx.new())
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}
    assert {:error, _} = Unify.unify(t1, t2, ctx, nil)
  end

  # Structurally-rich solutions: the solution body carries a type-former, so the
  # abstraction step (`mabs`) must recurse THROUGH a binder-introducing node and
  # keep the pattern var's de Bruijn level correct. A depth bug here would abstract
  # the wrong variable and produce an unsound metavariable solution.

  test "Pi solution: ?m(n) =? (Πk:Nat. Nat)  ⇒  ?m := λn. Πk:Nat. Nat" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)

    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}} ==
             Unify.zonk({:meta, m}, ctx2)
  end

  test "Sigma solution: ?m(n) =? Sigma(Nat, λ_.Nat)  ⇒  ?m := λn. Sigma(Nat, λ_.Nat)" do
    {ctx, m} = fam_ctx()
    # Inductive Sigma (D2): the non-dependent pair type is `Sigma(Nat, λ_.Nat)`.
    sig = {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, sig}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, sig} == Unify.zonk({:meta, m}, ctx2)
  end

  test "Equivalent solution binding the pattern var: ?m(n) =? Eq Nat n n  ⇒  ?m := λn. Eq Nat n n" do
    # The bound var n appears INSIDE the Equivalent's index positions — mabs's
    # :data clause must abstract it (var 0 under the solution's λ), not leave it
    # dangling or escape. A wrong depth yields the wrong endpoint. (Migrated
    # from the primitive {:eq} spelling when the form retired, Phase C; the
    # dedicated mabs {:eq} clause retired with it.)
    {ctx, m} = fam_ctx()
    eqv = {:data, :Equivalent, [@nat], [{:var, 0}, {:var, 0}]}
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, eqv}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, eqv} == Unify.zonk({:meta, m}, ctx2)
  end

  test "indexed-family solution: ?m(n) =? Vec n  ⇒  ?m := λn. Vec n (index abstracted)" do
    # The pattern var flows into a family INDEX position. mabs's `:data` clause must
    # recurse into the index list and abstract n there — the dependent-inference case
    # (a metavariable resolved to an indexed type).
    {ctx, m} = fam_ctx()
    t1 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:data, :Vec, [], [{:var, 0}]}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, {:data, :Vec, [], [{:var, 0}]}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "ctor-valued index: Vec(?m n) =? Vec(S n)  ⇒  ?m := λn. S n" do
    {ctx, m} = fam_ctx_nn()

    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, {:ctor, :S, [{:var, 0}]}} ==
             solve_index(ctx, m, {:ctor, :S, [{:var, 0}]})
  end

  test "op-spine-valued index: Vec(?m n) =? Vec(int_add n n)  ⇒  ?m := λn. int_add n n" do
    # K2 re-spell: computed index is a builtin-op global spine (mabs's generic
    # {:app} clause abstracts it; same solution shape).
    {ctx, m} = fam_ctx_nn()
    spine = {:app, {:app, {:global, :int_add}, {:var, 0}}, {:var, 0}}
    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, spine} == solve_index(ctx, m, spine)
  end

  test "case-valued index: Vec(?m n) =? Vec(case n {Z→Z; S k→k})  ⇒  ?m := λn. case n {…}" do
    # The scrutinee is the pattern var n; mabs's :case clause must abstract it and
    # descend into each branch body at depth + ctor-arity (the S branch adds 1).
    rhs =
      {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat},
       [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:var, 0}}]}

    {ctx, m} = fam_ctx_nn()
    assert solve_index(ctx, m, rhs) == {:lam, Cure.Core.Grade.unrestricted(), @nat, rhs}
  end

  test "effect-wrapped solution: mabs descends through Effect" do
    {ctx, m} = fam_ctx_nn()
    lhs = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:effect_type, {:app, {:meta, m}, {:var, 0}}}}
    rhs = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:effect_type, @nat}}

    assert {:ok, ctx2} = Unify.unify(lhs, rhs, ctx, nil)

    assert {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat} ==
             Unify.zonk({:meta, m}, ctx2)
  end
end
