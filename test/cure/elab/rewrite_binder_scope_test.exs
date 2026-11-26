defmodule Cure.Elab.RewriteBinderScopeTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, Rewrite, Subst}

  @nat {:data, :Nat, [], []}
  @zero {:ctor, :Z, []}

  defp binder_pairs do
    [
      {{:pi, :erased, @nat, {:var, 1}}, {:pi, :erased, @nat, {:var, 2}}},
      {{:lam, :unrestricted, @nat, {:var, 1}}, {:lam, :unrestricted, @nat, {:var, 2}}},
      {{:let, :erased, @nat, @zero, {:var, 1}}, {:let, :erased, @nat, @zero, {:var, 2}}},
      {{:case, @zero, {:global, :motive}, [{:C, 2, {:ctor, :Pair, [{:var, 2}, {:var, 0}]}}]},
       {:case, @zero, {:global, :motive}, [{:C, 2, {:ctor, :Pair, [{:var, 3}, {:var, 0}]}}]}},
      {{:lam, :unrestricted, @nat,
        {:case, @zero, {:global, :motive}, [{:C, 2, {:let, :erased, @nat, @zero, {:var, 4}}}]}},
       {:lam, :unrestricted, @nat,
        {:case, @zero, {:global, :motive}, [{:C, 2, {:let, :erased, @nat, @zero, {:var, 5}}}]}}}
    ]
  end

  test "default, numbered and all goal rewrites shift replacements beneath every binder" do
    for {original, expected} <- binder_pairs(),
        selector <- [nil, 1, :all],
        direction <- [:forward, :backwards] do
      {left, right} = if direction == :forward, do: {{:var, 0}, {:var, 1}}, else: {{:var, 1}, {:var, 0}}

      assert {:ok, _build, ^expected, [_]} =
               Rewrite.directed_plan({:var, 2}, @nat, left, right, original, direction, selector)
    end
  end

  test "hypothesis transforms preserve binder scope in both directions" do
    for {original, expected} <- binder_pairs(),
        selector <- [nil, 1],
        direction <- [:forward, :backwards] do
      {left, right} = if direction == :forward, do: {{:var, 0}, {:var, 1}}, else: {{:var, 1}, {:var, 0}}

      assert {:ok, _transform, ^expected, [_]} =
               Rewrite.directed_transform({:var, 2}, @nat, left, right, original, direction, selector)
    end
  end

  test "scoped walkers and motive abstraction agree for let and nested case binders" do
    for {original, expected} <- binder_pairs() do
      assert Rewrite.contains_term_scoped?(original, {:var, 0})
      assert Rewrite.replace_term_scoped(original, {:var, 0}, {:var, 1}) == expected
      abstracted = Rewrite.abstract_term(original, {:var, 0}, 0)
      assert Subst.instantiate(abstracted, [{:var, 1}]) == expected
    end

    bound_only = {:let, :erased, @nat, @zero, {:var, 0}}
    refute Rewrite.contains_term_scoped?(bound_only, {:var, 0})
    assert Rewrite.replace_term_scoped(bound_only, {:var, 0}, {:var, 1}) == bound_only
    assert [] = Rewrite.occurrences(bound_only, {:var, 0})
  end

  test "rewrite-all updates each original case branch path without capturing its local fields" do
    original =
      {:case, @zero, {:global, :motive}, [{:First, 0, {:var, 0}}, {:Second, 2, {:ctor, :Pair, [{:var, 2}, {:var, 0}]}}]}

    expected =
      {:case, @zero, {:global, :motive}, [{:First, 0, {:var, 1}}, {:Second, 2, {:ctor, :Pair, [{:var, 3}, {:var, 0}]}}]}

    assert {:ok, _build, ^expected, [first, second]} =
             Rewrite.directed_plan({:var, 2}, @nat, {:var, 0}, {:var, 1}, original, :forward, :all)

    assert first.traversal_path == [2, 0, 1]
    assert second.traversal_path == [2, 1, 1, 1, 0]
  end

  test "transport evidence for Pi, lambda and let occurrences checks against the original goal" do
    assert {:ok, env} =
             Program.elaborate("""
             mod RewriteBinderFixture
               type Nat = Z | S(Nat)
               fn witness(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) = h
             end
             """)

    %{type: type} = Env.get_def(env, :witness)
    {context, _target} = open_telescope(type, Context.empty(env))
    nat = {:data, :"RewriteBinderFixture#Nat", [], []}
    x = {:var, 2}
    y = {:var, 1}
    lambda = fn value -> {:lam, :unrestricted, nat, Subst.shift(value, 1, 0)} end
    function_type = {:pi, :unrestricted, nat, nat}

    fixtures = [
      {{:pi, :unrestricted, nat, Rewrite.mk_eq(nat, Subst.shift(x, 1, 0), Subst.shift(y, 1, 0))},
       {:lam, :unrestricted, nat, Rewrite.mk_refl(Subst.shift(y, 1, 0))}},
      {Rewrite.mk_eq(function_type, lambda.(x), lambda.(y)), Rewrite.mk_refl(lambda.(y))},
      {{:let, :unrestricted, nat, y, Rewrite.mk_eq(nat, Subst.shift(x, 1, 0), Subst.shift(y, 1, 0))},
       Rewrite.mk_refl(y)}
    ]

    for {original, evidence} <- fixtures, selector <- [nil, 1, :all] do
      assert {:ok, build, rewritten, [_]} =
               Rewrite.directed_plan({:var, 0}, nat, x, y, original, :forward, selector)

      assert :ok = Kernel.check(context, evidence, Eval.eval(rewritten, Context.env(context)))
      assert :ok = Kernel.check(context, build.(evidence), Eval.eval(original, Context.env(context)))

      selected = if selector == :all, do: 1, else: selector

      assert {:ok, transform, ^rewritten, [_]} =
               Rewrite.directed_transform({:var, 0}, nat, x, y, original, :forward, selected)

      assert :ok = Kernel.check(context, transform.(build.(evidence)), Eval.eval(rewritten, Context.env(context)))
    end

    case_lambda = fn value ->
      {:lam, :unrestricted, nat,
       {:case, {:var, 0}, {:lam, :unrestricted, nat, nat},
        [
          {:"RewriteBinderFixture#Z", 0, Subst.shift(value, 1, 0)},
          {:"RewriteBinderFixture#S", 1, Subst.shift(value, 2, 0)}
        ]}}
    end

    original = Rewrite.mk_eq(function_type, case_lambda.(x), case_lambda.(y))
    evidence = Rewrite.mk_refl(case_lambda.(y))

    assert {:ok, build, rewritten, [_, _]} =
             Rewrite.directed_plan({:var, 0}, nat, x, y, original, :forward, :all)

    assert :ok = Kernel.check(context, evidence, Eval.eval(rewritten, Context.env(context)))
    assert :ok = Kernel.check(context, build.(evidence), Eval.eval(original, Context.env(context)))
  end

  defp open_telescope({:pi, grade, domain, body}, context),
    do: open_telescope(body, Context.extend(context, Eval.eval(domain, Context.env(context)), grade))

  defp open_telescope(target, context), do: {context, target}
end
