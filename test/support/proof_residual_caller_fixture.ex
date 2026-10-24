defmodule Cure.Test.ProofResidualCallerFixture do
  @moduledoc false

  alias Cure.Core.{Conv, Eval, Grade, Inductive, ProofRecipe, ProofWire, Quote, Term}
  alias Cure.Test.{ProofBundleFixture, ProofResidualComparisonFixture, ProofSnapshotFixture}

  # Explicit, finite caller proposals. Actual calls see only this reviewed
  # terminating corpus; neither inference nor totality is asserted by data.
  def cases do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    beta = fn ty -> {:app, {:lam, g, {:type, 0}, {:var, 0}}, ty} end
    beta_kind = {:r_app, {:r_lam, :r_leaf, :r_leaf}, :r_leaf}
    bindings = [{"A", {:type, 0}}, {"x", {:var, 0}}]

    dependent =
      {:caller, bindings, [:r_leaf, :r_leaf], [atom, payload], [:r_leaf, :r_leaf], {:var, 0}, beta.({:var, 1}), :r_leaf,
       beta_kind}

    binder =
      {:caller, bindings, [:r_leaf, :r_leaf], [atom, payload], [:r_leaf, :r_leaf], {:lam, g, {:var, 1}, {:var, 0}},
       {:pi, g, beta.({:var, 1}), beta.({:var, 2})}, {:r_lam, :r_leaf, :r_leaf}, {:r_pi, beta_kind, beta_kind}}

    [{:residual, {:checking, subject, recipe, inferred_kind, goal, goal_kind}, inferred} | _] =
      ProofResidualComparisonFixture.checking_cases()

    empty = {:caller, [], [], [], [], subject, goal, recipe, goal_kind}

    collision =
      {:caller, [{"A", {:type, 0}}, {"x", {:type, 0}}, {"x", {:var, 1}}], [:r_leaf, :r_leaf, :r_leaf],
       [atom, atom, payload], [:r_leaf, :r_leaf, :r_leaf], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf}

    [
      {:dependent, dependent, :r_leaf, {:var, 1}, true},
      {:binder, binder, {:r_pi, :r_leaf, :r_leaf}, {:pi, g, {:var, 1}, {:var, 2}}, true},
      open_case(:opaque, false, false),
      open_case(:constructor, true, false),
      open_case(:nested, false, true),
      {:empty, empty, inferred_kind, inferred, true},
      {:collision, collision, :r_leaf, {:var, 2}, false}
    ]
  end

  def to_agda do
    observations = Enum.map_join(cases(), "\n", &observation/1)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Paired raw packets and reviewed actual observations, not extraction refinement.
     module Fixtures.ExecutableResidualCaller where
     open import Data.Bool using (Bool; true; false)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (refl)
     open import Core.Syntax using (Term)
     import Core.ClosureEval as E
     open import Fixtures.ExecutableResidualQuotation using (read-term)
     #{observations}
     """}
  end

  defp observation({key, {:caller, bindings, _, arguments, _, subject, goal, _, _} = caller, kind, inferred, accepted}) do
    signature = ProofSnapshotFixture.environment()
    size = length(bindings)
    env = fresh(size)
    closed_subject = close(subject, arguments)
    closed_goal = close(goal, arguments)
    open_left = Quote.reify(Eval.eval(inferred, env), size, signature)
    open_right = Quote.reify(Eval.eval(goal, env), size, signature)
    closed_quoted = Quote.reify(Eval.eval(closed_subject, []), 0, signature)
    actual = Conv.conv?(inferred, goal, env, size, signature)
    {:ok, caller_chars} = ProofRecipe.encode_caller(caller, ProofBundleFixture.table())
    {:ok, kind_chars} = ProofRecipe.encode_recipe(kind, ProofBundleFixture.table())
    name = Atom.to_string(key)

    """
    #{name}-caller-characters #{name}-kind-characters : List Char
    #{name}-caller-characters = toList "#{caller_chars}"
    #{name}-kind-characters = toList "#{kind_chars}"
    #{name}-size : ℕ
    #{name}-size = #{size}
    #{name}-environment : List E.Value
    #{name}-environment = #{environment(env)}
    #{name}-inferred #{name}-open-left #{name}-open-right #{name}-closed-subject #{name}-closed-goal #{name}-closed-quoted : Term
    #{name}-inferred = #{term(inferred)}
    #{name}-open-left = #{term(open_left)}
    #{name}-open-right = #{term(open_right)}
    #{name}-closed-subject = #{term(closed_subject)}
    #{name}-closed-goal = #{term(closed_goal)}
    #{name}-closed-quoted = #{term(closed_quoted)}
    #{name}-actual #{name}-expected-admission : Bool
    #{name}-actual = #{actual}
    #{name}-expected-admission = #{accepted}
    """
  end

  defp open_case(key, constructor?, nested?) do
    g = Grade.unrestricted()
    atom = {:atom_type}
    {domain, domain_kind} = case_type({:var, 0}, {:var, 1}, true, nested?)
    {codomain, codomain_kind} = case_type({:var, 1}, {:var, 2}, true, nested?)
    {goal_domain, goal_domain_kind} = case_type({:var, 0}, {:var, 1}, false, nested?)
    {goal_codomain, goal_codomain_kind} = case_type({:var, 1}, {:var, 2}, false, nested?)
    true = codomain == Term.shift(domain, 1, 0)
    bindings = [{"A", {:type, 0}}, {"x", {:data, :"Boundary#Packed", [], [{:var, 0}]}}]

    {value, value_recipe} =
      if constructor?,
        do: {{:ctor, :"Boundary#Pack", [atom, {:atom_lit, :payload}]}, {:r_ctor, [], [], [:r_leaf, :r_leaf]}},
        else: {{:global, :"Boundary#packed"}, :r_leaf}

    caller =
      {:caller, bindings, [:r_leaf, {:r_data, [], [:r_leaf]}], [atom, value], [:r_leaf, value_recipe],
       {:lam, g, domain, {:var, 0}}, {:pi, g, goal_domain, goal_codomain}, {:r_lam, domain_kind, :r_leaf},
       {:r_pi, goal_domain_kind, goal_codomain_kind}}

    {key, caller, {:r_pi, domain_kind, codomain_kind}, {:pi, g, domain, codomain}, true}
  end

  defp case_type(scrutinee, index, redex?, nested?) do
    g = Grade.unrestricted()
    atom = {:atom_type}
    motive = {:lam, g, {:type, 0}, {:lam, g, {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:type, 0}}}

    {body, body_recipe} =
      cond do
        nested? -> case_type(Term.shift(scrutinee, 2, 0), Term.shift(index, 2, 0), redex?, false)
        redex? -> {{:app, {:lam, g, {:type, 0}, {:var, 0}}, atom}, {:r_app, {:r_lam, :r_leaf, :r_leaf}, :r_leaf}}
        true -> {atom, :r_leaf}
      end

    ctors =
      Enum.map([:"Boundary#Pack", :"Boundary#Alternate"], &Inductive.get_ctor(ProofSnapshotFixture.environment(), &1))

    branches = Enum.map(ctors, fn ctor -> {ctor.name, 2, body} end)

    recipes =
      Enum.map(ctors, fn ctor ->
        [_, _] = ctor.args
        [result_index] = ctor.result_indices
        value = {:ctor, ctor.name, [{:var, 1}, {:var, 0}]}
        target = {:app, {:app, Term.shift(motive, 2, 0), result_index}, value}
        {[:r_leaf, :r_leaf], {:r_convert, target, {:c_sym, two_beta(target)}, body_recipe}}
      end)

    kind = {:r_pi, :r_leaf, {:r_pi, {:r_data, [], [:r_leaf]}, :r_leaf}}
    motive_recipe = {:r_lam, :r_leaf, {:r_lam, {:r_data, [], [:r_leaf]}, :r_leaf}}
    recipe = {:r_case, :r_leaf, [], [:r_leaf], 1, kind, motive_recipe, recipes}

    {{:case, scrutinee, motive, branches},
     {:r_convert, {:type, 0}, two_beta({:app, {:app, motive, index}, scrutinee}), recipe}}
  end

  defp two_beta({:app, {:app, {:lam, _g, _domain, body}, index}, value}),
    do: {:c_trans, {:app, top_sub(body, index), value}, {:c_app, :c_beta, :c_refl}, :c_beta}

  defp top_sub(body, value), do: body |> Term.subst(0, Term.shift(value, 1, 0)) |> Term.shift(-1, 0)
  defp close(body, arguments), do: Enum.reduce(Enum.reverse(arguments), body, &top_sub(&2, &1))
  defp fresh(0), do: []
  defp fresh(size), do: Enum.map((size - 1)..0//-1, &{:vneutral, {:nvar, &1}})
  defp environment([]), do: "[]"

  defp environment(env),
    do: "(" <> Enum.map_join(env, " ∷ ", fn {:vneutral, {:nvar, n}} -> "(E.v-neutral (E.n-var #{n}))" end) <> " ∷ [])"

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{chars}") refl)|
  end
end
