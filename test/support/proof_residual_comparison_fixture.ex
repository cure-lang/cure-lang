defmodule Cure.Test.ProofResidualComparisonFixture do
  @moduledoc false

  alias Cure.Core.{Conv, Eval, Grade, Inductive, ProofRecipe, ProofWire, Quote, Term}
  alias Cure.Test.{ProofBundleFixture, ProofResidualQuotationFixture, ProofSnapshotFixture}

  # Only reviewed terminating terms are evaluated. Source recipes are
  # explicit proposals; decoding and native admission are checked in Agda.
  def checking_cases do
    {plain, plain_kind} = case_type(false, false)
    {redex, redex_kind} = case_type(true, false)
    {nested, nested_kind} = case_type(false, true)
    {nested_redex, nested_redex_kind} = case_type(true, true)

    [
      checking(:residual, redex, redex_kind, plain, plain_kind),
      checking(:reverse, plain, plain_kind, redex, redex_kind),
      checking(
        :data,
        {:data, :"Boundary#Packed", [], [redex]},
        {:r_data, [], [redex_kind]},
        {:data, :"Boundary#Packed", [], [plain]},
        {:r_data, [], [plain_kind]}
      ),
      checking(:nested, nested_redex, nested_redex_kind, nested, nested_kind)
    ]
  end

  def comparisons do
    signature = ProofSnapshotFixture.environment()

    previous =
      Enum.map(ProofResidualQuotationFixture.cases(), fn {key, program, env, depth} ->
        {key, program, Quote.reify(Eval.eval(program, env), depth, signature), env, depth}
      end)

    checking =
      Enum.map(checking_cases(), fn {key, {:checking, _, _, _, goal, _}, inferred} ->
        {checking_key(key), inferred, goal, [], 0}
      end)

    atom = {:atom_type}
    g = Grade.unrestricted()
    case_node = fn name, ar -> {:case, {:global, :"Boundary#packed"}, atom, [{name, ar, atom}]} end

    previous ++
      checking ++
      [
        {:delta_boundary, {:global, :"Boundary#answer"}, {:atom_lit, :answer}, [], 0},
        {:eta_boundary, {:lam, g, atom, {:app, {:var, 1}, {:var, 0}}}, {:var, 0}, [{:vneutral, {:nvar, 0}}], 1},
        {:grade_boundary, {:pi, Grade.one(), atom, atom}, {:pi, g, atom, atom}, [], 0},
        {:universe_boundary, {:type, 0}, {:type, 1}, [], 0},
        {:name_boundary, case_node.(:"Boundary#Pack", 2), case_node.(:"Boundary#Alternate", 2), [], 0},
        {:arity_boundary, case_node.(:"Boundary#Pack", 2), case_node.(:"Boundary#Pack", 3), [], 0}
      ]
  end

  def to_agda do
    observations = Enum.map_join(comparisons(), "\n", &observation/1)

    requests =
      Enum.map_join(checking_cases(), "\n", fn {key, request, inferred} ->
        {:ok, characters} = ProofRecipe.encode_checking(request, ProofBundleFixture.table())
        name = Atom.to_string(key)

        """
        #{name}-characters : List Char
        #{name}-characters = toList "#{characters}"
        #{name}-inferred : Term
        #{name}-inferred = #{term(inferred)}
        """
      end)

    {:ok,
     """
     {-# OPTIONS --guardedness #-}
     -- Fixed actual Conv/Quote pairs and raw requests, not universal refinement.
     module Fixtures.ExecutableResidualComparison where
     open import Data.Bool using (Bool; true; false)
     open import Data.Char using (Char)
     open import Data.List using (List; []; _∷_)
     open import Data.Nat using (ℕ)
     open import Data.String.Base using (toList)
     open import Relation.Binary.PropositionalEquality using (refl)
     open import Core.Syntax using (Term)
     import Core.ClosureEval as E
     import Core.ResidualComparison as Compare
     open import Fixtures.ExecutableResidualQuotation using (read-term)
     import Fixtures.ExecutableResidualQuotation as Prior
     #{observations}
     #{requests}
     """}
  end

  defp observation({key, left, right, env, depth}) do
    signature = ProofSnapshotFixture.environment()
    lq = Quote.reify(Eval.eval(left, env), depth, signature)
    rq = Quote.reify(Eval.eval(right, env), depth, signature)
    actual = Conv.conv?(left, right, env, depth, signature)
    classification = if lq == rq, do: "Compare.equal-forms", else: "Compare.distinct-forms"
    name = key |> Atom.to_string() |> String.replace("_", "-")
    environment = environment(key, env)

    """
    #{name}-left #{name}-right #{name}-left-quoted #{name}-right-quoted : Term
    #{name}-left = #{term(left)}
    #{name}-right = #{term(right)}
    #{name}-left-quoted = #{term(lq)}
    #{name}-right-quoted = #{term(rq)}
    #{name}-environment : List E.Value
    #{name}-environment = #{environment}
    #{name}-depth : ℕ
    #{name}-depth = #{depth}
    #{name}-actual : Bool
    #{name}-actual = #{actual}
    #{name}-classification : Compare.Classification
    #{name}-classification = #{classification}
    """
  end

  defp environment(_key, []), do: "[]"
  defp environment(:eta_boundary, [_value]), do: "(E.v-neutral (E.n-var 0) ∷ [])"
  defp environment(key, _env), do: "Prior.#{key |> Atom.to_string() |> String.replace("_", "-")}-environment"

  defp checking_key(:residual), do: :checking_residual
  defp checking_key(:reverse), do: :checking_reverse
  defp checking_key(:data), do: :checking_data
  defp checking_key(:nested), do: :checking_nested

  defp checking(key, domain, kind, goal_domain, goal_kind) do
    g = Grade.unrestricted()
    inferred = {:pi, g, domain, domain}

    request =
      {:checking, {:lam, g, domain, {:var, 0}}, {:r_lam, kind, :r_leaf}, {:r_pi, kind, kind},
       {:pi, g, goal_domain, goal_domain}, {:r_pi, goal_kind, goal_kind}}

    {key, request, inferred}
  end

  defp case_type(redex?, nested?) do
    g = Grade.unrestricted()
    atom = {:atom_type}
    global = {:global, :"Boundary#packed"}
    motive = {:lam, g, {:type, 0}, {:lam, g, {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:type, 0}}}
    beta_kind = {:r_app, {:r_lam, :r_leaf, :r_leaf}, :r_leaf}
    beta_type = {:app, {:lam, g, {:type, 0}, {:var, 0}}, atom}

    {body, body_recipe} =
      cond do
        nested? -> case_type(redex?, false)
        redex? -> {beta_type, beta_kind}
        true -> {atom, :r_leaf}
      end

    ctors =
      Enum.map([:"Boundary#Pack", :"Boundary#Alternate"], &Inductive.get_ctor(ProofSnapshotFixture.environment(), &1))

    branches = Enum.map(ctors, fn ctor -> {ctor.name, 2, body} end)

    branch_recipes =
      Enum.map(ctors, fn ctor ->
        [_, _] = ctor.args
        [index] = ctor.result_indices
        value = {:ctor, ctor.name, [{:var, 1}, {:var, 0}]}
        goal = {:app, {:app, Term.shift(motive, 2, 0), index}, value}
        {[:r_leaf, :r_leaf], {:r_convert, goal, {:c_sym, two_beta(goal)}, body_recipe}}
      end)

    kind = {:r_pi, :r_leaf, {:r_pi, {:r_data, [], [:r_leaf]}, :r_leaf}}
    motive_recipe = {:r_lam, :r_leaf, {:r_lam, {:r_data, [], [:r_leaf]}, :r_leaf}}
    case_recipe = {:r_case, :r_leaf, [], [:r_leaf], 1, kind, motive_recipe, branch_recipes}
    program = {:case, global, motive, branches}
    recipe = {:r_convert, {:type, 0}, two_beta({:app, {:app, motive, atom}, global}), case_recipe}
    {program, recipe}
  end

  defp two_beta({:app, {:app, {:lam, _g, _domain, body}, index}, value}) do
    middle = body |> Term.subst(0, Term.shift(index, 1, 0)) |> Term.shift(-1, 0)
    {:c_trans, {:app, middle, value}, {:c_app, :c_beta, :c_refl}, :c_beta}
  end

  defp term(term) do
    {:ok, chars} = ProofWire.encode_term(term, ProofBundleFixture.table())
    ~s|(read-term (toList "#{chars}") refl)|
  end
end
