defmodule Cure.Test.ProofCaseContextFixture do
  @moduledoc false

  alias Cure.Core.{Env, Eval, Grade, ProofRecipe, ProofWire, Quote, Term}
  alias Cure.Test.{ProofBundleFixture, ProofRecipeFixture, ProofSnapshotFixture}

  # Explicit fixture annotations, not automatic recipe inference.
  def requests do
    g = Grade.unrestricted()
    atom = {:atom_type}
    payload = {:atom_lit, :payload}
    %{body: {:case, packed, motive, branches}} = Env.get_def(ProofSnapshotFixture.environment(), :"Boundary#unpack")
    {:certificate, _families, [_, _, _, {:packet, _, {:r_convert, _, _, base}}]} = ProofRecipeFixture.certificate()
    {:r_case, ctor, ps, indices, level, kind, mot, branch_recipes} = base
    open_scrutinee = {:ctor, :"Boundary#Pack", [{:var, 1}, {:var, 0}]}
    open_case = {:case, open_scrutinee, motive, branches}
    open_recipe = converted_case({:var, 1}, {:var, 1}, open_scrutinee, motive, base)
    lambda_scrutinee = {:ctor, :"Boundary#Pack", [atom, {:var, 0}]}
    lambda_case = {:case, lambda_scrutinee, motive, branches}
    lambda_recipe = converted_case(atom, atom, lambda_scrutinee, motive, base)
    nested_branches = Enum.map(branches, fn {name, arity, _body} -> {name, arity, open_case} end)

    nested_recipes =
      Enum.map(branch_recipes, fn {fields, {:r_convert, goal, conversion, :r_leaf}} ->
        {fields, {:r_convert, goal, conversion, open_recipe}}
      end)

    nested_base = {:r_case, ctor, ps, indices, level, kind, mot, nested_recipes}
    nested_recipe = converted_case(atom, atom, packed, motive, nested_base)

    [
      {:dependent,
       {:caller, [{"A", {:type, 0}}, {"x", {:var, 0}}], [:r_leaf, :r_leaf], [atom, payload], [:r_leaf, :r_leaf],
        open_case, {:var, 1}, open_recipe, :r_leaf}, [{:vatom, :payload}, {:vatom_type}]},
      {:lambda,
       {:caller, [], [], [], [], {:lam, g, atom, lambda_case}, {:pi, g, atom, atom}, {:r_lam, :r_leaf, lambda_recipe},
        {:r_pi, :r_leaf, :r_leaf}}, []},
      {:nested, {:caller, [], [], [], [], {:case, packed, motive, nested_branches}, atom, nested_recipe, :r_leaf}, []}
    ]
  end

  def to_agda do
    observations = Enum.map_join(requests(), "\n", &observation/1)

    {:ok,
     """
     -- Existing-tag caller requests plus fixed terminating Eval/Quote observations.
     module Fixtures.ExecutableCaseContext where
     open import Data.Char using (Char)
     open import Data.List using (List)
     open import Data.String.Base using (toList)

     #{observations}
     """}
  end

  defp observation({key, {:caller, _, _, _, _, subject, _goal, _, _} = request, env}) do
    {:ok, characters} = ProofRecipe.encode_caller(request, ProofBundleFixture.table())
    quoted = Quote.reify(Eval.eval(subject, env), 0)
    {:ok, quoted_chars} = ProofWire.encode_term(quoted, ProofBundleFixture.table())
    name = Atom.to_string(key)

    """
    #{name}-characters : List Char
    #{name}-characters = toList "#{characters}"
    #{name}-quoted-characters : List Char
    #{name}-quoted-characters = toList "#{quoted_chars}"
    """
  end

  defp converted_case(goal, index, scrutinee, motive, base) do
    middle = {:app, beta({:app, motive, index}), scrutinee}
    {:r_convert, goal, {:c_trans, middle, {:c_app, :c_beta, :c_refl}, :c_beta}, base}
  end

  defp beta({:app, {:lam, _grade, _domain, body}, argument}),
    do: body |> Term.subst(0, Term.shift(argument, 1, 0)) |> Term.shift(-1, 0)
end
