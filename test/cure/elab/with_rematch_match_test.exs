defmodule Cure.Elab.WithRematchMatchTest do
  @moduledoc """
  Unit tests for `Cure.Elab.Elaborator.match_parent_lhs/2` — the LHS re-match
  algorithm (ports Idris `TTImp.WithClause.getMatch`). Pure AST: it matches the
  parent function's original param patterns against a with-clause's RESTATED
  patterns, producing a substitution `parent_var => refined_pattern`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Elaborator

  defp v(name), do: {:variable, [], name}
  defp ctor(name, args), do: {:function_call, [name: name], args}

  test "variable against a constructor application binds the refinement" do
    # parent `n`, restated `S(m)`  =>  n ↦ S(m)
    assert {:ok, subst} = Elaborator.match_parent_lhs([v("n")], [ctor("S", [v("m")])])
    assert %{"n" => {:function_call, meta, [{:variable, _, "m"}]}} = subst
    assert Keyword.get(meta, :name) == "S"
  end

  test "variable against a nullary constructor binds the refinement" do
    assert {:ok, subst} = Elaborator.match_parent_lhs([v("n")], [ctor("Z", [])])
    assert %{"n" => {:function_call, meta, []}} = subst
    assert Keyword.get(meta, :name) == "Z"
  end

  test "lowercase GADT constructors are valid restated patterns" do
    assert {:ok, subst} = Elaborator.match_parent_lhs([v("s")], [ctor("szero", [])])
    assert %{"s" => {:function_call, meta, []}} = subst
    assert Keyword.get(meta, :name) == "szero"
  end

  test "variable against a variable is an alias" do
    assert {:ok, subst} = Elaborator.match_parent_lhs([v("n")], [v("m")])
    assert %{"n" => {:variable, _, "m"}} = subst
  end

  test "multiple params: refined + kept sibling" do
    # parent `(n, w)`, restated `(S(m), w)` => n ↦ S(m), w ↦ w
    assert {:ok, subst} =
             Elaborator.match_parent_lhs([v("n"), v("w")], [ctor("S", [v("m")]), v("w")])

    assert %{"n" => {:function_call, _, [{:variable, _, "m"}]}, "w" => {:variable, _, "w"}} = subst
  end

  test "constructor against constructor recurses structurally" do
    # orig `S(k)`, restated `S(S(j))` => k ↦ S(j)
    assert {:ok, subst} =
             Elaborator.match_parent_lhs([ctor("S", [v("k")])], [ctor("S", [ctor("S", [v("j")])])])

    assert %{"k" => {:function_call, meta, [{:variable, _, "j"}]}} = subst
    assert Keyword.get(meta, :name) == "S"
  end

  test "also accepts {:param, …} originals" do
    assert {:ok, subst} =
             Elaborator.match_parent_lhs([{:param, [], "n"}], [ctor("S", [v("m")])])

    assert %{"n" => {:function_call, _, _}} = subst
  end

  test "rejects a non-constructor (forced/arithmetic) restated pattern" do
    kpk = {:binary_op, [operator: :+], [v("k"), v("k")]}

    assert {:error, {:with_rematch_non_constructor_pattern, _}} =
             Elaborator.match_parent_lhs([v("n")], [kpk])
  end

  test "rejects a constructor-head mismatch on structural recurse" do
    assert {:error, {:with_rematch_ctor_mismatch, _, _}} =
             Elaborator.match_parent_lhs([ctor("S", [v("k")])], [ctor("Z", [])])
  end

  test "rejects an arity mismatch between params and restated patterns" do
    assert {:error, {:with_rematch_arity_mismatch, _, _}} =
             Elaborator.match_parent_lhs([v("n")], [v("n"), v("w")])
  end
end
