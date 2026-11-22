defmodule Cure.Elab.Omega.Certificate do
  @moduledoc """
  Core encoding for the existing checked Boolean LIA candidate test.

  Rows use `dot(coefficients, variables) <= bound`. Every row shares one
  sorted variable basis, so sparse coefficients cannot change dimensions or
  silently refer to another variable. A `True` result validates multipliers;
  it does not supply semantic premise evidence or prove a source goal.
  """

  @checker :"Std.Proof.LinearArithmetic#check_lia_candidate"

  @doc "Build a candidate test; hypotheses do not include the negated goal."
  def term(hypotheses, goal, multipliers) when is_list(hypotheses) and is_list(multipliers) do
    rows = hypotheses ++ [goal]

    if Enum.all?(rows, &valid_row?/1) and Enum.all?(multipliers, &(is_integer(&1) and &1 >= 0)) do
      variables = basis(rows)
      args = [list(hypotheses, &atom_term(&1, variables)), atom_term(goal, variables), list(multipliers, &nat/1)]
      {:ok, Enum.reduce(args, {:global, @checker}, fn arg, call -> {:app, call, arg} end)}
    else
      {:error, :invalid_omega_certificate_input}
    end
  end

  def term(_hypotheses, _goal, _multipliers), do: {:error, :invalid_omega_certificate_input}

  @doc "The shared coordinate basis, preserving actual de Bruijn indices."
  def basis(rows) do
    rows |> Enum.flat_map(fn {{_bound, coefficients}, _} -> Map.keys(coefficients) end) |> Enum.uniq() |> Enum.sort()
  end

  @doc "Encode a valuation on the same basis; do not invert context indices."
  def valuation(rows), do: rows |> basis() |> list(&{:var, &1})

  defp atom_term({{bound, coefficients}, relation}, variables) do
    values = Enum.map(variables, &Map.get(coefficients, &1, 0))

    relation =
      if relation == :le, do: :"Std.Proof.LinearArithmetic#LessOrEqual", else: :"Std.Proof.LinearArithmetic#LessThan"

    {:ctor, :"Std.Proof.LinearArithmetic#LinearAtom", [list(values, &integer/1), integer(bound), {:ctor, relation, []}]}
  end

  defp list(values, encode) do
    Enum.reduce(Enum.reverse(values), {:ctor, :"Std.List#Nil", []}, fn value, rest ->
      {:ctor, :"Std.List#Cons", [encode.(value), rest]}
    end)
  end

  defp integer(value) when value >= 0, do: {:ctor, :"Std.Int#FromNat", [nat(value)]}
  defp integer(value), do: {:ctor, :"Std.Int#NegativeSuccessor", [nat(-value - 1)]}
  defp nat(value), do: {:nat_lit, value}

  defp valid_row?({{bound, coefficients}, relation}) when is_integer(bound) and is_map(coefficients) do
    relation in [:le, :lt] and
      Enum.all?(coefficients, fn {index, coefficient} ->
        is_integer(index) and index >= 0 and is_integer(coefficient)
      end)
  end

  defp valid_row?(_row), do: false
end
