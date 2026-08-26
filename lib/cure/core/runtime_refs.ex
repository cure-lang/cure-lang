defmodule Cure.Core.RuntimeRefs do
  @moduledoc """
  Collects the canonical globals needed to evaluate a Core term at runtime.

  Types, motives, and binder domains are deliberately excluded: they are checked
  before erasure but do not require a BEAM definition. Keeping this projection in
  one module prevents reachability and emission validation from drifting apart.
  """

  @spec globals(term()) :: [atom()]
  def globals(term), do: collect(term)

  defp collect({:global, name}) when is_atom(name), do: [name]

  defp collect({:case, scrutinee, _motive, branches}) do
    collect(scrutinee) ++
      Enum.flat_map(branches, fn
        {_constructor, _arity, body} -> collect(body)
        branch -> collect(branch)
      end)
  end

  defp collect({:pi, _grade, _domain, _codomain}), do: []
  defp collect({:lam, _grade, _domain, body}), do: collect(body)

  defp collect({:let, _grade, _type, value, body}),
    do: collect(value) ++ collect(body)

  defp collect({:effect_type, _inner}), do: []

  defp collect(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&collect/1)

  defp collect(terms) when is_list(terms), do: Enum.flat_map(terms, &collect/1)
  defp collect(_leaf), do: []
end
