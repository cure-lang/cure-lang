defmodule Cure.Elab.Collapsible do
  @moduledoc false

  alias Cure.Core.{Grade, Inductive}

  @type classification :: :runtime | :unreachable | {:collapse, {atom(), non_neg_integer(), term()}}

  @doc "Classify a kernel-checked case by its runtime-relevant alternatives."
  @spec classify(Cure.Core.Env.t(), [{atom(), non_neg_integer(), term()}]) :: classification()
  def classify(env, branches) do
    case Enum.reject(branches, fn {_cname, _arity, body} -> unreachable?(body) end) do
      [] ->
        :unreachable

      [{cname, arity, body} = branch] ->
        if case?(env, cname, arity, body), do: {:collapse, branch}, else: :runtime

      _multiple_runtime_branches ->
        :runtime
    end
  end

  @doc "Whether a kernel-checked one-branch case carries no runtime choice or payload."
  def case?(env, cname, arity, body) do
    with dname when dname != nil <- Inductive.ctor_family(env, cname),
         %{indices: indices} <- Inductive.get_family(env, dname),
         quantities when is_list(quantities) <- Inductive.ctor_quantities(env, cname),
         true <- arity == length(quantities) do
      all_erased? =
        Enum.all?(quantities, &Grade.erased?/1) and
          (quantities != [] or indices != [])

      forced_payload_absent? =
        indices != [] and
          present_branch_fields_absent?(body, quantities)

      all_erased? or forced_payload_absent?
    else
      _ -> false
    end
  end

  # An empty elimination is kernel-certified ex-falso. A case all of whose
  # alternatives are themselves ex-falso likewise cannot produce a runtime
  # value. Keep this deliberately structural: lambdas, lets, and effects are
  # values/computations even when their bodies eventually eliminate an empty
  # type, so they must not be classified as unreachable here.
  defp unreachable?({:case, _scrutinee, _motive, []}), do: true

  defp unreachable?({:case, _scrutinee, _motive, branches}) when branches != [] do
    Enum.all?(branches, fn {_cname, _arity, body} -> unreachable?(body) end)
  end

  defp unreachable?({:app, function, _argument}), do: unreachable?(function)
  defp unreachable?(_term), do: false

  defp present_branch_fields_absent?(body, quantities) do
    present =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {quantity, _position} -> Grade.present?(quantity) end)
      |> MapSet.new(fn {_quantity, position} -> length(quantities) - 1 - position end)

    MapSet.disjoint?(present, free_indices(body, 0))
  end

  defp free_indices({:var, index}, depth) when index >= depth, do: MapSet.new([index - depth])
  defp free_indices({:var, _index}, _depth), do: MapSet.new()

  defp free_indices({tag, _grade, domain, body}, depth) when tag in [:pi, :lam] do
    MapSet.union(free_indices(domain, depth), free_indices(body, depth + 1))
  end

  defp free_indices({:let, _grade, type, value, body}, depth) do
    [free_indices(type, depth), free_indices(value, depth), free_indices(body, depth + 1)]
    |> Enum.reduce(MapSet.new(), &MapSet.union/2)
  end

  defp free_indices({:case, scrutinee, motive, branches}, depth) do
    base = MapSet.union(free_indices(scrutinee, depth), free_indices(motive, depth))

    Enum.reduce(branches, base, fn {_cname, arity, body}, acc ->
      MapSet.union(acc, free_indices(body, depth + arity))
    end)
  end

  defp free_indices(term, depth) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.drop(1)
    |> Enum.reduce(MapSet.new(), fn child, acc -> MapSet.union(acc, free_indices(child, depth)) end)
  end

  defp free_indices(term, depth) when is_list(term) do
    Enum.reduce(term, MapSet.new(), fn child, acc -> MapSet.union(acc, free_indices(child, depth)) end)
  end

  defp free_indices(_term, _depth), do: MapSet.new()
end
