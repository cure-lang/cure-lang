defmodule Cure.Compiler.ModulePipeline.Closure do
  @moduledoc """
  What a checked universe actually emits, read back from Core.

  Core is the only place where "what does this definition depend on" has a final
  answer: the surface may say `use`, the manifest may say discovery, but the
  emitted term names exactly the globals it needs. Every question here is
  answered by walking that term, so reachability, totality and emission cannot
  drift apart from each other.
  """

  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.Name

  @doc """
  A definition's Core, keyed canonically.

  Core carries no spans and no source order, so two runs that agree on meaning
  produce equal values here even when the files were written or submitted
  differently.
  """
  @spec normalized(Env.t(), String.t(), String.t()) :: {:ok, map()} | {:error, term()}
  def normalized(%Env{} = env, module_name, name) do
    key = Name.qualify(module_name, name)

    case Map.fetch(env.defs, key) do
      {:ok, definition} -> {:ok, %{key: key, type: definition.type, body: definition.body}}
      :error -> {:error, {:definition_unavailable, key}}
    end
  end

  @doc """
  Every global mentioned by a definition is a canonical owner-qualified key that
  the universe knows.

  A bare, unqualified, or dangling global in Core means a name survived
  elaboration without being resolved to a definition — the exact failure the
  canonical identity rule exists to prevent.
  """
  @spec all_globals_canonical?(Env.t(), [atom()]) :: boolean()
  def all_globals_canonical?(%Env{} = env, keys) do
    Enum.all?(keys, fn key ->
      definition = Map.fetch!(env.defs, key)

      definition
      |> mentioned_globals()
      |> Enum.all?(&(Name.owner(&1) != nil and Map.has_key?(env.defs, &1)))
    end)
  end

  @doc """
  The transitive closure of definitions an entry point emits.

  Kernel primitives terminate the walk rather than appearing in it: they are the
  ground the emitted code stands on, not code this universe emits. A global that
  is neither emitted nor primitive is reported instead of dropped.
  """
  @spec emission(Env.t(), atom(), (atom() -> tuple())) :: {:ok, [tuple()]} | {:error, term()}
  def emission(%Env{} = env, root, identify) do
    case reachable(env, [root]) do
      {:ok, keys} -> {:ok, Enum.map(keys, &{:definition, identify.(&1), Map.fetch!(env.defs, &1).body})}
      {:error, _} = error -> error
    end
  end

  @doc "Every key reachable from `roots`, primitives excluded."
  @spec reachable(Env.t(), [atom()]) :: {:ok, [atom()]} | {:error, term()}
  def reachable(%Env{} = env, roots), do: walk(env, primitive_keys(), roots, MapSet.new(), [])

  defp walk(_env, _primitives, [], _seen, collected), do: {:ok, Enum.sort(collected)}

  defp walk(env, primitives, [key | rest], seen, collected) do
    cond do
      MapSet.member?(seen, key) ->
        walk(env, primitives, rest, seen, collected)

      # The kernel's own globals are seeded, not checked: they are the one place
      # the walk stops without having found a definition to emit.
      MapSet.member?(primitives, key) ->
        walk(env, primitives, rest, MapSet.put(seen, key), collected)

      not Map.has_key?(env.defs, key) ->
        {:error, {:unresolved_global, key}}

      true ->
        definition = Map.fetch!(env.defs, key)
        walk(env, primitives, mentioned_globals(definition) ++ rest, MapSet.put(seen, key), [key | collected])
    end
  end

  defp primitive_keys do
    Env.empty() |> Builtins.seed(MapSet.new()) |> Map.fetch!(:defs) |> Map.keys() |> MapSet.new()
  end

  defp mentioned_globals(definition) do
    []
    |> collect(definition.body)
    |> collect(definition.type)
    |> Enum.uniq()
  end

  defp collect(acc, {:global, key}) when is_atom(key), do: [key | acc]
  defp collect(acc, term) when is_tuple(term), do: term |> Tuple.to_list() |> then(&collect(acc, &1))
  defp collect(acc, terms) when is_list(terms), do: Enum.reduce(terms, acc, &collect(&2, &1))
  defp collect(acc, %{} = term) when not is_struct(term), do: term |> Map.to_list() |> then(&collect(acc, &1))
  defp collect(acc, _term), do: acc
end
