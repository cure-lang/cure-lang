defmodule Cure.Compiler.ModulePipeline.Environment do
  @moduledoc """
  A semantic environment assembled from checked module interfaces.

  Merging is a union keyed by canonical module identity, so idempotence and
  order-independence hold by construction rather than by convention: merging the
  same interface twice replaces an entry with itself, and two interfaces for the
  same module with different hashes is a conflict rather than a last-writer-wins
  overwrite.
  """

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.ModulePipeline.Interface
  alias Cure.Core.{Builtins, Conv, Env}
  alias Cure.Elab.Name

  defstruct interfaces: %{}, env: nil

  @type t :: %__MODULE__{interfaces: %{String.t() => ModuleInterface.t()}, env: Env.t()}

  @spec merge([ModuleInterface.t()]) :: {:ok, t()} | {:error, term()}
  def merge(interfaces) when is_list(interfaces) do
    with {:ok, table} <- table(interfaces),
         {:ok, env} <- Interface.environment(table) do
      {:ok, %__MODULE__{interfaces: table, env: env}}
    end
  end

  defp table(interfaces) do
    Enum.reduce_while(interfaces, {:ok, %{}}, fn interface, {:ok, table} ->
      case Map.fetch(table, interface.module_name) do
        :error ->
          {:cont, {:ok, Map.put(table, interface.module_name, interface)}}

        {:ok, existing} ->
          if existing.interface_hash == interface.interface_hash,
            do: {:cont, {:ok, table}},
            else: {:halt, {:error, {:conflicting_interfaces, interface.module_name}}}
      end
    end)
  end

  @doc """
  A canonical, order-independent projection of everything the environment means.

  Two environments with the same dump accept exactly the same programs.
  """
  @spec semantic_dump(t()) :: term()
  def semantic_dump(%__MODULE__{env: env}) do
    %{
      defs: sorted(env.defs, & &1.type),
      direct_call_summaries: Enum.sort(env.direct_call_summaries),
      totality_components: Enum.sort(env.totality_components),
      totality_component_of: Enum.sort(env.totality_component_of),
      families: sorted(env.families, & &1),
      ctors: sorted(env.ctors, & &1),
      ctor_to_family: Enum.sort(env.ctor_to_family),
      interfaces: sorted(env.interfaces, & &1),
      primitives: sorted(env.primitives, & &1),
      builtins: Enum.sort(env.builtins),
      constrained: Enum.sort(env.constrained),
      coherence: env.coherence,
      equations: Enum.sort(env.equations),
      lemmas: Enum.sort(env.lemmas)
    }
  end

  defp sorted(table, projection) do
    table |> Enum.sort_by(&elem(&1, 0)) |> Enum.map(fn {key, value} -> {key, projection.(value)} end)
  end

  @doc "Every canonical name the environment owns, tagged with its namespace."
  @spec canonical_identities(t()) :: [{atom(), atom()}]
  def canonical_identities(%__MODULE__{env: env}) do
    [
      Enum.map(Map.keys(env.families), &{:type, &1}),
      Enum.map(Map.keys(env.ctors), &{:constructor, &1}),
      Enum.map(Map.keys(env.defs), &{:value, &1}),
      Enum.map(Map.keys(env.interfaces), &{:interface, &1})
    ]
    |> Enum.concat()
    |> Enum.sort()
  end

  @doc """
  Whether two written type names denote the same type up to definitional
  equality in this environment.
  """
  @spec definitionally_equal?(t(), String.t(), String.t()) :: boolean()
  def definitionally_equal?(%__MODULE__{} = environment, left, right) do
    env = query_env(environment)

    with {:ok, left_term} <- type_term(env, left),
         {:ok, right_term} <- type_term(env, right) do
      Conv.conv?(left_term, right_term, [], 0, env)
    else
      :error -> false
    end
  end

  # Dumps project only what the interfaces own, but a *question* about types is
  # asked against the same ground the elaborator stands on — builtin families
  # included, or `Int` would be an unknown name rather than a type.
  defp query_env(%__MODULE__{env: %Env{} = env}) do
    seeded = Builtins.seed(Env.empty(), MapSet.new())

    %Env{
      env
      | families: Map.merge(seeded.families, env.families),
        ctors: Map.merge(seeded.ctors, env.ctors),
        ctor_to_family: Map.merge(seeded.ctor_to_family, env.ctor_to_family),
        defs: Map.merge(seeded.defs, env.defs),
        primitives: Map.merge(seeded.primitives, env.primitives),
        certified: MapSet.union(seeded.certified, env.certified),
        totality_certified: MapSet.union(seeded.totality_certified, env.totality_certified)
    }
  end

  defp type_term(env, written) do
    case canonical_key(env, written) do
      {:ok, key} -> {:ok, family_or_global(env, key)}
      :error -> :error
    end
  end

  defp family_or_global(env, key) do
    if Map.has_key?(env.families, key), do: {:data, key, [], []}, else: {:global, key}
  end

  defp canonical_key(env, written) do
    candidates =
      case String.split(written, ".") do
        [bare] -> Enum.filter(names(env), &(Name.base(&1) == bare))
        parts -> [Name.qualify(Enum.drop(parts, -1) |> Enum.join("."), List.last(parts))]
      end

    case candidates |> Enum.filter(&known?(env, &1)) |> Enum.uniq() do
      [key] -> {:ok, key}
      _ -> :error
    end
  end

  defp names(env), do: Map.keys(env.families) ++ Map.keys(env.defs)

  defp known?(env, key), do: Map.has_key?(env.families, key) or Map.has_key?(env.defs, key)
end
