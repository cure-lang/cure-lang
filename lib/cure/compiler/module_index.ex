defmodule Cure.Compiler.ModuleIndex.Entry do
  @moduledoc false

  @enforce_keys [:module_name, :source_path, :source_hash]
  defstruct module_name: nil,
            source_path: nil,
            source_hash: nil,
            direct_edges: [],
            provided_modules: [],
            prelude_provider?: false

  @type t :: %__MODULE__{
          module_name: String.t(),
          source_path: Path.t(),
          source_hash: binary(),
          direct_edges: [Cure.Compiler.ModuleIndex.edge()],
          provided_modules: [String.t()],
          prelude_provider?: boolean()
        }
end

defmodule Cure.Compiler.ModuleIndex do
  @moduledoc """
  Canonical module-name index for a complete compilation universe.

  Paths are validated attributes. Resolution and dependency edges use declared
  module identities exclusively, so filename order cannot affect identity.
  """

  alias Cure.Compiler.ModuleIndex.Entry
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityScan}

  @compiler_modules MapSet.new(["Std.Builtin"])

  defstruct entries: %{}, paths: %{}, providers: %{}, prelude_providers: MapSet.new()

  @type edge :: %{
          required(:kind) => :use_import | :qualified_reference | :prelude_provider,
          required(:source_module) => String.t(),
          required(:target) => String.t(),
          required(:source_path) => Path.t(),
          required(:line) => pos_integer()
        }

  @spec module_names(t()) :: [String.t()]
  def module_names(%__MODULE__{providers: providers}), do: providers |> Map.keys() |> Enum.sort()

  @doc "Whether a canonical module interface is supplied by the compiler itself."
  @spec compiler_owned?(String.t()) :: boolean()
  def compiler_owned?(module_name), do: MapSet.member?(@compiler_modules, module_name)

  @doc "Canonical module interfaces available in every compiler environment."
  @spec compiler_modules() :: MapSet.t(String.t())
  def compiler_modules, do: @compiler_modules

  @type t :: %__MODULE__{
          entries: %{String.t() => Entry.t()},
          paths: %{Path.t() => String.t()},
          providers: %{String.t() => String.t()},
          prelude_providers: MapSet.t(String.t())
        }

  @spec build([Path.t()], keyword()) :: {:ok, t()} | {:error, term()}
  def build(paths, opts \\ []) do
    paths = paths |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()

    with {:ok, entries} <- scan_entries(paths, opts),
         :ok <- reject_duplicates(entries),
         :ok <- reject_provider_duplicates(entries) do
      index = assemble(entries)

      if Keyword.get(opts, :validate_dependencies, true),
        do: validate_dependencies(index, Keyword.get(opts, :known_modules, [])),
        else: {:ok, index}
    end
  end

  @doc "Build an index from already-scanned canonical entries."
  @spec from_entries([Entry.t()], keyword()) :: {:ok, t()} | {:error, term()}
  def from_entries(entries, opts \\ []) do
    entries =
      entries
      |> Enum.map(fn entry -> %{entry | source_path: Path.expand(entry.source_path)} end)
      |> Enum.sort_by(&{&1.module_name, &1.source_path})

    with :ok <- reject_duplicates(entries),
         :ok <- reject_provider_duplicates(entries) do
      index = assemble(entries)

      if Keyword.get(opts, :validate_dependencies, true),
        do: validate_dependencies(index, Keyword.get(opts, :known_modules, [])),
        else: {:ok, index}
    end
  end

  @spec fetch(t(), String.t()) :: {:ok, Entry.t()} | {:error, term()}
  def fetch(%__MODULE__{entries: entries, providers: providers}, module_name) do
    owner = Map.get(providers, module_name, module_name)

    case Map.fetch(entries, owner) do
      {:ok, entry} ->
        {:ok, entry}

      :error ->
        {:error, {:module_unavailable, module_name, %{available_modules: providers |> Map.keys() |> Enum.sort()}}}
    end
  end

  @doc "Return the source module whose compilation unit provides `module_name`."
  @spec provider_owner(t(), String.t()) :: String.t() | nil
  def provider_owner(%__MODULE__{providers: providers}, module_name),
    do: Map.get(providers, module_name)

  @spec fetch_by_path(t(), Path.t()) :: {:ok, Entry.t()} | {:error, term()}
  def fetch_by_path(%__MODULE__{paths: paths} = index, path) do
    case Map.fetch(paths, Path.expand(path)) do
      {:ok, module_name} -> fetch(index, module_name)
      :error -> {:error, {:source_not_indexed, Path.expand(path)}}
    end
  end

  @spec edges(t(), String.t()) :: [edge()]
  def edges(%__MODULE__{} = index, module_name) do
    case index.entries[module_name] do
      nil ->
        []

      entry ->
        ambient =
          for provider <- index.prelude_providers,
              provider != module_name do
            %{
              kind: :prelude_provider,
              source_module: module_name,
              target: provider,
              source_path: entry.source_path,
              line: 1
            }
          end

        (entry.direct_edges ++ ambient)
        |> Enum.uniq_by(&{&1.kind, &1.target, &1.line})
        |> Enum.sort_by(&{&1.target, &1.kind, &1.line})
    end
  end

  @spec dependency_order(t()) :: [String.t()]
  def dependency_order(%__MODULE__{} = index) do
    names = Map.keys(index.entries)

    dependencies =
      Map.new(names, fn name ->
        deps =
          index
          |> edges(name)
          |> Enum.map(& &1.target)
          |> Enum.map(&(provider_owner(index, &1) || &1))
          |> Enum.filter(&Map.has_key?(index.entries, &1))
          |> Enum.reject(&(&1 == name))
          |> Enum.uniq()

        {name, deps}
      end)

    Cure.Compiler.DepGraph.toposort(dependencies, names)
  end

  defp scan_entries(paths, opts) do
    Enum.reduce_while(paths, {:ok, []}, fn path, {:ok, entries} ->
      case scan_entry(path, opts) do
        {:ok, nil} -> {:cont, {:ok, entries}}
        {:ok, entry} -> {:cont, {:ok, [entry | entries]}}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  defp scan_entry(path, opts) do
    with {:ok, source} <- File.read(path) do
      if String.trim(source) == "" do
        {:ok, nil}
      else
        facts = FixityScan.harvest_source(source, path, BuiltinFixity.table())

        case facts.module do
          module_name when is_binary(module_name) ->
            direct_edges =
              Enum.map(facts.uses, fn use ->
                edge(:use_import, module_name, use.target, path, use.line)
              end) ++
                Enum.map(facts.qualified_targets, fn reference ->
                  edge(:qualified_reference, module_name, reference.target, path, reference.line)
                end)

            {:ok,
             %Entry{
               module_name: module_name,
               source_path: path,
               source_hash: :crypto.hash(:sha256, source),
               direct_edges: direct_edges,
               provided_modules: [module_name],
               prelude_provider?: facts.prelude?
             }}

          _ ->
            if Keyword.get(opts, :ignore_unidentified, false),
              do: {:ok, nil},
              else: {:error, {:module_identity_missing, path}}
        end
      end
    else
      {:error, reason} -> {:error, {:module_index_source_error, path, reason}}
    end
  end

  defp edge(kind, source_module, target, path, line),
    do: %{kind: kind, source_module: source_module, target: target, source_path: path, line: line}

  defp reject_duplicates(entries) do
    entries
    |> Enum.group_by(& &1.module_name)
    |> Enum.find_value(:ok, fn
      {_name, [_entry]} -> nil
      {name, duplicates} -> {:error, {:duplicate_module, name, Enum.map(duplicates, & &1.source_path) |> Enum.sort()}}
    end)
  end

  defp reject_provider_duplicates(entries) do
    entries
    |> Enum.flat_map(fn entry ->
      Enum.map(entry.provided_modules, &{&1, entry.module_name, entry.source_path})
    end)
    |> Enum.group_by(&elem(&1, 0))
    |> Enum.find_value(:ok, fn
      {_provided, [{_name, _owner, _path}]} ->
        nil

      {provided, duplicates} ->
        paths = duplicates |> Enum.map(&elem(&1, 2)) |> Enum.uniq() |> Enum.sort()

        if length(paths) == 1,
          do: nil,
          else: {:error, {:duplicate_module, provided, paths}}
    end)
  end

  defp assemble(entries) do
    providers =
      entries
      |> Enum.flat_map(fn entry ->
        Enum.map(entry.provided_modules, &{&1, entry.module_name})
      end)
      |> Enum.into(%{})

    %__MODULE__{
      entries: Map.new(entries, &{&1.module_name, &1}),
      paths: Map.new(entries, &{&1.source_path, &1.module_name}),
      providers: providers,
      prelude_providers:
        entries
        |> Enum.filter(& &1.prelude_provider?)
        |> MapSet.new(& &1.module_name)
    }
  end

  defp validate_dependencies(index, known_modules) do
    universe =
      index.providers
      |> Map.keys()
      |> MapSet.new()
      |> MapSet.union(@compiler_modules)
      |> MapSet.union(MapSet.new(known_modules))

    missing =
      index.entries
      |> Map.keys()
      |> Enum.sort()
      |> Enum.find_value(fn module_name ->
        Enum.find(edges(index, module_name), &(not MapSet.member?(universe, &1.target)))
      end)

    if missing,
      do: {:error, {:module_dependency_missing, missing}},
      else: {:ok, index}
  end
end
