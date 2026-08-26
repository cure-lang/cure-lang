defmodule Cure.Compiler.ModulePipeline.SemanticGraph do
  @moduledoc """
  The checked semantic graph.

  Bootstrap discovery is conservative and may over-include; this graph records
  what resolution *actually* consumed. It is authoritative for dependency
  hashes, invalidation, emission closure, and diagnostics.

  The edge vocabulary is closed: `Cure.Compiler.ModulePipeline.semantic_edge_kinds/0`
  enumerates it and `put/2` rejects anything else, so a second informal
  dependency notion cannot accumulate beside this one.
  """

  alias Cure.Compiler.ModuleManifest

  @kinds [
    :lexical_use,
    :qualified_reference,
    :prelude_symbol_use,
    :type_reference,
    :value_reference,
    :interface_provider,
    :implementation_selection,
    :macro_home,
    :macro_generated_reference,
    :generated_declaration_owner,
    :extern_owner,
    :runtime_call
  ]

  defstruct edges: %{}

  @type edge :: %{
          required(:kind) => atom(),
          required(:source) => String.t(),
          required(:target) => String.t(),
          optional(:declaration) => tuple() | nil,
          optional(:phase) => atom(),
          optional(:span) => map() | nil
        }

  @type t :: %__MODULE__{edges: %{String.t() => [edge()]}}

  @spec kinds() :: [atom()]
  def kinds, do: @kinds

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Seed the graph with the edges the manifest already established by scanning
  headers: explicit imports, qualified references, and the ambient prelude
  surface. Later phases add the edges only elaboration can know.
  """
  @spec from_manifest(ModuleManifest.t()) :: t()
  def from_manifest(%ModuleManifest{} = manifest) do
    manifest.dependencies
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.reduce(new(), fn {_identity, dependencies}, graph ->
      Enum.reduce(dependencies, graph, fn dependency, graph ->
        put(graph, %{
          kind: bootstrap_kind(dependency.kind),
          source: elem(dependency.source, 1),
          target: elem(dependency.target, 1),
          declaration: nil,
          phase: :discover,
          span: dependency.span
        })
      end)
    end)
  end

  defp bootstrap_kind(:use_import), do: :lexical_use
  defp bootstrap_kind(kind) when kind in @kinds, do: kind

  @spec put(t(), edge()) :: t()
  def put(%__MODULE__{} = graph, %{kind: kind, source: source, target: target} = edge)
      when kind in @kinds and is_binary(source) and is_binary(target) do
    edge =
      edge
      |> Map.put_new(:declaration, nil)
      |> Map.put_new(:phase, nil)
      |> Map.put_new(:span, nil)

    existing = Map.get(graph.edges, source, [])

    if Enum.any?(existing, &same_edge?(&1, edge)) do
      graph
    else
      %{graph | edges: Map.put(graph.edges, source, [edge | existing])}
    end
  end

  defp same_edge?(left, right) do
    left.kind == right.kind and left.target == right.target and
      left.declaration == right.declaration
  end

  @spec edges(t() | nil, String.t()) :: [edge()]
  def edges(nil, _source), do: []
  def edges(%__MODULE__{} = graph, source) when is_binary(source), do: Map.get(graph.edges, source, [])

  @doc "Every edge, in a stable order independent of insertion order."
  @spec to_list(t() | nil) :: [edge()]
  def to_list(nil), do: []

  def to_list(%__MODULE__{} = graph) do
    graph.edges
    |> Map.values()
    |> List.flatten()
    |> Enum.sort_by(&{&1.source, &1.target, &1.kind, inspect(&1.declaration)})
  end

  @doc "Modules `source` depends on through any checked edge."
  @spec targets(t() | nil, String.t()) :: [String.t()]
  def targets(graph, source), do: graph |> edges(source) |> Enum.map(& &1.target) |> Enum.uniq() |> Enum.sort()

  @doc "Modules that depend on `target` through any checked edge."
  @spec dependents(t() | nil, String.t()) :: [String.t()]
  def dependents(graph, target) do
    graph
    |> to_list()
    |> Enum.filter(&(&1.target == target))
    |> Enum.map(& &1.source)
    |> Enum.uniq()
    |> Enum.sort()
  end
end
