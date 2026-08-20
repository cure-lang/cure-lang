defmodule Cure.Compiler.ModuleInterface do
  @moduledoc """
  Immutable semantic interface for one checked Cure module.

  Interface identity includes the compiler schema, canonical module identity,
  exported declarations, and extension payloads. Dependency-interface
  identities are validation metadata rather than part of this module's public
  identity. Keeping those hashes separate is essential for cyclic interface
  graphs: recursively embedding dependency hashes cannot reach a cryptographic
  fixed point. Source content likewise has its own hash for cache invalidation,
  but does not perturb semantic identity when an edit changes only comments or
  formatting. Transitional callers may still retain an `export_env`, but it is
  deliberately excluded from semantic identity.
  """

  # Version 2 introduced the checked-module handoff: `owned_env` is the exact
  # certified environment and `export_env` is its canonical consumer
  # projection. Version 3 separates dependency-validation hashes from a
  # module's own public identity so cyclic interface graphs converge. Version 4
  # separates checked totality from permission to δ-unfold a published body.
  # Version 5 publishes body-hash-keyed direct-call summaries and atomic SCC
  # certificate identities for Agda-style incremental totality checking.
  # Version 8 retains diagnostic call-site/macro provenance in direct summaries
  # while excluding it from semantic interface identity.
  @schema_version 8

  @enforce_keys [
    :module_name,
    :source_path,
    :source_hash,
    :dependency_interface_hashes,
    :interface_hash
  ]
  defstruct schema_version: @schema_version,
            module_name: nil,
            source_path: nil,
            # Transitional compatibility aliases. New consumers use
            # `source_path`, `direct_edges`, and dependency hashes.
            path: nil,
            source_hash: nil,
            dependency_interface_hashes: %{},
            dependency_names: [],
            interface_hash: nil,
            direct_edges: [],
            canonical_declarations: %{},
            canonical_externs: %{},
            extension_payloads: %{},
            runtime_artifact: nil,
            compiletime_artifact: nil,
            source_metadata: %{},
            owned_env: nil,
            direct_import_names: MapSet.new(),
            export_env: nil

  @type t :: %__MODULE__{}

  @spec schema_version() :: pos_integer()
  def schema_version, do: @schema_version

  @spec new(keyword() | map()) :: t()
  def new(attrs) when is_list(attrs), do: attrs |> Map.new() |> new()

  def new(attrs) when is_map(attrs) do
    module_name = Map.fetch!(attrs, :module_name)
    source_path = attrs |> Map.fetch!(:source_path) |> Path.expand()
    source_hash = Map.fetch!(attrs, :source_hash)
    dependency_hashes = normalize_hashes(Map.get(attrs, :dependency_interface_hashes, %{}))
    declarations = Map.get(attrs, :canonical_declarations, %{})
    externs = Map.get(attrs, :canonical_externs, %{})
    extensions = Map.get(attrs, :extension_payloads, %{})
    direct_edges = Map.get(attrs, :direct_edges, [])

    identity = %{
      schema_version: @schema_version,
      module_name: module_name,
      # Locations belong to the diagnostic projection, not semantic identity:
      # inserting a comment before an unchanged dependency must not force every
      # dependent module to rebuild.
      direct_edges: semantic_edges(direct_edges),
      canonical_declarations: semantic_declarations(declarations),
      canonical_externs: externs,
      extension_payloads: extensions
    }

    struct!(
      __MODULE__,
      attrs
      |> Map.put(:schema_version, @schema_version)
      |> Map.put(:module_name, module_name)
      |> Map.put(:source_path, source_path)
      |> Map.put(:path, source_path)
      |> Map.put(:source_hash, source_hash)
      |> Map.put(:dependency_interface_hashes, dependency_hashes)
      |> Map.put(:direct_edges, normalize_edges(direct_edges))
      |> Map.put(:canonical_declarations, declarations)
      |> Map.put(:canonical_externs, externs)
      |> Map.put(:extension_payloads, extensions)
      |> Map.put(:interface_hash, semantic_hash(identity))
    )
  end

  @spec validate(t()) :: :ok | {:error, term()}
  def validate(%__MODULE__{schema_version: version}) when version != @schema_version,
    do: {:error, {:module_interface_schema_incompatible, version, @schema_version}}

  def validate(%__MODULE__{} = interface) do
    rebuilt =
      interface
      |> Map.from_struct()
      |> Map.delete(:interface_hash)
      |> new()

    if rebuilt.interface_hash == interface.interface_hash,
      do: :ok,
      else: {:error, {:module_interface_hash_mismatch, interface.module_name, interface.source_path}}
  end

  def validate(other), do: {:error, {:module_interface_corrupt, other}}

  @spec semantic_hash(term()) :: binary()
  def semantic_hash(term),
    do: :crypto.hash(:sha256, :erlang.term_to_binary(term, [:deterministic]))

  defp normalize_hashes(hashes), do: hashes |> Enum.sort_by(&elem(&1, 0)) |> Map.new()

  defp normalize_edges(edges) do
    Enum.sort_by(edges, fn edge ->
      {Map.fetch!(edge, :target), Map.fetch!(edge, :kind), Map.get(edge, :line, 1)}
    end)
  end

  defp semantic_edges(edges) do
    edges
    |> Enum.map(&Map.take(&1, [:kind, :package, :target]))
    |> Enum.uniq()
    |> Enum.sort_by(&{&1.target, &1.kind})
  end

  defp semantic_declarations(declarations) do
    Map.update(declarations, :direct_call_summaries, %{}, fn summaries ->
      Map.new(summaries, fn {name, summary} ->
        {name, Cure.Core.Certificate.semantic_summary(summary)}
      end)
    end)
  end
end
