defmodule Cure.Compiler.BuildManifest do
  @moduledoc """
  Persisted fingerprint store for incremental Cure compilation.

  Version 3 gives the three hashes in an incremental build distinct jobs:

  * `workspace_key` names the immutable compiler/build configuration;
  * `input_snapshot` names the exact source and dependency inputs;
  * `artifact_digest` seals the complete emitted artifact set.

  An invalid artifact digest is never accepted as a fresh build.
  """

  @manifest_version 3
  @filename ".cure_manifest"

  # The standalone escript does not ship Mix, and its embedded BEAM files do
  # not have ordinary filesystem paths. Embed one deterministic identity for
  # every Cure compiler source and build-definition input instead. Declaring
  # them as external resources ensures this module is recompiled whenever any
  # of those inputs changes.
  @toolchain_inputs (Path.wildcard(Path.expand("../../**/*.{ex,exs}", __DIR__)) ++
                       [
                         Path.expand("../../../mix.exs", __DIR__),
                         Path.expand("../../../mix.lock", __DIR__)
                       ])
                    |> Enum.filter(&File.regular?/1)
                    |> Enum.uniq()
                    |> Enum.sort()

  for path <- @toolchain_inputs do
    @external_resource path
  end

  @toolchain_fingerprint @toolchain_inputs
                         |> Enum.map(fn path ->
                           {Path.relative_to(path, Path.expand("../../..", __DIR__)), File.read!(path)}
                         end)
                         |> :erlang.term_to_binary([:deterministic])
                         |> then(&:crypto.hash(:sha256, &1))
  # `binary_to_term(..., [:safe])` refuses atoms that do not already exist in
  # the VM. Keeping the complete closed schema here interns every on-disk key
  # and enum value when this module loads, while module names and paths remain
  # binaries and therefore cannot grow the atom table.
  @manifest_atoms [
    :version,
    :modules,
    :expected_modules,
    :workspace_key,
    :input_snapshot,
    :artifact_digest,
    :validated_at,
    :kind,
    :context,
    :dependencies,
    :dependency_interface_hashes,
    :source,
    :stat,
    :device,
    :inode,
    :mtime,
    :ctime,
    :edges,
    :compile_order,
    :interface,
    :runtime,
    :source_path,
    :source_hash,
    :interface_hash,
    :deps,
    :compile_dependencies,
    :runtime_dependencies,
    :beams,
    :artifacts,
    :path,
    :module,
    :sha256,
    :size,
    :exports_hash,
    :provenance,
    :producer_snapshot,
    :provenance_hash,
    :compiler_hash,
    :warning_count,
    :language_edition,
    :otp_release,
    :elixir_version,
    :target,
    :codegen_options_hash,
    :source_roots_hash,
    :package,
    :package_exports,
    :package_exports_hash,
    :stdlib,
    :packages,
    :format,
    :unknown,
    :project,
    :stdlib,
    :dependency,
    :bundle,
    :release,
    :beam
  ]
  @type stat_signature :: %{
          optional(:device) => non_neg_integer() | nil,
          optional(:inode) => non_neg_integer() | nil,
          size: non_neg_integer(),
          mtime: integer(),
          ctime: integer()
        }
  @type entry :: %{
          source: %{path: String.t(), sha256: binary(), stat: stat_signature()},
          warning_count: non_neg_integer(),
          interface_hash: binary() | nil,
          edges: %{compile_order: [String.t()], interface: [String.t()], runtime: [String.t()]},
          artifacts: [map()]
        }
  @type t :: %{
          version: pos_integer(),
          workspace_key: binary(),
          input_snapshot: binary() | nil,
          artifact_digest: binary() | nil,
          validated_at: integer() | nil,
          modules: %{String.t() => entry()},
          expected_modules: [String.t()],
          kind: atom(),
          context: map(),
          dependencies: map()
        }

  @spec empty(binary()) :: t()
  def empty(workspace_key) when is_binary(workspace_key),
    do: %{
      version: @manifest_version,
      workspace_key: workspace_key,
      input_snapshot: nil,
      artifact_digest: nil,
      validated_at: nil,
      modules: %{},
      expected_modules: [],
      kind: :unknown,
      context: %{},
      dependencies: %{stdlib: nil, packages: %{}}
    }

  @doc "Read and validate a version-3 manifest without hiding its failure reason."
  @spec read(String.t()) :: {:ok, t()} | {:error, atom()}
  def read(output_dir) do
    path = output_dir |> resolve_published_root() |> Path.join(@filename)

    case File.read(path) do
      {:ok, bin} ->
        with {:ok, term} <- safe_decode(bin),
             :ok <- validate_shape(term),
             true <- valid_digest?(term) do
          {:ok, normalize(term)}
        else
          :error -> {:error, :manifest_invalid}
          {:error, reason} -> {:error, reason}
          false -> {:error, :manifest_digest_mismatch}
        end

      {:error, :enoent} ->
        {:error, :manifest_missing}

      {:error, _reason} ->
        {:error, :manifest_unreadable}
    end
  end

  @spec load(String.t()) :: t()
  def load(output_dir) do
    case read(output_dir) do
      {:ok, manifest} -> manifest
      {:error, _reason} -> empty("")
    end
  end

  @spec save(t(), String.t()) :: :ok
  def save(manifest, output_dir) do
    manifest = manifest |> normalize() |> seal()
    File.mkdir_p!(output_dir)
    final = Path.join(output_dir, @filename)
    tmp = final <> ".tmp"
    File.write!(tmp, :erlang.term_to_binary(manifest, [:deterministic]))
    File.rename!(tmp, final)
    :ok
  end

  @doc "Seal a manifest with its deterministic artifact digest."
  @spec seal(t()) :: t()
  def seal(manifest) do
    Map.put(manifest, :artifact_digest, artifact_digest(manifest))
  end

  @doc "Compute the deterministic artifact digest without its self-reference."
  @spec artifact_digest(map()) :: binary()
  def artifact_digest(manifest) when is_map(manifest) do
    manifest
    |> Map.put(:artifact_digest, nil)
    |> Map.put(:validated_at, nil)
    |> strip_stat_metadata()
    |> :erlang.term_to_binary([:deterministic])
    |> then(&:crypto.hash(:sha256, &1))
  end

  @doc "Whether the recorded artifact digest matches the manifest contents."
  @spec valid_digest?(map()) :: boolean()
  def valid_digest?(%{artifact_digest: nil, modules: modules})
      when map_size(modules) == 0,
      do: true

  def valid_digest?(%{artifact_digest: digest} = manifest) when is_binary(digest),
    do: digest == artifact_digest(manifest)

  def valid_digest?(_), do: false

  @doc "The manifest filename shared by every artifact-set consumer."
  @spec filename() :: String.t()
  def filename, do: @filename

  @doc "SHA-256 over the compiler source and build-definition inputs embedded at build time."
  @spec toolchain_fingerprint() :: binary()
  def toolchain_fingerprint, do: @toolchain_fingerprint

  @doc false
  @spec semantic_toolchain_beam?(Path.t()) :: boolean()
  def semantic_toolchain_beam?(_path), do: true

  defp safe_decode(bin) do
    # Keep this runtime traversal: assigning the literal to an unused variable
    # is optimized away, leaving newer schema atoms absent from a fresh VM and
    # making the safe decoder reject our own manifest.
    Enum.each(@manifest_atoms, &:erlang.atom_to_binary(&1))
    {:ok, :erlang.binary_to_term(bin, [:safe])}
  rescue
    _ -> :error
  end

  defp validate_shape(%{
         version: @manifest_version,
         workspace_key: workspace_key,
         input_snapshot: input_snapshot,
         artifact_digest: artifact_digest,
         validated_at: validated_at,
         modules: modules,
         expected_modules: expected_modules,
         kind: kind,
         context: context,
         dependencies: dependencies
       })
       when is_binary(workspace_key) and is_map(modules) and
              (is_binary(input_snapshot) or is_nil(input_snapshot)) and
              (is_binary(artifact_digest) or is_nil(artifact_digest)) and
              (is_integer(validated_at) or is_nil(validated_at)) do
    valid? =
      kind in [:unknown, :project, :stdlib, :dependency, :bundle, :release] and
        is_map(context) and is_map(dependencies) and
        Map.has_key?(dependencies, :stdlib) and is_map(Map.get(dependencies, :packages)) and
        is_list(expected_modules) and Enum.all?(expected_modules, &is_binary/1) and
        Enum.all?(modules, fn {name, entry} -> is_binary(name) and valid_entry?(entry) end)

    if valid?, do: :ok, else: {:error, :manifest_invalid}
  end

  defp validate_shape(%{version: version}) when version != @manifest_version,
    do: {:error, :manifest_version_unsupported}

  defp validate_shape(_), do: {:error, :manifest_invalid}

  defp valid_entry?(entry) when is_map(entry) do
    valid_source?(Map.get(entry, :source)) and
      (is_binary(Map.get(entry, :interface_hash)) or is_nil(Map.get(entry, :interface_hash))) and
      valid_edges?(Map.get(entry, :edges)) and
      is_list(Map.get(entry, :artifacts)) and
      Map.get(entry, :artifacts) != [] and
      Enum.all?(Map.get(entry, :artifacts), &valid_artifact?/1) and
      valid_warning_count?(Map.get(entry, :warning_count, 0))
  end

  defp valid_entry?(_), do: false

  defp valid_artifact?(artifact) when is_map(artifact) do
    is_binary(Map.get(artifact, :path)) and
      is_binary(Map.get(artifact, :module)) and
      is_binary(Map.get(artifact, :sha256)) and
      is_integer(Map.get(artifact, :size)) and Map.get(artifact, :size) >= 0 and
      valid_stat?(Map.get(artifact, :stat)) and
      is_binary(Map.get(artifact, :exports_hash)) and
      is_map(Map.get(artifact, :provenance)) and
      is_binary(Map.get(artifact, :provenance_hash)) and
      (is_binary(Map.get(artifact, :producer_snapshot)) or
         is_nil(Map.get(artifact, :producer_snapshot)))
  end

  defp valid_artifact?(_), do: false

  defp string_list?(values), do: is_list(values) and Enum.all?(values, &is_binary/1)
  defp valid_warning_count?(count), do: is_integer(count) and count >= 0

  defp valid_source?(%{path: path, sha256: sha256, stat: stat}),
    do: is_binary(path) and is_binary(sha256) and valid_stat?(stat)

  defp valid_source?(_), do: false

  defp valid_edges?(%{compile_order: order, interface: interface, runtime: runtime}),
    do: string_list?(order) and string_list?(interface) and string_list?(runtime)

  defp valid_edges?(_), do: false

  defp valid_stat?(%{size: size, mtime: mtime, ctime: ctime}),
    do: is_integer(size) and size >= 0 and is_integer(mtime) and is_integer(ctime)

  defp valid_stat?(_), do: false

  defp normalize(term), do: empty(Map.fetch!(term, :workspace_key)) |> Map.merge(term)

  defp strip_stat_metadata(%{} = map) do
    map
    |> Map.delete(:stat)
    |> Map.new(fn {key, value} -> {key, strip_stat_metadata(value)} end)
  end

  defp strip_stat_metadata(values) when is_list(values), do: Enum.map(values, &strip_stat_metadata/1)
  defp strip_stat_metadata(value), do: value

  defp resolve_published_root(output_dir) do
    with {:ok, generation} <- File.read(Path.join(output_dir, "current")),
         generation = String.trim(generation),
         true <- String.match?(generation, ~r/\A[0-9a-f]{64}\z/),
         root = Path.join([output_dir, ".cure_generations", generation]),
         true <- File.dir?(root) do
      root
    else
      _ -> output_dir
    end
  end
end
