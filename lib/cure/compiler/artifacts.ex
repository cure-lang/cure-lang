defmodule Cure.Compiler.Artifacts do
  @moduledoc """
  Content integrity for Cure-generated BEAM artifact sets.

  This module is the shared boundary between incremental compilation and every
  consumer that wants to load or copy generated BEAMs. A filename is never
  freshness evidence: each artifact is identified by its bytes, BEAM module,
  exports, and optional Cure provenance attribute.
  """

  alias Cure.Compiler.Artifacts.Writer
  alias Cure.Compiler.BuildManifest

  @doc "Run the unified read-only or repairing artifact sweep."
  @spec sweep(keyword()) ::
          {:ok, Cure.Compiler.Artifacts.Result.t()} | {:error, term()}
  defdelegate sweep(opts), to: Cure.Compiler.Artifacts.Sweep, as: :run

  @doc "Artifact digest of the first verified stdlib generation visible to this process."
  @spec stdlib_fingerprint() :: binary()
  def stdlib_fingerprint do
    case open_verified_set(kind: :stdlib, candidates: Cure.Stdlib.Paths.beam_dirs()) do
      {:ok, %{artifact_digest: artifact_digest}} -> artifact_digest
      {:error, _reason} -> empty_artifact_fingerprint()
    end
  end

  @doc "Artifact digest of a verified stdlib generation rooted at `dir`."
  @spec stdlib_fingerprint(Path.t()) :: binary()
  def stdlib_fingerprint(dir) do
    case open_verified_set(dir) do
      {:ok, %{kind: :stdlib, artifact_digest: artifact_digest}} -> artifact_digest
      _ -> empty_artifact_fingerprint()
    end
  end

  @doc "Copy one already verified generation into another artifact-set root."
  @spec copy_verified_set(Path.t(), Path.t()) :: {:ok, Path.t()} | {:error, term()}
  defdelegate copy_verified_set(source_root, output_root),
    to: Cure.Compiler.Artifacts.Writer,
    as: :copy_verified

  @doc """
  Copy exactly one verified generation into an existing flat `ebin` directory.

  This is for OTP application and release layouts where BEAMs must remain
  directly under `ebin`. The destination is verified again after copying; a
  caller must not publish its enclosing package unless this function succeeds.
  """
  @spec copy_verified_flat(Path.t(), Path.t()) :: {:ok, map()} | {:error, term()}
  def copy_verified_flat(source_root, destination) do
    with {:ok, source} <- open_verified_set(source_root, verification: :full),
         :ok <- File.mkdir_p(destination),
         :ok <- copy_manifest_artifacts(source, destination),
         :ok <-
           File.cp(
             Path.join(source.artifact_root, BuildManifest.filename()),
             Path.join(destination, BuildManifest.filename())
           ),
         {:ok, copied} <- open_verified_set(destination, verification: :full),
         true <- copied.artifact_digest == source.artifact_digest do
      {:ok, copied}
    else
      false -> {:error, :copied_artifact_root_mismatch}
      {:error, _} = error -> error
    end
  end

  @doc """
  Merge complete verified sets into one flat packaged artifact set.

  The first root supplies the compiler context. Every input is verified before
  copying, duplicate module ownership is rejected, the merged manifest is
  sealed by this subsystem, and the destination is verified again.
  """
  @spec merge_verified_flat([Path.t()], Path.t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def merge_verified_flat(roots, destination, opts \\ []) when is_list(roots) and roots != [] do
    with {:ok, sets} <- open_all_verified(roots),
         {:ok, modules} <- merge_modules(sets),
         :ok <- File.mkdir_p(destination),
         :ok <- copy_sets(sets, destination) do
      primary = hd(sets)
      kind = Keyword.get(opts, :kind, :bundle)
      artifact_digests = Enum.map(sets, & &1.artifact_digest) |> Enum.sort()
      input_snapshot = digest({kind, artifact_digests})

      package_digests =
        Keyword.get_lazy(opts, :package_artifact_digests, fn ->
          sets
          |> tl()
          |> Enum.map(& &1.artifact_digest)
          |> Enum.sort()
          |> Enum.with_index(1)
          |> Map.new(fn {artifact_digest, index} -> {"dependency-#{index}", artifact_digest} end)
        end)

      manifest =
        primary
        |> Map.drop([:artifact_root])
        |> Map.merge(%{
          kind: kind,
          input_snapshot: input_snapshot,
          artifact_digest: nil,
          validated_at: filesystem_timestamp(destination),
          modules: modules,
          expected_modules: modules |> Map.keys() |> Enum.sort(),
          dependencies: %{
            stdlib: get_in(primary, [:dependencies, :stdlib]),
            packages: package_digests
          }
        })

      manifest =
        if Keyword.has_key?(opts, :package_exports) do
          exports = normalize_package_exports(Keyword.get(opts, :package_exports))

          manifest
          |> put_in([:context, :package_exports], exports)
          |> put_in([:context, :package_exports_hash], digest(exports))
        else
          manifest
        end

      :ok = BuildManifest.save(manifest, destination)

      with {:ok, copied} <- open_verified_set(destination, verification: :full),
           true <- copied.kind == kind do
        {:ok, copied}
      else
        false -> {:error, {:artifact_kind_mismatch, kind}}
        {:error, _} = error -> error
      end
    end
  end

  @type reason ::
          :manifest_entry_invalid
          | :beam_missing
          | :beam_unreadable
          | :artifact_path_invalid
          | :beam_module_mismatch
          | :artifact_hash_mismatch
          | :artifact_size_mismatch
          | :exports_hash_mismatch
          | :provenance_missing
          | :provenance_mismatch
          | :producer_snapshot_mismatch

  @type artifact :: %{
          path: String.t(),
          module: String.t(),
          sha256: binary(),
          size: non_neg_integer(),
          exports_hash: binary(),
          stat: map(),
          provenance: map(),
          producer_snapshot: binary() | nil,
          provenance_hash: binary()
        }

  @doc "Build a deterministic integrity record for one BEAM."
  @spec record(Path.t(), Path.t(), keyword()) :: {:ok, artifact()} | {:error, reason()}
  def record(path, root \\ ".", opts \\ []) do
    absolute = Path.expand(path, root)

    with {:ok, stat} <- File.stat(absolute, time: :posix) do
      signature = stat_signature(stat)

      case if(Keyword.get(opts, :verification, :cached) == :full,
             do: :miss,
             else: cached_record(absolute, signature)
           ) do
        {:ok, artifact} -> {:ok, artifact}
        :miss -> record_uncached(absolute, root, stat, signature)
      end
    else
      {:error, :enoent} -> {:error, :beam_missing}
      {:error, _reason} -> {:error, :beam_unreadable}
    end
  end

  @doc "Scope artifact metadata memoization to one complete sweep."
  @spec with_cache((-> result)) :: result when result: term()
  def with_cache(fun) when is_function(fun, 0) do
    key = {__MODULE__, :record_cache}
    stats_key = {__MODULE__, :hash_stats}
    previous = Process.get(key)
    previous_stats = Process.get(stats_key)
    Process.put(key, %{})
    Process.put(stats_key, %{computed: 0, reused: 0})

    try do
      fun.()
    after
      if previous, do: Process.put(key, previous), else: Process.delete(key)
      if previous_stats, do: Process.put(stats_key, previous_stats), else: Process.delete(stats_key)
    end
  end

  @doc false
  def hash_stats, do: Process.get({__MODULE__, :hash_stats}, %{computed: 0, reused: 0})

  @doc false
  @spec invalidate_paths([Path.t()], Path.t()) :: :ok
  def invalidate_paths(paths, root) do
    key = {__MODULE__, :record_cache}
    absolutes = paths |> Enum.map(&Path.expand(&1, root)) |> MapSet.new()

    case Process.get(key) do
      %{} = cache ->
        retained =
          Map.reject(cache, fn {{path, _signature}, _artifact} ->
            MapSet.member?(absolutes, path)
          end)

        Process.put(key, retained)

      _ ->
        :ok
    end

    :ok
  end

  defp record_uncached(absolute, root, stat, signature) do
    with {:ok, bytes} <- File.read(absolute),
         {:ok, module, exports, provenance} <- beam_metadata(absolute) do
      artifact = %{
        path: Path.relative_to(absolute, Path.expand(root)),
        module: Atom.to_string(module),
        sha256: :crypto.hash(:sha256, bytes),
        size: stat.size,
        stat: signature,
        exports_hash: digest(exports),
        provenance: provenance,
        producer_snapshot: if(is_map(provenance), do: Map.get(provenance, :producer_snapshot)),
        provenance_hash: digest(provenance)
      }

      increment_hash_stat(:computed)
      cache_record(absolute, signature, artifact)
      {:ok, artifact}
    else
      {:error, _reason} -> {:error, :beam_unreadable}
    end
  end

  @doc "Verify an in-memory Cure BEAM before loading it into the VM."
  @spec verify_binary(binary(), module()) :: :ok | {:error, reason()}
  def verify_binary(binary, expected_module) when is_binary(binary) and is_atom(expected_module) do
    case beam_metadata({:binary, binary}) do
      {:ok, ^expected_module, _exports, provenance} when is_map(provenance) -> :ok
      {:ok, ^expected_module, _exports, _provenance} -> {:error, :provenance_missing}
      {:ok, _other, _exports, _provenance} -> {:error, :beam_module_mismatch}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Verify the exact in-memory bytes against one manifest artifact record."
  @spec verify_binary_against(binary(), artifact()) :: :ok | {:error, [reason()]}
  def verify_binary_against(binary, expected) when is_binary(binary) and is_map(expected) do
    case beam_metadata({:binary, binary}) do
      {:ok, module, exports, provenance} ->
        actual = %{
          module: Atom.to_string(module),
          sha256: :crypto.hash(:sha256, binary),
          size: byte_size(binary),
          exports_hash: digest(exports),
          provenance: provenance,
          producer_snapshot: if(is_map(provenance), do: Map.get(provenance, :producer_snapshot)),
          provenance_hash: digest(provenance)
        }

        reasons =
          []
          |> mismatch(actual.module != Map.get(expected, :module), :beam_module_mismatch)
          |> mismatch(actual.sha256 != Map.get(expected, :sha256), :artifact_hash_mismatch)
          |> mismatch(actual.size != Map.get(expected, :size), :artifact_size_mismatch)
          |> mismatch(actual.exports_hash != Map.get(expected, :exports_hash), :exports_hash_mismatch)
          |> mismatch(not is_map(actual.provenance), :provenance_missing)
          |> mismatch(
            actual.producer_snapshot != Map.get(expected, :producer_snapshot),
            :producer_snapshot_mismatch
          )
          |> mismatch(
            actual.provenance_hash != Map.get(expected, :provenance_hash),
            :provenance_mismatch
          )
          |> Enum.reverse()

        if reasons == [], do: :ok, else: {:error, reasons}

      {:error, reason} ->
        {:error, [reason]}
    end
  end

  @doc "Record every BEAM named by a module manifest entry."
  @spec record_paths([String.t()], Path.t()) :: {:ok, [artifact()]} | {:error, {String.t(), reason()}}
  def record_paths(paths, root) do
    paths
    |> Enum.sort()
    |> Enum.reduce_while({:ok, []}, fn relative, {:ok, acc} ->
      case record(relative, root) do
        {:ok, artifact} -> {:cont, {:ok, [artifact | acc]}}
        {:error, reason} -> {:halt, {:error, {relative, reason}}}
      end
    end)
    |> case do
      {:ok, artifacts} -> {:ok, Enum.reverse(artifacts)}
      error -> error
    end
  end

  @doc "Return every reason an artifact no longer matches its recorded bytes."
  @spec verify_artifact(map(), Path.t(), keyword()) :: [reason()]
  def verify_artifact(expected, root, opts \\ [])

  def verify_artifact(expected, root, opts) when is_map(expected) do
    with {:ok, path} <- safe_relative_path(expected),
         {:ok, actual} <- verified_record(expected, path, root, opts) do
      []
      |> mismatch(actual.module != Map.get(expected, :module), :beam_module_mismatch)
      |> mismatch(actual.sha256 != Map.get(expected, :sha256), :artifact_hash_mismatch)
      |> mismatch(actual.size != Map.get(expected, :size), :artifact_size_mismatch)
      |> mismatch(actual.exports_hash != Map.get(expected, :exports_hash), :exports_hash_mismatch)
      |> mismatch(not is_map(actual.provenance), :provenance_missing)
      |> mismatch(
        actual.producer_snapshot != Map.get(expected, :producer_snapshot),
        :producer_snapshot_mismatch
      )
      |> mismatch(
        actual.provenance_hash != Map.get(expected, :provenance_hash),
        :provenance_mismatch
      )
      |> Enum.reverse()
    else
      {:error, reason} -> [reason]
    end
  rescue
    KeyError -> [:manifest_entry_invalid]
  end

  def verify_artifact(_expected, _root, _opts), do: [:manifest_entry_invalid]

  @doc "Verify every artifact in one module entry."
  @spec verify_entry(map(), Path.t(), keyword()) :: [reason()]
  def verify_entry(entry, root, opts \\ [])

  def verify_entry(entry, root, opts) when is_map(entry) do
    case Map.get(entry, :artifacts) do
      artifacts when is_list(artifacts) and artifacts != [] ->
        artifacts
        |> Enum.flat_map(&verify_artifact(&1, root, opts))
        |> Enum.uniq()

      _ ->
        [:manifest_entry_invalid]
    end
  end

  def verify_entry(_entry, _root, _opts), do: [:manifest_entry_invalid]

  @doc "Verify a complete manifest and reject unclaimed Cure BEAMs."
  @spec verify_manifest(map(), Path.t(), keyword()) :: :ok | {:error, map()}
  def verify_manifest(manifest, root, opts \\ []) when is_map(manifest) do
    opts =
      opts
      |> Keyword.put_new(:verification, :full)
      |> Keyword.put_new(:validated_at, Map.get(manifest, :validated_at))

    module_failures =
      manifest
      |> Map.get(:modules, %{})
      |> Enum.reduce(%{}, fn {name, entry}, acc ->
        reasons =
          verify_entry(entry, root, opts) ++
            verify_entry_provenance(name, entry, manifest)

        case Enum.uniq(reasons) do
          [] -> acc
          reasons -> Map.put(acc, name, reasons)
        end
      end)

    artifact_paths =
      manifest
      |> Map.get(:modules, %{})
      |> Map.values()
      |> Enum.flat_map(&Map.get(&1, :artifacts, []))
      |> Enum.map(&Map.get(&1, :path))

    claimed = artifact_paths |> Enum.filter(&is_binary/1) |> MapSet.new()

    duplicate_ownership =
      artifact_paths
      |> Enum.filter(&is_binary/1)
      |> Enum.frequencies()
      |> Enum.filter(fn {_path, count} -> count > 1 end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.sort()

    invalid_paths =
      artifact_paths
      |> Enum.reject(fn path -> match?({:ok, _}, safe_relative_path(%{path: path})) end)
      |> Enum.sort()

    discovered =
      root
      |> Path.join(discovery_glob(Map.get(manifest, :kind), root))
      |> Path.wildcard()
      |> Enum.map(&Path.relative_to(&1, root))
      |> MapSet.new()

    orphans = MapSet.difference(discovered, claimed) |> MapSet.to_list() |> Enum.sort()
    root_valid? = BuildManifest.valid_digest?(manifest)
    expected_modules = Map.get(manifest, :expected_modules)
    actual_modules = manifest |> Map.get(:modules, %{}) |> Map.keys() |> Enum.sort()
    complete? = is_list(expected_modules) and Enum.sort(expected_modules) == actual_modules

    if module_failures == %{} and orphans == [] and root_valid? and
         duplicate_ownership == [] and invalid_paths == [] and complete? do
      :ok
    else
      {:error,
       %{
         modules: module_failures,
         orphans: orphans,
         duplicate_ownership: duplicate_ownership,
         invalid_paths: invalid_paths,
         incomplete_module_set: not complete?,
         artifact_digest_mismatch: not root_valid?
       }}
    end
  rescue
    _ ->
      {:error,
       %{
         modules: %{},
         orphans: [],
         duplicate_ownership: [],
         invalid_paths: [],
         incomplete_module_set: true,
         artifact_digest_mismatch: false,
         manifest_invalid: true
       }}
  end

  @doc """
  Open one complete verified artifact set.

  A path verifies that exact root. A keyword list with `:candidates` selects
  the first complete valid root and never combines files across directories.
  """
  @spec open_verified_set(Path.t() | keyword()) :: {:ok, map()} | {:error, term()}
  def open_verified_set(root_or_opts)

  def open_verified_set(root) when is_binary(root) do
    open_verified_set(root, verification: :cached)
  end

  def open_verified_set(opts) when is_list(opts) do
    candidates = Keyword.fetch!(opts, :candidates)
    expected_kind = Keyword.get(opts, :kind)
    verification = Keyword.get(opts, :verification, :cached)

    failures =
      Enum.reduce_while(candidates, [], fn root, failures ->
        case open_verified_set(root, verification: verification) do
          {:ok, manifest} ->
            if is_nil(expected_kind) or manifest.kind == expected_kind do
              {:halt, {:ok, manifest}}
            else
              {:cont, [{root, {:artifact_kind_mismatch, manifest.kind}} | failures]}
            end

          {:error, reason} ->
            {:cont, [{root, reason} | failures]}
        end
      end)

    case failures do
      {:ok, manifest} -> {:ok, manifest}
      failures -> {:error, {:no_verified_artifact_set, Enum.reverse(failures)}}
    end
  end

  @spec open_verified_set(Path.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def open_verified_set(root, opts) when is_binary(root) and is_list(opts) do
    root = Writer.resolve(root)

    with {:ok, manifest} <- BuildManifest.read(root),
         true <- map_size(manifest.modules) > 0,
         :ok <- verify_manifest(manifest, root, opts) do
      {:ok, Map.put(manifest, :artifact_root, Path.expand(root))}
    else
      false -> {:error, :artifact_manifest_empty}
      {:error, details} when is_map(details) -> {:error, {:artifact_set_invalid, details}}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Verify a complete set, then load all of its claimed BEAMs."
  @spec load_verified_set(Path.t()) :: :ok | {:error, term()}
  def load_verified_set(root) do
    with {:ok, set} <- open_verified_set(root),
         artifacts <- sorted_artifacts(set),
         :ok <- preflight_loaded_artifacts(artifacts, set.artifact_root) do
      Enum.reduce_while(artifacts, :ok, fn artifact, :ok ->
        module = String.to_existing_atom(artifact.module)
        path = Path.join(set.artifact_root, artifact.path)

        case :code.is_loaded(module) do
          {:file, _} ->
            {:cont, :ok}

          false ->
            with {:ok, binary} <- File.read(path),
                 :ok <- verify_binary_against(binary, artifact),
                 {:module, ^module} <-
                   :code.load_binary(module, String.to_charlist(path), binary) do
              {:cont, :ok}
            else
              reason -> {:halt, {:error, {:artifact_load_failed, module, reason}}}
            end
        end
      end)
    end
  end

  @doc "Verify one complete set, then load only the requested resident modules."
  @spec load_verified_modules(Path.t(), [module()]) :: :ok | {:error, term()}
  def load_verified_modules(root, modules) when is_list(modules) do
    with {:ok, set} <- open_verified_set(root) do
      wanted = modules |> MapSet.new(&Atom.to_string/1)

      artifacts =
        set
        |> sorted_artifacts()
        |> Enum.filter(&MapSet.member?(wanted, &1.module))

      found = artifacts |> Enum.map(& &1.module) |> MapSet.new()

      if MapSet.equal?(wanted, found) do
        load_recorded_artifacts(artifacts, set.artifact_root)
      else
        {:error, {:artifact_modules_missing, MapSet.difference(wanted, found) |> MapSet.to_list()}}
      end
    end
  end

  @doc false
  @spec load_recorded_artifacts([artifact()], Path.t()) :: :ok | {:error, term()}
  def load_recorded_artifacts(artifacts, root) do
    with :ok <- verify_recorded_artifacts(artifacts, root),
         :ok <- preflight_replaceable_artifacts(artifacts, root) do
      Enum.reduce_while(artifacts, :ok, fn artifact, :ok ->
        module = String.to_existing_atom(artifact.module)
        path = Path.join(root, artifact.path)

        with {:ok, binary} <- File.read(path),
             :ok <- verify_binary_against(binary, artifact),
             :ok <- load_or_keep_recorded(module, path, binary) do
          {:cont, :ok}
        else
          reason -> {:halt, {:error, {:artifact_load_failed, module, reason}}}
        end
      end)
    end
  end

  defp verify_recorded_artifacts(artifacts, root) do
    Enum.reduce_while(artifacts, :ok, fn artifact, :ok ->
      case verify_artifact(artifact, root) do
        [] -> {:cont, :ok}
        reasons -> {:halt, {:error, {:artifact_verification_failed, artifact.path, reasons}}}
      end
    end)
  end

  defp preflight_replaceable_artifacts(artifacts, root) do
    Enum.reduce_while(artifacts, :ok, fn artifact, :ok ->
      module = String.to_existing_atom(artifact.module)
      path = Path.join(root, artifact.path)

      if :code.is_sticky(module) and match?({:file, _}, :code.is_loaded(module)) do
        with {:ok, {^module, disk_md5}} <- :beam_lib.md5(String.to_charlist(path)) do
          if module.module_info(:md5) == disk_md5,
            do: {:cont, :ok},
            else: {:halt, {:error, {:resident_artifact_mismatch, module}}}
        else
          _ -> {:halt, {:error, {:artifact_unreadable, module}}}
        end
      else
        {:cont, :ok}
      end
    end)
  end

  defp sorted_artifacts(set) do
    set.modules
    |> Map.values()
    |> Enum.flat_map(&Map.get(&1, :artifacts, []))
    |> Enum.sort_by(& &1.path)
  end

  defp preflight_loaded_artifacts(artifacts, root) do
    Enum.reduce_while(artifacts, :ok, fn artifact, :ok ->
      module = String.to_existing_atom(artifact.module)
      path = Path.join(root, artifact.path)

      case :code.is_loaded(module) do
        {:file, _} ->
          with {:ok, {^module, disk_md5}} <- :beam_lib.md5(String.to_charlist(path)) do
            if module.module_info(:md5) == disk_md5 do
              {:cont, :ok}
            else
              {:halt, {:error, {:resident_artifact_mismatch, module}}}
            end
          else
            _ -> {:halt, {:error, {:artifact_unreadable, module}}}
          end

        false ->
          {:cont, :ok}
      end
    end)
  end

  defp maybe_evict_loaded(module, _path) do
    case :code.is_loaded(module) do
      false ->
        :ok

      {:file, _} ->
        :code.purge(module)
        :code.delete(module)
        :ok
    end
  end

  defp load_or_keep_recorded(module, path, binary) do
    case :code.is_loaded(module) do
      {:file, _} ->
        with {:ok, {^module, disk_md5}} <- :beam_lib.md5(String.to_charlist(path)) do
          if module.module_info(:md5) == disk_md5 do
            :ok
          else
            with :ok <- maybe_evict_loaded(module, path),
                 {:module, ^module} <-
                   :code.load_binary(module, String.to_charlist(path), binary) do
              :ok
            end
          end
        end

      false ->
        case :code.load_binary(module, String.to_charlist(path), binary) do
          {:module, ^module} -> :ok
          error -> error
        end
    end
  end

  defp copy_manifest_artifacts(source, destination) do
    source
    |> sorted_artifacts()
    |> Enum.reduce_while(:ok, fn artifact, :ok ->
      source_path = Path.join(source.artifact_root, artifact.path)
      destination_path = Path.join(destination, artifact.path)

      case File.cp(source_path, destination_path) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:artifact_copy_failed, artifact.path, reason}}}
      end
    end)
  end

  defp open_all_verified(roots) do
    Enum.reduce_while(roots, {:ok, []}, fn root, {:ok, sets} ->
      case open_verified_set(root, verification: :full) do
        {:ok, set} -> {:cont, {:ok, [set | sets]}}
        {:error, reason} -> {:halt, {:error, {:artifact_set_invalid, root, reason}}}
      end
    end)
    |> case do
      {:ok, sets} -> {:ok, Enum.reverse(sets)}
      error -> error
    end
  end

  defp merge_modules(sets) do
    Enum.reduce_while(sets, {:ok, %{}}, fn set, {:ok, modules} ->
      duplicates = Map.keys(set.modules) |> Enum.filter(&Map.has_key?(modules, &1))

      if duplicates == [] do
        {:cont, {:ok, Map.merge(modules, set.modules)}}
      else
        {:halt, {:error, {:duplicate_artifact_modules, Enum.sort(duplicates)}}}
      end
    end)
  end

  defp copy_sets(sets, destination) do
    destination = Path.expand(destination)

    sets
    |> Enum.flat_map(fn set ->
      beams =
        for entry <- Map.values(set.modules),
            artifact <- Map.fetch!(entry, :artifacts),
            do: {set.artifact_root, artifact.path}

      interfaces =
        set.artifact_root
        |> Path.join("*.cureinterface")
        |> Path.wildcard()
        |> Enum.map(&{set.artifact_root, Path.basename(&1)})

      beams ++ interfaces
    end)
    |> Enum.reduce_while(:ok, fn {root, path}, :ok ->
      source = Path.join(root, path)
      target = Path.join(destination, path)

      if Path.expand(source) == Path.expand(target) do
        {:cont, :ok}
      else
        case File.cp(source, target) do
          :ok -> {:cont, :ok}
          {:error, reason} -> {:halt, {:error, {:artifact_copy_failed, path, reason}}}
        end
      end
    end)
  end

  defp normalize_package_exports(exports) when is_map(exports) do
    exports
    |> Enum.map(fn {package, modules} ->
      {to_string(package), modules |> List.wrap() |> Enum.map(&to_string/1) |> Enum.uniq() |> Enum.sort()}
    end)
    |> Map.new()
  end

  defp normalize_package_exports(_exports), do: %{}

  defp discovery_glob(kind, root) do
    if Path.basename(Path.dirname(Path.expand(root))) == ".cure_generations",
      do: "*.beam",
      else: flat_discovery_glob(kind)
  end

  defp flat_discovery_glob(:stdlib), do: "Cure.Std.*.beam"
  defp flat_discovery_glob(_kind), do: "Cure.*.beam"

  defp safe_relative_path(%{path: path}) when is_binary(path) do
    expanded = Path.expand(path, "/artifact-root")

    if Path.type(path) == :relative and
         (expanded == "/artifact-root" or String.starts_with?(expanded, "/artifact-root/")) and
         Path.basename(path) == path do
      {:ok, path}
    else
      {:error, :artifact_path_invalid}
    end
  end

  defp safe_relative_path(_), do: {:error, :artifact_path_invalid}

  defp verify_entry_provenance(name, entry, manifest) do
    entry
    |> Map.get(:artifacts, [])
    |> Enum.flat_map(fn artifact ->
      provenance = Map.get(artifact, :provenance)

      cond do
        not is_map(provenance) ->
          [:provenance_missing]

        Map.get(provenance, :source_hash) != get_in(entry, [:source, :sha256]) ->
          [:provenance_mismatch]

        manifest.kind not in [:bundle, :release] and
            Map.get(provenance, :compiler_hash) != get_in(manifest, [:context, :compiler_hash]) ->
          [:provenance_mismatch]

        not provenance_module_owned?(Map.get(provenance, :module), name) ->
          [:provenance_mismatch]

        true ->
          []
      end
    end)
  end

  defp provenance_module_owned?(emitted, source_module) when is_binary(emitted) do
    emitted = String.replace_prefix(emitted, "Cure.", "")
    emitted == source_module or String.starts_with?(emitted, source_module <> ".")
  end

  defp provenance_module_owned?(_, _), do: false

  defp cached_record(path, signature) do
    case Process.get({__MODULE__, :record_cache}) do
      %{} = cache -> Map.get(cache, {path, signature}, :miss)
      _ -> :miss
    end
  end

  defp cache_record(path, signature, artifact) do
    key = {__MODULE__, :record_cache}

    case Process.get(key) do
      %{} = cache -> Process.put(key, Map.put(cache, {path, signature}, {:ok, artifact}))
      _ -> :ok
    end
  end

  defp verified_record(expected, path, root, opts) do
    verification = Keyword.get(opts, :verification, :cached)
    validated_at = Keyword.get(opts, :validated_at)
    absolute = Path.expand(path, root)

    with :cached <- verification,
         expected_stat when is_map(expected_stat) <- Map.get(expected, :stat),
         {:ok, stat} <- File.stat(absolute, time: :posix),
         actual_stat <- stat_signature(stat),
         true <- actual_stat == expected_stat,
         true <- timestamp_safe?(actual_stat, validated_at) do
      increment_hash_stat(:reused)
      {:ok, expected}
    else
      _ -> record(path, root, verification: :full)
    end
  end

  defp timestamp_safe?(%{mtime: mtime, ctime: ctime}, validated_at)
       when is_integer(validated_at),
       do: max(mtime, ctime) < validated_at

  defp timestamp_safe?(_stat, _validated_at), do: false

  @doc false
  def stat_signature(%File.Stat{} = stat) do
    %{
      device: {stat.major_device, stat.minor_device},
      inode: stat.inode,
      size: stat.size,
      mtime: stat.mtime,
      ctime: stat.ctime
    }
  end

  @doc false
  @spec record_source(Path.t(), map() | nil, integer() | nil, keyword()) :: map()
  def record_source(path, expected \\ nil, validated_at \\ nil, opts \\ []) do
    stat = path |> File.stat!(time: :posix) |> stat_signature()
    verification = Keyword.get(opts, :verification, :cached)

    if verification == :cached and is_map(expected) and Map.get(expected, :stat) == stat and
         timestamp_safe?(stat, validated_at) do
      increment_hash_stat(:reused)
      expected
    else
      increment_hash_stat(:computed)

      %{
        path: path,
        sha256: path |> File.read!() |> then(&:crypto.hash(:sha256, &1)),
        stat: stat
      }
    end
  end

  @doc false
  def filesystem_timestamp(root) do
    File.mkdir_p!(root)
    path = Path.join(root, ".cure_timestamp_#{System.unique_integer([:positive, :monotonic])}")
    File.write!(path, <<>>, [:sync])

    try do
      File.stat!(path, time: :posix).mtime
    after
      File.rm(path)
    end
  end

  defp increment_hash_stat(field) do
    key = {__MODULE__, :hash_stats}

    case Process.get(key) do
      %{} = stats -> Process.put(key, Map.update!(stats, field, &(&1 + 1)))
      _ -> :ok
    end
  end

  defp mismatch(reasons, true, reason), do: [reason | reasons]
  defp mismatch(reasons, false, _reason), do: reasons

  defp digest(term), do: :crypto.hash(:sha256, :erlang.term_to_binary(term, [:deterministic]))

  defp beam_metadata({:binary, binary}) when is_binary(binary), do: beam_metadata_input(binary)
  defp beam_metadata(path) when is_binary(path), do: beam_metadata_input(String.to_charlist(path))

  defp beam_metadata_input(input) do
    case :beam_lib.chunks(input, [:exports, :attributes]) do
      {:ok, {module, chunks}} ->
        exports = chunks |> Keyword.get(:exports, []) |> Enum.sort()

        provenance =
          chunks
          |> Keyword.get(:attributes, [])
          |> Keyword.get(:cure_artifact)
          |> unwrap_attribute()

        {:ok, module, exports, provenance}

      {:error, _module, _reason} ->
        {:error, :beam_unreadable}

      {:error, _reason} ->
        {:error, :beam_unreadable}
    end
  end

  defp unwrap_attribute([value]) when is_map(value), do: value
  defp unwrap_attribute(value) when is_map(value), do: value
  defp unwrap_attribute(_), do: nil

  defp empty_artifact_fingerprint do
    :crypto.hash(:sha256, :erlang.term_to_binary([], [:deterministic]))
  end
end
