defmodule Cure.Compiler.Artifacts.Sweep do
  @moduledoc "The single discovery, verification, repair, and publication sweep."

  alias Cure.Compiler.Artifacts
  alias Cure.Compiler.Artifacts.Result
  alias Cure.Compiler.{BuildManifest, ModulePipeline}
  alias Cure.Compiler.Artifacts.Writer

  @spec run(keyword()) :: {:ok, Result.t()} | {:error, term()}
  def run(opts) do
    output_dir = Keyword.fetch!(opts, :output_dir)

    if Keyword.get(opts, :repair, true) do
      repair(opts, output_dir)
    else
      Artifacts.with_cache(fn -> validate(output_dir, opts) end)
    end
  end

  defp repair(opts, output_dir) do
    source_roots = opts |> Keyword.fetch!(:source_roots) |> List.wrap()

    source_paths =
      case Keyword.get(opts, :source_paths) do
        nil ->
          source_roots
          |> Enum.flat_map(&Path.wildcard(Path.join(&1, "**/*.cure")))
          |> Enum.uniq()
          |> Enum.sort()

        paths ->
          paths |> List.wrap() |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()
      end

    case Cure.Compiler.ModulePipeline.Selection.normalize(opts) do
      {:ok, :canonical} -> repair_canonical(opts, source_paths, source_roots, output_dir)
      {:error, _} = error -> error
    end
  end

  defp repair_canonical(opts, source_paths, source_roots, output_dir) do
    with {:ok, edition} <- canonical_edition(opts) do
      opts = Keyword.put(opts, :edition, edition)
      do_repair_canonical(opts, source_paths, source_roots, output_dir)
    else
      {:error, reason} ->
        target = Keyword.get(opts, :project_dir, List.first(source_paths) || "<project>")
        {:error, {:artifact_sweep_failed, [{target, {:edition_error, reason}}]}}
    end
  end

  defp do_repair_canonical(opts, source_paths, source_roots, output_dir) do
    refresh_prelude_manifest_if_needed(opts, source_roots)
    prior = canonical_prior_generation(opts, output_dir, source_roots)
    interface_roots = canonical_interface_roots(opts)
    cache = Keyword.get(opts, :cache, Path.join(output_dir, ".cure_interface_cache"))

    if not prior.reusable? and is_binary(cache), do: File.rm_rf(cache)

    request_opts =
      [
        module_pipeline: :canonical,
        entry_point: :artifact_sweep,
        kind: Keyword.get(opts, :kind, :project),
        package: Keyword.get(opts, :package, "root"),
        source_roots: source_roots,
        interface_roots: interface_roots,
        artifact_roots: prior.artifact_roots,
        cache: cache,
        products: [:beams],
        publication: nil,
        collect_diagnostics: true,
        event_sink: Keyword.get(opts, :progress)
      ]
      |> maybe_request_option(opts, :macro_execution)
      |> maybe_request_option(opts, :package_exports)
      |> maybe_request_option(opts, :prelude_set)
      |> maybe_request_option(opts, :compiler_providers)
      |> maybe_request_option(opts, :edition)
      |> maybe_request_option(opts, :compiler_options)

    with {:ok, checked} <- check_canonical_pipeline(source_paths, request_opts),
         {:ok, staged} <-
           Writer.transact(output_dir, fn stage ->
             publish_canonical_generation(stage, checked, opts, source_roots)
           end),
         {:ok, manifest} <- Artifacts.open_verified_set(staged.artifact_root, verification: :full) do
      {:ok, canonical_result(manifest, checked, prior)}
    end
  end

  defp canonical_edition(opts) do
    case Keyword.fetch(opts, :edition) do
      {:ok, edition} -> Cure.Edition.parse(edition)
      :error -> Cure.Edition.resolve(%{project_dir: Keyword.get(opts, :project_dir)})
    end
  end

  # Collected module failures are causal records, not an opaque error list.
  # Normalize them once at the artifact boundary into the long-standing sweep
  # contract consumed by CLI, Mix, project, bundle, and stdlib entry points.
  # The original reason is deliberately retained verbatim so its source
  # context, Core trace, closure path, and macro provenance reach the shared
  # diagnostic adapter unchanged.
  defp check_canonical_pipeline(source_paths, request_opts) do
    case ModulePipeline.check_entry_point(:artifact_sweep, source_paths, request_opts) do
      {:error, diagnostics} when is_list(diagnostics) ->
        {:error,
         {:artifact_sweep_failed,
          Enum.map(diagnostics, fn diagnostic ->
            {pipeline_failure_target(diagnostic), pipeline_failure_reason(diagnostic)}
          end)}}

      result ->
        result
    end
  end

  defp pipeline_failure_target(%{primary: %{span: %{path: path}}}) when is_binary(path), do: path
  defp pipeline_failure_target(%{module: module}) when is_binary(module), do: module
  defp pipeline_failure_target(_diagnostic), do: "<module-pipeline>"

  defp pipeline_failure_reason(%{reason: reason}), do: reason
  defp pipeline_failure_reason(diagnostic), do: diagnostic

  defp refresh_prelude_manifest_if_needed(opts, source_roots) do
    configured = Cure.Stdlib.Paths.source_dirs() |> Enum.map(&Path.expand/1) |> MapSet.new()

    if Keyword.get(opts, :kind, :project) == :stdlib or
         Enum.any?(source_roots, &MapSet.member?(configured, Path.expand(&1))) do
      Cure.Elab.Program.invalidate_prelude_manifest()
    end

    :ok
  end

  defp canonical_interface_roots(opts) do
    explicit = opts |> Keyword.get(:interface_roots, []) |> List.wrap()

    package_roots =
      opts
      |> Keyword.get(:package_artifact_sets, [])
      |> Enum.flat_map(fn
        {_name, %{artifact_root: root}} when is_binary(root) -> [root]
        {_name, %{root: root}} when is_binary(root) -> [root]
        {_name, root} when is_binary(root) -> [root]
        _invalid -> []
      end)

    # A dependency package is compiled against the explicit foundation roots
    # supplied by its package driver. Adding every ambient/legacy stdlib
    # directory as well would load a second provider for a module whose
    # foundation interface just changed (for example Std.Char), turning a
    # normal source edit into a duplicate-provider artifact failure. Ordinary
    # project builds retain ambient discovery because they may not have an
    # explicit foundation root.
    stdlib_roots =
      if Keyword.get(opts, :kind, :project) == :stdlib or
           (Keyword.get(opts, :kind, :project) == :dependency and explicit != []) do
        []
      else
        case Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Cure.Stdlib.Paths.beam_dirs(),
               verification: :full
             ) do
          {:ok, %{artifact_root: root}} -> [root]
          {:error, _reason} -> []
        end
      end

    (explicit ++ package_roots ++ stdlib_roots)
    |> Enum.map(&Path.expand/1)
    |> Enum.uniq()
  end

  defp canonical_prior_generation(opts, output_dir, source_roots) do
    configured = opts |> Keyword.get(:artifact_roots, []) |> List.wrap()
    current = Writer.resolve(output_dir)
    recorded = recorded_generation(current)

    {roots, reusable?, manifest, reason} =
      cond do
        Keyword.get(opts, :force, false) ->
          {configured, false, recorded, :forced}

        true ->
          case Artifacts.open_verified_set(current, verification: :full) do
            {:ok, published} ->
              case generation_mismatch(published, opts, source_roots) do
                nil -> {[published.artifact_root | configured], true, published, nil}
                mismatch -> {configured, false, published, mismatch}
              end

            {:error, _reason} ->
              {configured, false, recorded, if(recorded, do: :artifact_hash_mismatch, else: nil)}
          end
      end

    %{
      artifact_roots: roots |> Enum.map(&Path.expand/1) |> Enum.uniq(),
      reusable?: reusable?,
      manifest: manifest,
      rebuild_reason: reason,
      orphan_beams: orphan_beams(current, manifest)
    }
  end

  defp recorded_generation(root) do
    case BuildManifest.read(root) do
      {:ok, manifest} -> Map.put(manifest, :artifact_root, root)
      {:error, _reason} -> nil
    end
  end

  defp generation_mismatch(published, opts, source_roots) do
    cond do
      published.kind != Keyword.get(opts, :kind, :project) -> :compiler_context_mismatch
      published.dependencies != canonical_dependencies(opts) -> :dependency_artifact_digest_mismatch
      published.context != canonical_context(opts, source_roots) -> :compiler_context_mismatch
      true -> nil
    end
  end

  defp orphan_beams(_root, nil), do: []

  defp orphan_beams(root, manifest) do
    claimed =
      manifest.modules
      |> Map.values()
      |> Enum.flat_map(&Map.get(&1, :beams, []))
      |> MapSet.new()

    root
    |> Path.join("*.beam")
    |> Path.wildcard()
    |> Enum.map(&Path.basename/1)
    |> Enum.reject(&MapSet.member?(claimed, &1))
    |> Enum.sort()
  end

  defp publish_canonical_generation(stage, checked, opts, source_roots) do
    remove_previous_generation(stage)

    with :ok <- write_canonical_beams(stage, checked.beams),
         :ok <- ModulePipeline.write_interfaces(checked, stage),
         {:ok, modules} <- canonical_manifest_entries(stage, checked),
         :ok <-
           BuildManifest.save(
             canonical_manifest(modules, opts, source_roots, stage),
             stage
           ) do
      {:ok, %{}}
    end
  end

  defp write_canonical_beams(stage, beams) do
    Enum.reduce_while(beams, :ok, fn {module, binary}, :ok ->
      path = Path.join(stage, Atom.to_string(module) <> ".beam")

      case File.write(path, binary) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:artifact_write_failed, path, reason}}}
      end
    end)
  end

  defp canonical_manifest_entries(stage, checked) do
    checked.manifest.entries
    |> Enum.sort_by(fn {identity, _entry} -> identity end)
    |> Enum.reduce_while({:ok, %{}}, fn {identity, entry}, {:ok, modules} ->
      beam_module = String.to_existing_atom("Cure." <> entry.module_name)
      beam_path = Atom.to_string(beam_module) <> ".beam"

      with {:ok, artifact} <- Artifacts.record(beam_path, stage, verification: :full),
           {:ok, interface} <- Map.fetch(checked.interfaces, identity) do
        targets = ModulePipeline.SemanticGraph.targets(checked.semantic_graph, entry.module_name)

        module_entry = %{
          source: Artifacts.record_source(entry.source_path, nil, nil, verification: :full),
          warning_count: 0,
          interface_hash: interface.interface_hash,
          edges: %{compile_order: targets, interface: targets, runtime: targets},
          beams: [beam_path],
          artifacts: [artifact]
        }

        {:cont, {:ok, Map.put(modules, entry.module_name, module_entry)}}
      else
        :error -> {:halt, {:error, {:canonical_interface_missing, entry.module_name}}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp canonical_manifest(modules, opts, source_roots, stage) do
    context = canonical_context(opts, source_roots)

    %{
      version: 3,
      kind: Keyword.get(opts, :kind, :project),
      workspace_key: digest(context),
      input_snapshot: modules |> Map.values() |> Enum.map(&get_in(&1, [:source, :sha256])) |> Enum.sort() |> digest(),
      artifact_digest: nil,
      validated_at: Artifacts.filesystem_timestamp(stage),
      context: context,
      dependencies: canonical_dependencies(opts),
      modules: modules,
      expected_modules: modules |> Map.keys() |> Enum.sort()
    }
  end

  defp canonical_context(opts, source_roots) do
    %{
      compiler_hash: BuildManifest.toolchain_fingerprint(),
      package: Keyword.get(opts, :package, "root"),
      package_exports: normalize_package_exports(Keyword.get(opts, :package_exports, %{})),
      package_exports_hash: digest(Keyword.get(opts, :package_exports, %{})),
      language_edition: Cure.Edition.current(),
      otp_release: to_string(:erlang.system_info(:otp_release)),
      elixir_version: System.version(),
      target: :beam,
      source_roots_hash: digest(Enum.map(source_roots, &Path.expand/1) |> Enum.sort()),
      codegen_options_hash: digest(Keyword.get(opts, :compile_opts, []))
    }
  end

  defp canonical_dependencies(opts) do
    %{
      stdlib: Keyword.get(opts, :stdlib_artifact_digest),
      packages: Keyword.get(opts, :package_artifact_digests, %{})
    }
  end

  defp normalize_package_exports(exports) when is_map(exports) do
    exports
    |> Enum.map(fn {package, modules} -> {to_string(package), Enum.sort(Enum.uniq(List.wrap(modules)))} end)
    |> Enum.sort()
    |> Map.new()
  end

  defp normalize_package_exports(_exports), do: %{}

  defp remove_previous_generation(stage) do
    stage
    |> File.ls!()
    |> Enum.each(fn entry -> File.rm_rf!(Path.join(stage, entry)) end)

    :ok
  end

  defp canonical_result(manifest, checked, prior) do
    rebuilt =
      Map.new(checked.rebuilt_modules, fn module ->
        {module, rebuild_reasons(module, manifest, prior)}
      end)

    reused = manifest.modules |> Map.keys() |> Kernel.--(Map.keys(rebuilt)) |> Enum.sort()
    removed = removed_entries(manifest, prior)

    %Result{
      pipeline: :canonical,
      workspace_key: manifest.workspace_key,
      input_snapshot: manifest.input_snapshot,
      artifact_digest: manifest.artifact_digest,
      artifact_root: manifest.artifact_root,
      reused: reused,
      rebuilt: rebuilt,
      removed: removed,
      cycles: canonical_cycles(checked),
      verification: :full,
      manifest_path: Path.join(manifest.artifact_root, BuildManifest.filename())
    }
  end

  defp rebuild_reasons(_module, _manifest, %{rebuild_reason: reason}) when not is_nil(reason),
    do: [reason]

  defp rebuild_reasons(module, manifest, %{manifest: %{modules: prior_modules}}) do
    case Map.fetch(prior_modules, module) do
      :error ->
        [:new_module]

      {:ok, prior} ->
        current = Map.fetch!(manifest.modules, module)

        if get_in(prior, [:source, :sha256]) != get_in(current, [:source, :sha256]),
          do: [:source_hash_mismatch],
          else: [:dependency_interface_changed]
    end
  end

  defp rebuild_reasons(_module, _manifest, _prior), do: [:new_module]

  defp removed_entries(manifest, prior) do
    removed_modules =
      case prior.manifest do
        %{modules: modules} -> Map.keys(modules) -- Map.keys(manifest.modules)
        _ -> []
      end

    Map.merge(
      Map.new(removed_modules, &{&1, [:source_removed]}),
      Map.new(prior.orphan_beams, &{&1, [:orphan_artifact]})
    )
  end

  defp canonical_cycles(checked) do
    checked.components
    |> Enum.filter(&(length(&1) > 1))
    |> Enum.map(&canonical_cycle_hops(&1, checked.manifest))
  end

  defp canonical_cycle_hops(component, manifest) do
    members = MapSet.new(component)
    start = Enum.min_by(component, &elem(&1, 1))

    adjacency =
      Map.new(component, fn identity ->
        targets =
          manifest.dependencies
          |> Map.get(identity, [])
          |> Enum.map(& &1.target)
          |> Enum.filter(&MapSet.member?(members, &1))
          |> Enum.uniq()
          |> Enum.sort_by(&elem(&1, 1))

        {identity, targets}
      end)

    path = find_cycle_path(start, start, adjacency, MapSet.new([start])) || [start, start]

    path
    |> Enum.with_index()
    |> Enum.map(fn {identity, index} ->
      entry = Map.fetch!(manifest.entries, identity)
      next = Enum.at(path, index + 1) || Enum.at(path, 1)

      line =
        manifest.dependencies
        |> Map.get(identity, [])
        |> Enum.find_value(entry_line(entry), fn dependency ->
          if dependency.target == next, do: get_in(dependency, [:span, :line]) || entry_line(entry)
        end)

      %{module: entry.module_name, path: entry.source_path, line: line}
    end)
  end

  defp find_cycle_path(current, start, adjacency, visited) do
    Enum.find_value(Map.get(adjacency, current, []), fn next ->
      cond do
        next == start ->
          [current, start]

        MapSet.member?(visited, next) ->
          nil

        true ->
          case find_cycle_path(next, start, adjacency, MapSet.put(visited, next)) do
            nil -> nil
            path -> [current | path]
          end
      end
    end)
  end

  defp entry_line(_entry), do: 1

  defp maybe_request_option(request, opts, key) do
    if Keyword.has_key?(opts, key), do: Keyword.put(request, key, Keyword.fetch!(opts, key)), else: request
  end

  defp digest(term), do: term |> :erlang.term_to_binary([:deterministic]) |> then(&:crypto.hash(:sha256, &1))

  defp validate(output_dir, opts) do
    expected_kind = Keyword.get(opts, :kind)

    verification = Keyword.get(opts, :verification, :cached)

    with {:ok, manifest} <- Artifacts.open_verified_set(output_dir, verification: verification),
         true <- is_nil(expected_kind) or manifest.kind == expected_kind do
      stats = Artifacts.hash_stats()

      {:ok,
       %Result{
         workspace_key: manifest.workspace_key,
         input_snapshot: manifest.input_snapshot,
         artifact_digest: manifest.artifact_digest,
         artifact_root: manifest.artifact_root,
         reused: manifest.modules |> Map.keys() |> Enum.sort(),
         verification: verification,
         hashes_computed: stats.computed,
         hashes_reused: stats.reused,
         manifest_path: Path.join(manifest.artifact_root, BuildManifest.filename())
       }}
    else
      false -> {:error, :artifact_kind_mismatch}
      {:error, _} = error -> error
    end
  end
end
