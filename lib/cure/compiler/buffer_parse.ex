defmodule Cure.Compiler.BufferParse do
  @moduledoc """
  Ephemeral shared parsing context for an active buffer and saved providers.

  Imported grammar uses the canonical manifest and Expansion provider ordering.
  The active text is a read override, not a source write or an interface field.
  Checking and publication remain the caller's ordinary Program authority.
  """

  alias Cure.Compiler.{ModuleIndex, ModuleManifest, Parser, SourceResolver}
  alias Cure.Compiler.ModulePipeline.Expansion
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityScan}

  @key {__MODULE__, :context}

  @doc false
  def active?, do: not is_nil(Process.get(@key))

  @doc false
  def scope(fun) do
    if Process.get(@key) do
      fun.()
    else
      previous_index = Process.get(:cure_module_index)
      supplied = if previous_index, do: Map.values(previous_index.entries), else: []
      Process.put(@key, %{sources: %{}, units: %{}, requested: MapSet.new(), supplied: supplied})

      try do
        SourceResolver.with_fresh_user_paths(fun)
      after
        Process.delete(@key)
        restore(:cure_module_index, previous_index)
      end
    end
  end

  @doc false
  def parse(source, tokens, opts) do
    scope(fn ->
      file = Keyword.get(opts, :file, "nofile")
      path = Path.expand(file)
      edition = source_edition(source, opts)
      key = {path, file, :crypto.hash(:sha256, source), edition, Keyword.get(opts, :prelude_providers, [])}
      context = Process.get(@key)
      Process.put(@key, %{context | sources: Map.put(context.sources, path, source)})

      case Map.fetch(context.units, key) do
        {:ok, ast} ->
          emit(ast, file, opts)
          {:ok, ast}

        :error ->
          facts = FixityScan.harvest_source(source, file, BuiltinFixity.table())

          if Enum.any?(facts.uses, &user_module?(&1.target)) do
            expand_buffer(source, path, file, facts, opts)
          else
            Parser.parse(tokens, opts)
          end
      end
    end)
  end

  defp expand_buffer(_source, path, file, facts, opts) do
    with {:ok, sources, known} <- gather([path], %{}, %{}),
         reader = reader(sources),
         options = [
           package: "buffer",
           source_reader: reader,
           source_names: %{path => file},
           parser_options: %{path => opts},
           implicit_modules: %{path => facts.module || "Main"},
           known_modules: Map.keys(known),
           edition: Keyword.get(opts, :edition, Cure.Edition.current()),
           validate_fixity_cycles: Keyword.get(opts, :validate_fixity_cycles, false)
         ],
         {:ok, manifest} <- ModuleManifest.build(Map.keys(sources), options),
         {:ok, expanded} <- Expansion.run(manifest, options) do
      cache_units(expanded, opts)
      ast = Map.fetch!(expanded.asts, manifest.paths[path])
      emit(ast, file, opts)
      {:ok, ast}
    else
      {:error, {:module_skeleton_error, {"buffer", name}, reason}} when name == facts.module or name == "Main" ->
        {:error, reason}

      {:error, _} = error ->
        error
    end
  end

  @spec gather([Path.t()], %{optional(Path.t()) => String.t()}, %{optional(String.t()) => true}) ::
          {:ok, %{optional(Path.t()) => String.t()}, %{optional(String.t()) => true}} | {:error, term()}
  defp gather([], sources, known), do: {:ok, sources, known}

  defp gather([path | rest], sources, known) do
    if Map.has_key?(sources, path) do
      gather(rest, sources, known)
    else
      with {:ok, source} <- reader(Process.get(@key).sources).(path) do
        facts = FixityScan.harvest_source(source, path, BuiltinFixity.table())
        references = Enum.uniq_by(facts.uses ++ facts.qualified_targets, & &1.target)
        names = references |> Enum.map(& &1.target) |> Enum.filter(&user_module?/1)

        with :ok <- index_requested(names),
             {:ok, providers, known} <- resolve(references, [], known) do
          gather(rest ++ providers, Map.put(sources, path, source), known)
        end
      end
    end
  end

  # Only requested identities participate in ambiguity checks. Unrelated
  # examples and test fixtures may legitimately share names such as Main.
  defp index_requested(names) do
    context = Process.get(@key)
    requested = MapSet.union(context.requested, MapSet.new(names))

    if MapSet.equal?(requested, context.requested) do
      :ok
    else
      roots = Process.get(:cure_source_roots, [])
      paths = Enum.flat_map(roots, &Path.wildcard(Path.join(&1, "**/*.cure")))
      sources = context.sources
      paths = Enum.uniq(Map.keys(sources) ++ paths)
      supplied_names = context.supplied |> Enum.flat_map(& &1.provided_modules) |> MapSet.new()
      missing = MapSet.difference(requested, supplied_names)

      with {:ok, discovered} <-
             ModuleIndex.build(paths,
               source_reader: reader(sources),
               only_modules: missing,
               ignore_unidentified: true,
               validate_dependencies: false
             ),
           {:ok, index} <-
             ModuleIndex.from_entries(context.supplied ++ Map.values(discovered.entries),
               validate_dependencies: false
             ) do
        Process.put(:cure_module_index, index)
        Process.put(@key, %{context | requested: requested})
        :ok
      else
        {:error, {:duplicate_module, name, paths}} ->
          {:error, {:duplicate_module_identity, name, paths}}

        {:error, _} = error ->
          error
      end
    end
  end

  @spec resolve([map()], [Path.t()], %{optional(String.t()) => true}) ::
          {:ok, [Path.t()], %{optional(String.t()) => true}}
  defp resolve([], paths, known), do: {:ok, Enum.uniq(paths), known}

  defp resolve([reference | rest], paths, known) do
    name = reference.target

    cond do
      ModuleIndex.compiler_owned?(name) ->
        resolve(rest, paths, Map.put(known, name, true))

      not user_module?(name) ->
        case SourceResolver.module_path(name) do
          {:ok, _path} -> resolve(rest, paths, Map.put(known, name, true))
          :not_found -> resolve(rest, paths, known)
        end

      true ->
        case SourceResolver.module_path(name) do
          {:ok, path} -> resolve(rest, [Path.expand(path) | paths], known)
          # Manifest validation produces the canonical missing identity error.
          :not_found -> resolve(rest, paths, known)
        end
    end
  end

  defp reader(overrides) do
    fn path ->
      case Map.fetch(overrides, Path.expand(path)) do
        {:ok, text} -> {:ok, text}
        :error -> File.read(path)
      end
    end
  end

  defp cache_units(expanded, opts) do
    context = Process.get(@key)
    edition = Keyword.get(opts, :edition, Cure.Edition.current())

    units =
      Enum.reduce(expanded.asts, context.units, fn {identity, ast}, units ->
        path = expanded.manifest.entries[identity].source_path
        source = Map.fetch!(expanded.sources, identity)
        root? = path == Path.expand(Keyword.get(opts, :file, "nofile"))
        file = if root?, do: Keyword.get(opts, :file, "nofile"), else: path
        providers = if root?, do: Keyword.get(opts, :prelude_providers, []), else: []
        normalized_edition = source_edition(source, edition: edition)
        Map.put(units, {path, file, :crypto.hash(:sha256, source), normalized_edition, providers}, ast)
      end)

    Process.put(@key, %{context | units: units})
  end

  defp user_module?(name), do: not String.starts_with?(name, "Std.") and not ModuleIndex.compiler_owned?(name)

  defp source_edition(source, opts) do
    value = Cure.Edition.pragma_edition(source) || Keyword.get(opts, :edition, Cure.Edition.current())
    # Authoritative Compiler/Expansion validation still owns invalid-edition
    # diagnostics; this key only identifies already-validated parsed units.
    case Cure.Edition.parse(value) do
      {:ok, edition} -> edition
      {:error, _} -> value
    end
  end

  defp emit(ast, file, opts) do
    if Keyword.get(opts, :emit_events, true),
      do: Cure.Pipeline.Events.emit(:parser, :parse_complete, ast, Cure.Pipeline.Events.meta(file, 1))
  end

  defp restore(key, nil), do: Process.delete(key)
  defp restore(key, value), do: Process.put(key, value)
end
