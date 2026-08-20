defmodule Cure.Compiler do
  @moduledoc """
  Compiler orchestrator for the Cure programming language.

  Chains together the full dependent compilation pipeline:

      source -> Lexer -> Parser -> Elab.Program -> Core.Kernel
             -> Elab.Erase -> Elab.Emit -> BeamWriter -> .beam

  Elaboration and trusted Core validation are mandatory. There is no
  unchecked classic-codegen path.

  Emits pipeline events at each stage boundary.

  ## Usage

      # Compile a file
      {:ok, module, warnings} = Cure.Compiler.compile_file("hello.cure")

      # Compile a string
      {:ok, module, warnings} = Cure.Compiler.compile_string(source, file: "hello.cure")

      # Compile and load into VM (for testing / REPL)
      {:ok, module} = Cure.Compiler.compile_and_load(source)
  """

  alias Cure.Compiler.{Lexer, Parser, BeamWriter}

  @doc """
  Compile a `.cure` source file to BEAM bytecode.

  Reads the file, runs the full pipeline, and writes a `.beam` file
  to the output directory.

  ## Options

  - `:output_dir` -- directory for standalone `.beam` output
    (default: `"_build/cure/scratch/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:source_roots` -- directories containing sibling `.cure` modules that may
    be imported with `use` (default: the source file's directory)
  """
  @spec compile_file(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_file(path, opts \\ []) do
    case compile_file_with_artifact(path, opts) do
      {:ok, module, warnings, _artifact} -> {:ok, module, warnings}
      {:error, _reason} = error -> error
    end
  end

  @doc """
  Compile a file and return the checked module artifact consumed by codegen.

  Incremental compilation uses this entry point so interface hashing reuses the
  exact certified environment that produced the BEAM artifact.
  """
  @spec compile_file_with_artifact(String.t(), keyword()) ::
          {:ok, module(), list(), Cure.Elab.CheckedModule.t() | nil} | {:error, term()}
  def compile_file_with_artifact(path, opts \\ []) do
    case File.read(path) do
      {:ok, source} ->
        opts = Keyword.put_new(opts, :file, path)
        compile_string_with_artifact(source, opts)

      {:error, reason} ->
        {:error, {:file_read_error, path, reason}}
    end
  end

  @doc """
  Load a module only when it is claimed by a complete verified artifact set.

  The whole set is preflighted before loading; a just-emitted standalone BEAM
  without a manifest is deliberately rejected.
  """
  @spec load_emitted(module(), Path.t()) :: :ok | {:error, term()}
  def load_emitted(module, output_dir) when is_atom(module) and is_binary(output_dir) do
    with {:ok, set} <- Cure.Compiler.Artifacts.open_verified_set(output_dir),
         true <-
           Enum.any?(set.modules, fn {_name, entry} ->
             Enum.any?(Map.get(entry, :artifacts, []), &(&1.module == Atom.to_string(module)))
           end),
         :ok <- Cure.Compiler.Artifacts.load_verified_set(set.artifact_root) do
      :ok
    else
      false -> {:error, :artifact_not_manifested}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Compile a Cure source string to BEAM bytecode and write to disk.

  ## Options

  - `:file` -- filename for error messages (default: `"nofile"`)
  - `:output_dir` -- directory for standalone `.beam` output
    (default: `"_build/cure/scratch/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec compile_string(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_string(source, opts \\ []) do
    case compile_string_with_artifact(source, opts) do
      {:ok, module, warnings, _artifact} -> {:ok, module, warnings}
      {:error, _reason} = error -> error
    end
  end

  @doc """
  Compile source and retain the checked module artifact used for emission.
  """
  @spec compile_string_with_artifact(String.t(), keyword()) ::
          {:ok, module(), list(), Cure.Elab.CheckedModule.t() | nil} | {:error, term()}
  def compile_string_with_artifact(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/scratch/ebin")
    emit? = Keyword.get(opts, :emit_events, true)
    declared_phases = Keyword.get(opts, :declared_phases)
    prelude_providers = Keyword.get(opts, :prelude_providers, [])
    qualified_envs = Keyword.get(opts, :qualified_envs, [])

    with_source_roots(file, opts, fn ->
      with {:ok, edition} <- resolve_edition(source, opts),
           {:ok, tokens} <- lex(source, file, emit?, edition),
           {:ok, ast} <- parse(tokens, file, emit?, edition, prelude_providers),
           {:ok, ast} <-
             migrate_warn(
               ast,
               file,
               source,
               edition,
               Keyword.get(opts, :migration_diagnostic_sink)
             ),
           ast = inject_prelude_uses(ast, prelude_providers),
           {:ok, ast} <- Cure.Elab.Program.expand_declaration_uses(ast),
           :ok <- validate_lifted_modules(ast),
           {:ok, units, cg_warnings, artifact} <-
             codegen(ast, source, file, emit?, output_dir, declared_phases, qualified_envs),
           units = inject_artifact_provenance(units, source, file, artifact, opts),
           {:ok, module, warnings} <-
             write_beam_units(units, output_dir, emit?, file, cg_warnings) do
        if artifact, do: Cure.Elab.Program.publish_checked_interface(artifact)
        {:ok, module, warnings, artifact}
      end
    end)
  end

  # Lifted-module requests are authored/generated source and therefore belong to
  # validation, not the internal-codegen error bucket. Codegen collects them
  # again to emit units; this early pass exists so malformed requests surface as
  # ordinary actionable diagnostics in both compile and check workflows.
  defp validate_lifted_modules(ast) do
    case Cure.Compiler.LiftModule.collect(ast) do
      {:ok, _requests} -> :ok
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Module names of every `@prelude`-marked module in a scanned dependency graph.
  A driver passes this list as the `:prelude_providers` compile option so a user
  `@prelude` module's operators reach every sibling in the same run.
  """
  @spec prelude_provider_names(Cure.Compiler.DepGraph.t()) :: [String.t()]
  defdelegate prelude_provider_names(graph), to: Cure.Compiler.DepGraph

  @doc """
  Compile a complete source universe through the canonical module graph.

  Every bulk driver should use this entry point or the canonical artifact sweep
  instead of sorting filenames and invoking `compile_file/2` independently.
  The graph supplies one dependency order, prelude-provider set, module index,
  and source-root universe to every file in the run.
  """
  @spec compile_files([Path.t()], keyword()) ::
          {:ok,
           %{
             compiled: [{Path.t(), module(), list()}],
             errors: [{Path.t(), term()}],
             cycles: [list()],
             module_index: Cure.Compiler.ModuleIndex.t()
           }}
          | {:error, {Path.t(), term()} | term()}
  def compile_files(files, opts \\ [])

  def compile_files([], opts) do
    with :ok <- reject_retired_bulk_options(opts),
         {:ok, :canonical} <- Cure.Compiler.ModulePipeline.Selection.normalize(opts) do
      {:ok,
       %{
         compiled: [],
         errors: [],
         cycles: [],
         module_index: nil,
         pipeline: :canonical
       }}
    end
  end

  def compile_files(files, opts) when is_list(files) do
    files = files |> Enum.map(&Path.expand/1) |> Enum.uniq()

    with :ok <- reject_retired_bulk_options(opts) do
      case Cure.Compiler.ModulePipeline.Selection.normalize(opts) do
        {:ok, :canonical} -> compile_files_canonical(files, opts)
        {:error, _reason} = error -> error
      end
    end
  end

  # A caller-supplied DepGraph plan was the second compilation authority: it
  # could disagree with the canonical manifest's source universe, Prelude set,
  # or generated semantic edges. Reject it explicitly instead of silently
  # ignoring it and appearing to honour stale ordering information.
  defp reject_retired_bulk_options(opts) do
    retired = [:plan] |> Enum.filter(&Keyword.has_key?(opts, &1)) |> Enum.sort()
    if retired == [], do: :ok, else: {:error, {:invalid_compile_files_options, retired}}
  end

  defp compile_files_canonical(files, opts) do
    request_opts =
      opts
      |> Keyword.take([
        :kind,
        :package,
        :package_dependencies,
        :package_exports,
        :source_roots,
        :interface_roots,
        :artifact_roots,
        :stdlib,
        :prelude_set,
        :compiler_providers,
        :edition,
        :macro_execution,
        :requested_roots,
        :diagnostic_sink,
        :event_sink,
        :incremental,
        :cache,
        :collect_diagnostics,
        :discovery_concurrency,
        :forbid_source_fallback,
        :forbid_beam_resolution,
        :fresh_environment
      ])
      |> Keyword.put(:module_pipeline, :canonical)
      |> Keyword.put(:products, [:beams])

    with {:ok, result} <-
           Cure.Compiler.ModulePipeline.check_entry_point(:compiler_files, files, request_opts),
         {:ok, compiled} <- publish_canonical_beams(result, opts) do
      {:ok,
       %{
         compiled: compiled,
         errors: [],
         cycles: canonical_cycles(result),
         module_index: nil,
         pipeline: :canonical,
         manifest: result.manifest,
         semantic_graph: result.semantic_graph,
         canonical_result: result
       }}
    end
  end

  defp publish_canonical_beams(result, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/project/ebin")
    emit? = Keyword.get(opts, :emit_events, true)
    load? = Keyword.get(opts, :load_emitted, true)
    File.mkdir_p!(output_dir)

    result.components
    |> List.flatten()
    |> Enum.reduce_while({:ok, []}, fn identity, {:ok, compiled} ->
      entry = Map.fetch!(result.manifest.entries, identity)
      module = String.to_atom("Cure." <> entry.module_name)

      with {:ok, binary} <- Map.fetch(result.beams, module),
           :ok <-
             BeamWriter.write_beam(module, binary, output_dir,
               emit_events: emit?,
               file: entry.source_path
             ),
           :ok <- maybe_load_canonical_beam(load?, module, binary) do
        {:cont, {:ok, [{entry.source_path, module, []} | compiled]}}
      else
        :error -> {:halt, {:error, {:canonical_beam_missing, entry.module_name}}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, compiled} -> {:ok, Enum.reverse(compiled)}
      {:error, _reason} = error -> error
    end
  end

  defp maybe_load_canonical_beam(false, _module, _binary), do: :ok

  defp maybe_load_canonical_beam(true, module, binary) do
    case :code.load_binary(module, ~c"canonical", binary) do
      {:module, ^module} -> :ok
      {:error, reason} -> {:error, {:beam_load_failed, module, reason}}
    end
  end

  defp canonical_cycles(result) do
    result.components
    |> Enum.filter(&(length(&1) > 1))
    |> Enum.map(fn component -> Enum.map(component, &elem(&1, 1)) end)
  end

  # `BeamWriter.compile_forms/2` returns `{:error, errors, warnings}` (3-tuple)
  # on lint/compile failures, but the public `compile_string/2`,
  # `compile_file/2`, and `compile_and_load/2` contracts are `{:ok, ...}` or
  # `{:error, reason}` (2-tuple). Normalize the BEAM-writer failure here so
  # downstream consumers (CLI, `cure check`, `mix cure.check.examples`, test
  # suites) can rely on the 2-tuple shape without `CaseClauseError` crashes.
  defp write_beam_units([{main_module, _main_forms} | _] = units, output_dir, emit?, file, cg_warnings) do
    Enum.reduce_while(units, {:ok, main_module, cg_warnings}, fn {expected_module, forms}, {:ok, main, warnings} ->
      case BeamWriter.compile_forms(forms) do
        {:ok, module, binary, beam_warnings} ->
          case BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
            :ok -> {:cont, {:ok, main, warnings ++ BeamWriter.normalize_warnings(beam_warnings, file)}}
            {:error, _} = err -> {:halt, err}
          end

        {:error, errors, _beam_warnings} when warnings != [] ->
          {:halt,
           {:error,
            {:codegen_failure,
             %{
               stage: :beam_writer,
               module: expected_module,
               file: file,
               reason: {:beam_lint, errors, warnings}
             }}}}

        {:error, errors, _beam_warnings} ->
          {:halt,
           {:error,
            {:codegen_failure,
             %{stage: :beam_writer, module: expected_module, file: file, reason: {:beam_lint, errors}}}}}
      end
    end)
  end

  defp write_beam_units([], _output_dir, _emit?, _file, _warnings),
    do: {:error, {:codegen_error, :no_compilation_units}}

  defp inject_artifact_provenance(units, source, file, artifact, opts) do
    compiler_hash = Cure.Compiler.BuildManifest.toolchain_fingerprint()

    base =
      Keyword.get_lazy(opts, :artifact_provenance, fn ->
        source_hash = :crypto.hash(:sha256, source)

        %{
          compiler_hash: compiler_hash,
          producer_snapshot:
            :crypto.hash(
              :sha256,
              :erlang.term_to_binary(
                %{compiler_hash: compiler_hash, source_hash: source_hash},
                [:deterministic]
              )
            )
        }
      end)

    interface_hash =
      case artifact do
        %Cure.Elab.CheckedModule{interface: %Cure.Compiler.ModuleInterface{interface_hash: hash}} ->
          hash

        _ ->
          nil
      end

    Enum.map(units, fn {module, forms} ->
      provenance =
        base
        |> Map.new()
        |> Map.merge(%{
          format: 1,
          module: module |> Atom.to_string() |> String.replace_prefix("Cure.", ""),
          source_path: Path.expand(file),
          source_hash: :crypto.hash(:sha256, source),
          interface_hash: interface_hash
        })

      {attrs, rest} = Enum.split_while(forms, &match?({:attribute, _, _, _}, &1))
      {module, attrs ++ [{:attribute, 1, :cure_artifact, [provenance]}] ++ rest}
    end)
  end

  defp compile_and_load_units([{main_module, _main_forms} | _] = units, file) do
    Enum.reduce_while(units, {:ok, main_module}, fn {expected_module, forms}, {:ok, main} ->
      with {:ok, ^expected_module, binary, _warnings} <- BeamWriter.compile_forms(forms),
           :ok <- Cure.Compiler.Artifacts.verify_binary(binary, expected_module),
           {:module, ^expected_module} <-
             :code.load_binary(expected_module, ~c"nofile", binary) do
        {:cont, {:ok, main}}
      else
        reason ->
          {:halt,
           {:error,
            {:codegen_failure,
             %{
               stage: :verified_beam_loader,
               module: expected_module,
               file: file,
               reason: reason
             }}}}
      end
    end)
  end

  defp compile_and_load_units([], file),
    do: {:error, {:codegen_failure, %{stage: :codegen, module: nil, file: file, reason: :no_compilation_units}}}

  @doc """
  Lex and parse a Cure source string into its raw parser AST.

  Runs the front end only — no type checking, optimization, or codegen — and
  with pipeline event emission disabled, so it works **headless**: under
  `mix run --no-compile --no-start`, a bare `elixir` invocation, or any context
  where the `:cure` application (and its events registry) is not started. This
  is the supported entry point for debugging and tooling that needs to inspect
  how a construct parses. See `Cure.Pipeline.Events.emission_enabled?/0`.

  ## Options

  - `:file` -- filename for error messages (default: `"nofile"`)

  Returns `{:ok, ast}` or `{:error, {:lex_error | :parse_error | :edition_error, reason}}`.
  An `:edition_error` is returned when the resolved edition (file pragma or project
  `Cure.toml`) is unknown — surfaced rather than silently degraded to the default.

  ## Examples

      iex> {:ok, ast} = Cure.Compiler.parse_source("mod X\\n  type T = A | B\\n")
      iex> is_list(ast)
      true
  """
  @spec parse_source(String.t(), keyword()) :: {:ok, list()} | {:error, term()}
  def parse_source(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")

    # Tooling entry: resolve the file's edition so inspection sees the same keyword
    # set the compiler would — pragma > project Cure.toml > default, matching the
    # compile path (A3-F2). A real :file discovers its project root so a manifest-
    # pinned edition is honoured; a genuine no-file source stays headless (nil dir
    # → default). An unknown edition is surfaced, not swallowed (iteration 8, F1):
    # a manifest edition error can't be re-caught by the parser (the manifest isn't
    # in the source), so degrading to current() would hide a real §3.1 error.
    project_dir = if file in [nil, "nofile"], do: nil, else: Cure.Project.find_root(file)

    case Cure.Edition.resolve(%{source: source, project_dir: project_dir}) do
      {:ok, edition} ->
        with {:ok, tokens} <- lex(source, file, false, edition) do
          # Single-file tooling utility: no driver, so no user `@prelude`
          # providers — falls back to the compiler-bundled prelude only.
          parse(tokens, file, false, edition, [])
        end

      {:error, reason} ->
        {:error, {:edition_error, reason}}
    end
  end

  @doc """
  Compile a Cure source string and load the resulting module into the VM.

  Does not write a `.beam` file to disk. Useful for testing and REPL.
  """
  @spec compile_and_load(String.t(), keyword()) ::
          {:ok, module()} | {:error, term()}
  def compile_and_load(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, false)
    declared_phases = Keyword.get(opts, :declared_phases)
    qualified_envs = Keyword.get(opts, :qualified_envs, [])
    prelude_providers = Keyword.get(opts, :prelude_providers, [])

    with_source_roots(file, opts, fn ->
      with {:ok, edition} <- resolve_edition(source, opts),
           {:ok, tokens} <- lex(source, file, emit?, edition),
           {:ok, ast} <- parse(tokens, file, emit?, edition, prelude_providers),
           ast = inject_prelude_uses(ast, prelude_providers),
           {:ok, ast} <- Cure.Elab.Program.expand_declaration_uses(ast),
           {:ok, units, _cg_warnings, artifact} <-
             codegen(ast, source, file, emit?, nil, declared_phases, qualified_envs),
           units = inject_artifact_provenance(units, source, file, artifact, opts) do
        # compile_and_load/2 intentionally does NOT persist bytecode to
        # disk -- it only loads into the current VM.
        compile_and_load_units(units, file)
      end
    end)
  end

  # The dependent elaborator resolves `use` imports from source, not from the
  # BEAM loader. Keep roots process-local for one compilation so recursive
  # imported-module elaboration and parallel callers cannot leak project state.
  defp with_source_roots(file, opts, fun) do
    roots =
      case Keyword.fetch(opts, :source_roots) do
        {:ok, explicit} -> explicit
        :error -> Process.get(:cure_source_roots) || default_source_roots(file)
      end
      |> List.wrap()
      |> Enum.filter(&is_binary/1)
      |> Enum.map(&Path.expand/1)
      |> Enum.uniq()

    previous = Process.get(:cure_source_roots)
    previous_index = Process.get(:cure_module_index)
    Process.put(:cure_source_roots, roots)

    case Keyword.get(opts, :module_index) do
      %Cure.Compiler.ModuleIndex{} = index -> Process.put(:cure_module_index, index)
      _ -> Process.delete(:cure_module_index)
    end

    try do
      fun.()
    after
      if previous == nil,
        do: Process.delete(:cure_source_roots),
        else: Process.put(:cure_source_roots, previous)

      if previous_index == nil,
        do: Process.delete(:cure_module_index),
        else: Process.put(:cure_module_index, previous_index)
    end
  end

  defp default_source_roots(file) when file in [nil, "nofile"], do: []
  defp default_source_roots(file), do: [Path.dirname(Path.expand(file))]

  # -- Pipeline Steps ----------------------------------------------------------

  defp lex(source, file, emit?, edition) do
    case Lexer.tokenize(source, file: file, emit_events: emit?, edition: edition) do
      {:ok, tokens} -> {:ok, tokens}
      {:error, reason} -> {:error, {:lex_error, reason}}
    end
  end

  defp parse(tokens, file, emit?, edition, prelude_providers) do
    case Parser.parse(tokens,
           file: file,
           emit_events: emit?,
           edition: edition,
           prelude_providers: prelude_providers,
           validate_fixity_cycles: true
         ) do
      {:ok, ast} -> {:ok, ast}
      {:error, errors} -> {:error, {:parse_error, errors}}
    end
  end

  # A user `@prelude` provider is an implicit `use`, not syntax-only parser
  # state. Inject ordinary import nodes into each source module so the existing
  # source loader brings the provider's definitions, types, and interfaces into
  # elaboration. Ordinary import collision/coherence checks remain authoritative.
  defp inject_prelude_uses(ast, []), do: ast

  defp inject_prelude_uses({:container, meta, body}, providers) when is_list(meta) do
    if Keyword.get(meta, :container_type) in [:module, :proof] do
      self = Keyword.get(meta, :name)

      existing =
        body
        |> List.wrap()
        |> Enum.flat_map(fn
          {:import, import_meta, _} -> [Keyword.get(import_meta, :source)]
          _ -> []
        end)
        |> MapSet.new()

      imports =
        providers
        |> Enum.reject(&(&1 == self or MapSet.member?(existing, &1)))
        # `prelude_injected: true` marks these as COMPILER-SYNTHESIZED, not lines the
        # author wrote. `Cure.Elab.Program.validate_stdlib_imports/1` keys off it: an
        # ambient provider is NOT an `order_deps` edge, so the compile order cannot
        # guarantee its beam exists yet (see `Incremental.compile_order/1`), and
        # demanding one breaks a cold build of the stdlib itself.
        |> Enum.map(
          &{:import, [source: &1, import_type: :use, language: :cure, line: 1, col: 1, prelude_injected: true], []}
        )

      {:container, meta, imports ++ List.wrap(body)}
    else
      {:container, meta, inject_prelude_uses(body, providers)}
    end
  end

  defp inject_prelude_uses({:block, meta, items}, providers) when is_list(items),
    do: {:block, meta, Enum.map(items, &inject_prelude_uses(&1, providers))}

  defp inject_prelude_uses(ast, _providers), do: ast

  # Resolve the edition this source compiles under (spec §3.2 precedence: file
  # `@edition` pragma > `Cure.toml` `[project].edition` > compiler default). The
  # resolved edition drives the lexer's keyword set (§4), so a file pinned to an
  # older edition still parses a since-retired keyword under `cure build` — the
  # feature's headline purpose (F-A). The project root is taken from `:project_dir`
  # when a caller supplies it, else discovered from the file's path (see below); a
  # bare source with no file and no manifest resolves to the file pragma alone,
  # else default (§3.2 point 3). An unknown edition (typo'd pragma / bad manifest)
  # fails loudly HERE (§3.1) rather than compiling silently under the default.
  defp resolve_edition(source, opts) do
    input = %{source: source}

    # A caller that knows the project root passes `:project_dir`; otherwise it is
    # DISCOVERED from the file's own path — the nearest ancestor `Cure.toml`. This
    # is what lets `cure build`/`run` honour a project's `[project].edition`
    # without every CLI caller threading a dir, while a file deep in a dependency
    # tree still binds to its own manifest (nearest wins), not a far-away app's.
    project_dir =
      Keyword.get(opts, :project_dir) ||
        Cure.Project.find_root(Keyword.get(opts, :file))

    input =
      case project_dir do
        nil -> input
        dir -> Map.put(input, :project_dir, dir)
      end

    case Cure.Edition.resolve(input) do
      {:ok, edition} -> {:ok, edition}
      {:error, reason} -> {:error, {:edition_error, reason}}
    end
  end

  # `cure build` warn-and-tolerate consumer of the migration facility (spec
  # §5.1): run the deprecation rules, print each warning to stderr, and continue
  # compiling on the *tolerated* (rewritten-in-memory) AST — the source file is
  # never modified. `cure migrate` is the separate rewrite-and-write consumer.
  defp migrate_warn(ast, file, source, edition, diagnostic_sink) do
    source_ast = ast
    {ast, warnings} = Cure.Migrate.run(ast, file: file, apply: :safe_only)

    warnings =
      case migration_preview_ast(source_ast, source, file, edition) do
        {:ok, preview_ast} ->
          {_preview_ast, preview_warnings} =
            Cure.Migrate.run(preview_ast, file: file, apply: :safe_only)

          if length(preview_warnings) == length(warnings), do: preview_warnings, else: warnings

        :error ->
          warnings
      end

    registry = migration_source_registry(file)

    diagnostics = Enum.map(warnings, &migration_warning_diagnostic(&1, registry))
    emit_migration_diagnostics(diagnostics, registry, diagnostic_sink)

    {:ok, ast}
  end

  defp emit_migration_diagnostics(diagnostics, registry, sink) when is_function(sink, 2) do
    sink.(diagnostics, registry)
    :ok
  rescue
    _ -> emit_migration_diagnostics(diagnostics, registry, nil)
  catch
    _, _ -> emit_migration_diagnostics(diagnostics, registry, nil)
  end

  defp emit_migration_diagnostics(diagnostics, registry, _sink) do
    sink =
      Cure.Diagnostic.Sink.new(
        registry: registry,
        format: :plain,
        output_device: :stderr,
        width: 80
      )

    sink
    |> Cure.Diagnostic.Sink.emit_all(diagnostics)
    |> Cure.Diagnostic.Sink.flush()
  end

  # Compilation deliberately parses without trivia. A whole-file migration
  # preview must not be printed from that AST because doing so would silently
  # omit comments. Re-tokenize only for trivia and attach it to the already
  # parsed tree; this copy feeds diagnostics only, never code generation.
  defp migration_preview_ast(ast, source, file, edition) do
    case Cure.Compiler.Lexer.tokenize(source,
           file: file,
           trivia: true,
           emit_events: false,
           edition: edition
         ) do
      {:ok, _tokens, trivia} -> {:ok, Cure.Compiler.Trivia.attach(ast, trivia)}
      _ -> :error
    end
  rescue
    _ -> :error
  end

  defp migration_warning_diagnostic(warning, registry) do
    details = Map.from_struct(warning)

    details =
      case warning.span || migration_warning_line_span(registry, warning.file, warning.line) do
        %Cure.Diagnostic.Span{} = span -> Map.put(details, :span, span)
        nil -> details
      end

    details = Map.put(details, :suggestions, migration_warning_suggestions(warning, registry))
    Cure.Diagnostic.Operational.migration_warning(details)
  end

  defp migration_warning_suggestions(%{tier: :manual}, _registry) do
    [%Cure.Diagnostic.Suggestion{message: "Port this deprecated syntax by hand.", applicability: :manual}]
  end

  defp migration_warning_suggestions(%{preview: preview, tier: tier, file: file}, registry)
       when is_binary(preview) and tier in [:machine, :review] do
    case migration_whole_source_span(registry, file) do
      %Cure.Diagnostic.Span{} = span ->
        applicability = if tier == :machine, do: :machine_applicable, else: :maybe_incorrect

        message =
          if tier == :machine,
            do: "Apply the semantics-preserving migration.",
            else: "Review and apply the proposed migration."

        [
          %Cure.Diagnostic.Suggestion{
            message: message,
            applicability: applicability,
            edits: [%Cure.Diagnostic.TextEdit{span: span, replacement: preview}]
          }
        ]

      nil ->
        []
    end
  end

  defp migration_warning_suggestions(_warning, _registry), do: []

  defp migration_whole_source_span(nil, _file), do: nil

  defp migration_whole_source_span(registry, file) do
    with {:ok, source} <- Cure.Diagnostic.SourceRegistry.fetch(registry, file) do
      lines = String.split(source, "\n", trim: false)

      Cure.Diagnostic.Span.new(
        source_id: file,
        path: file,
        start_byte: 0,
        end_byte: byte_size(source),
        start_line: 1,
        start_column: 1,
        end_line: length(lines),
        end_column: String.length(List.last(lines) || "") + 1
      )
    else
      _ -> nil
    end
  end

  # Migration rules historically report a line only. Until each producer is
  # upgraded to return its exact token span, turn that location into a useful
  # primary range covering the authored, non-blank portion of the line. This is
  # a real source-backed span (and therefore works in terminal/JSON/LSP), not a
  # renderer-side reconstruction.
  defp migration_warning_line_span(nil, _file, _line), do: nil
  defp migration_warning_line_span(_registry, _file, nil), do: nil
  defp migration_warning_line_span(_registry, _file, line) when not is_integer(line) or line < 1, do: nil

  defp migration_warning_line_span(registry, file, line) do
    with {:ok, source} <- Cure.Diagnostic.SourceRegistry.fetch(registry, file),
         text when is_binary(text) <- Enum.at(String.split(source, "\n", trim: false), line - 1) do
      leading = text |> String.codepoints() |> Enum.take_while(&(&1 in [" ", "\t"])) |> Enum.join()
      content = text |> String.trim_leading() |> String.trim_trailing("\r")
      column = String.length(leading) + 1
      length = max(String.length(content), 1)

      case Cure.Diagnostic.SourceRegistry.span_at(registry, file, line, column, length) do
        {:ok, span} -> span
        {:error, _} -> nil
      end
    else
      _ -> nil
    end
  end

  defp migration_source_registry(file) do
    case File.read(file) do
      {:ok, source} ->
        Cure.Diagnostic.SourceRegistry.new()
        |> Cure.Diagnostic.SourceRegistry.register(file, source, file)

      {:error, _reason} ->
        nil
    end
  end

  defp codegen(ast, source, file, _emit?, _output_dir, _declared_phases, qualified_envs) do
    case Cure.Compiler.LiftModule.collect(ast) do
      {:ok, lifted_requests} ->
        codegen_modules(ast, Cure.Compiler.LiftModule.strip(ast), lifted_requests, source, file, qualified_envs)

      {:error, reason} ->
        {:error, {:codegen_error, reason}}
    end
  end

  defp codegen_modules(original_ast, main_ast, lifted_requests, source, file, qualified_envs) do
    if match?({:lift_module, _, _}, main_ast) do
      case emit_lifted_modules(lifted_requests) do
        {:ok, lifted_units} -> {:ok, module_forms(lifted_units), [], nil}
        {:error, _} = error -> error
      end
    else
      codegen_modules_with_main(original_ast, main_ast, lifted_requests, source, file, qualified_envs)
    end
  end

  defp codegen_modules_with_main(original_ast, main_ast, lifted_requests, source, file, qualified_envs) do
    # Lifted modules are checked FIRST so the enclosing unit can name their
    # members. A lifted module never depends on the enclosing module by name --
    # `LiftModule.inherit_scope/2` has already inlined the declarations it needs
    # -- so this direction is the acyclic one. Without it a `fsm Machine`
    # declared in `mod Demo` is invisible to `Demo` itself: `Machine.Event`
    # failed with `{:bad_projection, "Event"}` because qualified resolution
    # loads interfaces from source files, and a lifted module has none.
    lifted = emit_lifted_modules(lifted_requests)

    # A failed lift contributes no surface; the main module is then checked
    # exactly as it was before lifting was reordered.
    lifted_surfaces =
      case lifted do
        {:ok, lifted_units} -> qualified_envs(lifted_units) ++ qualified_envs
        {:error, _} -> qualified_envs
      end

    # Single pipeline: every module is elaborated, checked, erased, and emitted
    # through the dependent Core.
    result =
      with :ok <- Cure.Elab.Program.validate_stdlib_imports(main_ast) do
        case dependent_codegen(main_ast, source, file, lifted_surfaces) do
          {:ok, forms, artifact} -> {:ok, forms, [], artifact}
          {:error, {:codegen_error, {:expansion_ill_typed, _} = reason}} -> {:error, reason}
          {:error, _} = err -> err
        end
      else
        {:error, reason} -> {:error, {:codegen_error, reason}}
      end

    # The main module's own error always wins. A lifted module carries an
    # inlined copy of the enclosing declarations, so a mistake in one of them
    # shows up in BOTH -- and the copy's version names a synthesised module the
    # author never wrote. Reporting the lift first would replace
    # `unknown_global :Tick` in `Unqualified` with a conversion failure inside
    # `Cure.Unqualified.Machine`.
    case {result, lifted} do
      {{:ok, forms, warnings, artifact}, {:ok, lifted_units}} when is_list(forms) ->
        # Inject the module's `@group(:g)` decorator as a BEAM `-group([:g]).`
        # attribute after the ordinary dependent pipeline has produced forms.
        main_forms = inject_group_attribute(forms, original_ast)

        {:ok, [{forms_module(main_forms), main_forms} | module_forms(lifted_units)], warnings, artifact}

      {{:error, _} = error, _} ->
        error

      {_other, {:error, _} = error} ->
        error

      {other, _} ->
        other
    end
  end

  # The owner-keyed checked environments of this unit's lifted modules, in
  # declaration order.
  defp qualified_envs(lifted_units) do
    Enum.map(lifted_units, &{&1.module_name, &1.env})
  end

  # `emit_lifted_modules/1` yields whole units so their environments stay
  # reachable; every codegen result is the `{module, forms}` pairs.
  defp module_forms(lifted_units) do
    Enum.map(lifted_units, &{&1.module, &1.forms})
  end

  defp emit_lifted_modules(requests) do
    Enum.reduce_while(requests, {:ok, []}, fn request, {:ok, acc} ->
      case Cure.Compiler.LiftModule.emit(request) do
        {:ok, unit} -> {:cont, {:ok, acc ++ [unit]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp forms_module([{:attribute, _line, :module, module} | _]), do: module

  defp forms_module(forms) do
    case Enum.find(forms, &match?({:attribute, _, :module, _}, &1)) do
      {:attribute, _line, :module, module} -> module
      _ -> raise ArgumentError, "compiled forms are missing a module attribute"
    end
  end

  # Walk the original AST for the first standalone `@group(:g)` decorator node
  # and, if present, splice `{:attribute, 1, :group, [g]}` into `forms` right
  # after the last leading module attribute (before any function form).
  defp inject_group_attribute(forms, ast) do
    case group_atom(ast) do
      nil ->
        forms

      atom ->
        {attrs, rest} = Enum.split_while(forms, &match?({:attribute, _, _, _}, &1))
        attrs ++ [{:attribute, 1, :group, [atom]}] ++ rest
    end
  end

  # The `@group(:g)` atom for the parsed program, or nil. `@group` above `mod`
  # attaches to the module container's meta; the in-body form is a parse error
  # (spec 2026-07-10-group-decorator-placement), so meta is the only source.
  defp group_atom(node) do
    node |> group_atoms() |> List.first()
  end

  # A module container with `@group(:g)` attached above `mod` carries the group
  # in its meta as a canonical decorator node
  # (`decorator: {:decorator, [name: :group], [{:literal, _, atom}]}`). Read it
  # there, then descend into the body for nested containers.
  defp group_atoms({:container, meta, children}) when is_list(meta) and is_list(children) do
    from_meta =
      case Keyword.get(meta, :decorator) do
        {:decorator, dm, [{:literal, _, atom}]} when is_atom(atom) ->
          if Keyword.get(dm, :name) == :group, do: [atom], else: []

        _ ->
          []
      end

    from_meta ++ Enum.flat_map(children, &group_atoms/1)
  end

  defp group_atoms({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &group_atoms/1)

  defp group_atoms(list) when is_list(list), do: Enum.flat_map(list, &group_atoms/1)
  defp group_atoms(_other), do: []

  # A dependent module is lowered by the kernel: elaborate to `Cure.Core`, erase
  # its {0,ω} index arguments, and emit the erased residue as real BEAM forms.
  defp dependent_codegen(ast, source, file, qualified_envs) do
    with {:ok, artifact} <-
           Cure.Elab.Program.check_ast_artifact(ast,
             source: source,
             file: file,
             prelude_mode: :bootstrap_safe,
             qualified_envs: qualified_envs
           ),
         {:ok, forms} <-
           Cure.Elab.Emit.compile_forms(
             artifact.env,
             artifact.module,
             artifact.local_defs
           ) do
      {:ok, forms, artifact}
    else
      {:error, {:source_context, {:expansion_ill_typed, _details}, _context} = reason} ->
        {:error, reason}

      {:error, {:final_core_violation, name, _rejections} = reason} ->
        {:error, {:codegen_error, {:source_context, reason, final_core_source_context(ast, name)}}}

      {:error, reason} ->
        {:error, {:codegen_error, reason}}
    end
  end

  defp final_core_source_context(ast, name) do
    source_info = find_definition_source_info(ast, Cure.Elab.Name.base(name))

    %{
      span: source_info && source_info.whole,
      provenance: if(source_info, do: source_info.provenance, else: []),
      checking: name,
      codegen_stage: :final_core_validation,
      codegen_module: Cure.Elab.Program.module_atom(ast),
      expression_category: :function_definition
    }
  end

  defp find_definition_source_info({:function_def, meta, _body}, bare_name) when is_list(meta) do
    if to_string(Keyword.get(meta, :name)) == bare_name do
      Cure.MetaAST.Metadata.source_info(meta)
    end
  end

  defp find_definition_source_info({_tag, _meta, children}, bare_name),
    do: find_definition_source_info(children, bare_name)

  defp find_definition_source_info(items, bare_name) when is_list(items),
    do: Enum.find_value(items, &find_definition_source_info(&1, bare_name))

  defp find_definition_source_info(_item, _bare_name), do: nil
end
