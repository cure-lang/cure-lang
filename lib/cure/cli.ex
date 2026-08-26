defmodule Cure.CLI do
  @moduledoc """
  Standalone command-line interface for the Cure programming language.

  ## Subcommands

      cure compile <file|dir>   Compile .cure files to BEAM bytecode
      cure run <file>           Compile and execute a .cure file
      cure check <file>         Type-check a .cure file without compiling
      cure lsp                  Start the Language Server Protocol server
      cure stdlib               Compile the standard library
      cure version              Show the Cure version
      cure help                 Show this help message

  ## Options

      --output-dir DIR    Output directory (default: _build/cure/project/ebin)
      --verbose           Show detailed compilation output
  """

  # Delegate to `Cure.version/0`, which is itself resolved at compile
  # time from the top-level `mix.exs` and marked as an
  # `@external_resource` so a version bump in `mix.exs` always reaches
  # the compiled escript.
  defp version, do: Cure.version()

  @doc "Entry point for escript."
  def main(args) do
    # Ensure the application is started
    Application.ensure_all_started(:cure)

    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [
          output_dir: :string,
          type_check: :boolean,
          optimize: :boolean,
          verbose: :boolean,
          help: :boolean,
          goal: :string,
          ctx: :string,
          effects: :string,
          max: :integer,
          depth: :integer,
          duration: :integer,
          width: :integer,
          action: :string,
          template: :string,
          lib: :boolean,
          app: :boolean,
          fsm: :boolean,
          filter: :string,
          doctests: :boolean,
          poll_ms: :integer,
          debounce: :integer,
          aggressive: :boolean,
          ast: :boolean,
          algebra: :boolean,
          safe: :boolean,
          check: :boolean,
          print: :boolean,
          dry_run: :boolean,
          hex: :boolean,
          handle: :string,
          token: :string,
          cover: :boolean,
          strict: :boolean,
          edition: :string,
          target: :string,
          format: :string,
          registry: :string,
          include_erts: :boolean,
          overwrite: :boolean,
          title: :string,
          main: :string,
          extras: :keep,
          # Retained v0.31 profile-file options. The classic optimizer itself
          # was deleted with the classic compiler.
          pgo: :boolean,
          record_profile: :boolean,
          profile_dir: :string,
          module: :string,
          top: :integer,
          # export-types / snap / story output + target. Without these declared,
          # OptionParser cannot tell they take a value: `--out` with a missing or
          # flag-following value collapses to boolean `true`, which then leaks into
          # the argv handed to the delegated Mix task in place of a filename.
          out: :string,
          target: :string,
          diagrams: :boolean,
          step: :boolean,
          raw: :boolean,
          theme: :string,
          mode: :string,
          history: :string,
          no_history: :boolean,
          error_device: :string
        ],
        aliases: [o: :output_dir, v: :verbose, h: :help, f: :filter, t: :template]
      )

    if invalid != [] do
      usage_error("Invalid command options: #{format_invalid_options(invalid)}")
    end

    if opts[:help] do
      help()
    else
      case rest do
        ["compile" | paths] ->
          cmd_compile(paths, opts)

        ["run" | [path]] ->
          cmd_run(path, opts)

        # Wrong argument count for a fixed-arity command is a usage error, not an
        # unknown command — without this fallback it fell through to the generic
        # catch-all and misblamed `run` (a valid command) as unknown.
        ["run" | _] ->
          usage_error("Usage: cure run <file>")

        ["check" | [path]] ->
          cmd_check(path, opts)

        ["check" | _] ->
          usage_error("Usage: cure check <file>")

        ["lsp"] ->
          cmd_lsp()

        # A fixed-arity command's extra positional arg is a usage error, not an
        # unknown command — without this fallback it fell through to the generic
        # catch-all and misblamed the (valid) command as unknown.
        ["lsp" | _] ->
          usage_error("Usage: cure lsp")

        ["stdlib"] ->
          cmd_stdlib(opts)

        ["stdlib" | _] ->
          usage_error("Usage: cure stdlib")

        ["version"] ->
          cmd_version()

        ["version" | _] ->
          usage_error("Usage: cure version")

        ["init" | [name]] ->
          cmd_init(name)

        ["init" | _] ->
          usage_error("Usage: cure init <name>")

        ["deps"] ->
          cmd_deps()

        ["deps", "update"] ->
          cmd_deps_update()

        ["deps", "tree"] ->
          cmd_deps_tree()

        # A `deps` invocation with an unrecognised subcommand must name the real
        # offender and fail, not fall through to the generic catch-all (which
        # would bind `unknown = "deps"`, blame a valid command, and exit 0).
        ["deps" | rest] ->
          usage_error("Unknown deps subcommand: #{Enum.join(rest, " ")}. Known: update, tree.")

        ["test"] ->
          cmd_test(opts)

        ["test" | _] ->
          usage_error("Usage: cure test")

        ["explain"] ->
          cmd_explain_all()

        ["explain" | [code]] ->
          cmd_explain(code)

        ["explain" | _] ->
          usage_error("Usage: cure explain [<error-code>]")

        ["doc" | paths] ->
          cmd_doc(paths, opts)

        ["repl"] ->
          cmd_repl(opts)

        ["repl" | _] ->
          usage_error("Usage: cure repl")

        ["fmt" | paths] ->
          cmd_fmt(paths, opts)

        ["audit", "trust", module] ->
          cmd_audit_trust(module, opts)

        ["audit" | _] ->
          usage_error("Usage: cure audit trust <Module> [--format text|json] [--strict] [--target <t>]")

        ["migrate" | paths] ->
          case cmd_migrate(paths, opts) do
            :ok -> :ok
            {:error, _} -> System.halt(1)
          end

        ["watch" | rest] ->
          cmd_watch(rest, opts)

        ["new" | rest] ->
          cmd_new(rest, opts)

        ["bench" | rest] ->
          cmd_bench(rest, opts)

        ["why"] ->
          cmd_explain_all()

        ["why" | [code]] ->
          cmd_explain(code)

        ["why" | _] ->
          usage_error("Usage: cure why [<error-code>]")

        ["doctor"] ->
          cmd_doctor(opts)

        ["doctor" | _] ->
          usage_error("Usage: cure doctor")

        ["fix"] ->
          cmd_fix(opts)

        ["fix" | _] ->
          usage_error("Usage: cure fix")

        ["publish" | _] ->
          cmd_publish(opts)

        ["search" | [query]] ->
          cmd_search(query, opts)

        ["search" | _] ->
          usage_error("Usage: cure search <query>")

        ["info" | [name]] ->
          cmd_info(name, opts)

        ["info" | _] ->
          usage_error("Usage: cure info <name>")

        ["keys", "generate", handle] ->
          cmd_keys_generate(handle)

        ["keys", "list"] ->
          cmd_keys_list()

        # Any other `keys` shape (bare, missing handle, unknown/extra subcommand)
        # must give a keys-specific usage error and fail — not fall through to the
        # generic catch-all, which would misblame `keys` as an unknown command.
        ["keys" | _rest] ->
          usage_error("Usage: cure keys generate <handle> | cure keys list")

        ["release" | rest] ->
          cmd_release(rest, opts)

        ["john"] ->
          cmd_john(opts)

        ["john" | _] ->
          usage_error("Usage: cure john")

        ["trace" | rest] ->
          cmd_trace(rest, opts)

        ["replay" | rest] ->
          cmd_replay(rest, opts)

        ["draw" | rest] ->
          cmd_draw(rest, opts)

        ["verify" | rest] ->
          cmd_verify(rest, opts)

        ["export-types" | rest] ->
          cmd_export_types(rest, opts)

        ["snap" | rest] ->
          cmd_snap(rest, opts)

        ["story" | _] ->
          cmd_story(opts)

        ["help" | _] ->
          # Extra args to `help` show help (standard CLI behavior), never fall
          # through to the catch-all and misblame `help` as an unknown command.
          help()

        [] ->
          help()

        [unknown | _] ->
          known_commands = ~w(
            compile run check lsp stdlib version init deps test
            explain doc repl fmt watch new bench why doctor fix migrate
            publish search info keys release trace replay
            john draw verify export-types snap story help
          )

          suffix =
            case Cure.Compiler.Errors.suggest(unknown, known_commands) do
              nil -> ""
              suggestion -> " Did you mean '#{suggestion}'?"
            end

          usage_error("Unknown command: #{unknown}.#{suffix} Run 'cure help' for usage.")
      end
    end
  end

  # -- replay (v0.28.0) --------------------------------------------------------

  defp cmd_replay([], _opts) do
    usage_error("Usage: cure replay <path.journal> [--module ModuleName] [--step]")
  end

  defp cmd_replay([path | _], opts) do
    step? = Keyword.get(opts, :step, false)
    mod_str = Keyword.get(opts, :module)

    case Cure.Observe.Journal.load(path) do
      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason))
        exit({:shutdown, 1})

      {:ok, entries} ->
        info("Loaded #{length(entries)} entries from #{path}")
        Cure.Observe.Replay.print_trace(entries)

        if mod_str do
          mod = Module.concat([mod_str])

          if verified_replay_module?(mod) do
            case Cure.Observe.Replay.replay(mod, entries, step: step?) do
              {:ok, :quit} ->
                info("Replay quit early.")

              {:ok, _results} ->
                info("Replay complete.")

              {:error, reason} ->
                error_diagnostic(Cure.Diagnostic.Operational.command_failure("Replay", reason))

                exit({:shutdown, 1})
            end
          else
            error_diagnostic(
              Cure.Diagnostic.Operational.artifact_error(
                "Module `#{mod_str}` is not loaded. Run `cure compile` first.",
                %{kind: :module_not_loaded, module: mod_str}
              )
            )

            exit({:shutdown, 1})
          end
        end
    end
  end

  defp verified_replay_module?(module) do
    case Cure.Compiler.Artifacts.load_verified_modules(
           "_build/cure/project/ebin",
           [module]
         ) do
      :ok -> true
      {:error, _reason} -> false
    end
  end

  # -- trace (v0.27.0) ---------------------------------------------------------

  # -- john (everything, all at once) ------------------------------------------

  defp cmd_john(opts) do
    john_opts =
      []
      |> put_if(opts, :width)

    _ = Cure.John.run(john_opts)
  end

  defp put_if(keyword, opts, key) do
    case Keyword.fetch(opts, key) do
      {:ok, value} -> Keyword.put(keyword, key, value)
      :error -> keyword
    end
  end

  defp cmd_trace([], _opts), do: usage_error("Usage: cure trace Module.fun/arity")

  defp cmd_trace([target | _], opts) do
    duration = Keyword.get(opts, :duration, 10) * 1000

    case parse_mfa(target) do
      {:ok, mfa} ->
        info("Tracing #{target} for #{div(duration, 1000)}s...")
        Cure.Observe.Trace.start(mfa)
        :timer.sleep(duration)
        Cure.Observe.Trace.stop()
        info("Trace stopped.")

      {:error, _} ->
        usage_error("Cannot parse `#{target}`; expected Module.fun/arity")
    end
  end

  defp parse_mfa(target) when is_binary(target) do
    case Regex.run(~r/^([\w\.]+)\.(\w+)\/(\d+)$/, target) do
      [_, mod, fun, arity] ->
        mod_atom = Module.concat([mod])
        {:ok, {mod_atom, String.to_atom(fun), String.to_integer(arity)}}

      _ ->
        {:error, :bad_mfa}
    end
  end

  # -- compile -----------------------------------------------------------------

  defp cmd_compile([], _opts), do: usage_error("Usage: cure compile <file|directory>")

  defp cmd_compile(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/project/ebin")
    verbose? = Keyword.get(opts, :verbose, false)

    # Preload the stdlib so sources that `use Std.Iter`, `use Std.Gen`,
    # etc. can resolve their imports at compile time. Without this, a
    # fresh VM hitting a bulk `cure compile examples/` run would see
    # `undefined_function` lint errors for any module referencing a
    # stdlib function whose beam has not yet been loaded.
    # When a Cure.toml is available, its [compiler] stdlib_path takes
    # priority over the default resolution chain.
    project =
      case Cure.Project.load() do
        {:ok, p} -> p
        _ -> nil
      end

    package_sets =
      case dependency_artifact_sets(project) do
        {:ok, sets} ->
          sets

        {:error, reason} ->
          emit_host_diagnostic(reason, hd(paths))
          exit({:shutdown, 1})
      end

    dependency_roots = dependency_source_roots(project)

    compile_opts = [
      output_dir: output_dir,
      emit_events: false,
      source_roots: dependency_roots ++ source_roots(paths)
    ]

    files =
      Enum.flat_map(paths, fn path ->
        if File.dir?(path) do
          path |> Path.join("**/*.cure") |> Path.wildcard()
        else
          [path]
        end
      end)
      |> Enum.uniq()

    ordered = Enum.sort(files)

    # Compilation validates explicit imports by asking whether their provider
    # module is loaded. Dependency closure scanning is intentionally about
    # project ordering and does not include every ambient/prelude provider, so
    # using it as a selective stdlib loader made a valid `use Std.Fsm` fail in a
    # fresh escript VM. CLI compilation promises the complete stdlib surface.
    preload_runtime_dependencies!(project)

    if verbose?, do: Enum.each(ordered, &info("Compiling #{&1}"))

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           source_paths: ordered,
           source_roots: Keyword.fetch!(compile_opts, :source_roots),
           output_dir: output_dir,
           kind: :project,
           repair: true,
           verify_stdlib: true,
           stdlib_artifact_digest: Cure.Compiler.Artifacts.stdlib_fingerprint(),
           package_artifact_sets: package_sets,
           package_artifact_digests: Map.new(package_sets, fn {name, set} -> {name, set.artifact_digest} end),
           compile_opts: Keyword.take(compile_opts, [:emit_events, :source_roots])
         ) do
      {:ok, result} ->
        Enum.each(result.cycles, fn walk ->
          emit_host_diagnostic({:import_cycle, walk}, hd(paths))
        end)

        result.rebuilt
        |> Enum.sort_by(&elem(&1, 0))
        |> Enum.each(fn {module, reasons} ->
          suffix =
            if verbose?,
              do: " [" <> Enum.map_join(reasons, ", ", &to_string/1) <> "]",
              else: ""

          info("  -> Cure.#{module}#{suffix}")
        end)

      {:error, {:artifact_sweep_failed, errors}} ->
        Enum.each(errors, fn {target, reason} ->
          emit_host_diagnostic(reason, source_path_for_target(target, ordered))
        end)

        exit({:shutdown, 1})

      {:error, reason} ->
        emit_host_diagnostic(reason, hd(paths))
        exit({:shutdown, 1})
    end
  end

  # -- run ---------------------------------------------------------------------

  @dialyzer {:nowarn_function, cmd_run: 2}
  defp cmd_run(path, _opts) do
    project =
      case Cure.Project.load() do
        {:ok, p} -> p
        _ -> nil
      end

    preload_runtime_dependencies!(project)
    source_roots = [Path.dirname(Path.expand(path)) | dependency_source_roots(project)]

    source =
      case File.read(path) do
        {:ok, s} ->
          s

        {:error, reason} ->
          error_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason))
          exit({:shutdown, 1})
      end

    case Cure.Compiler.compile_and_load(source,
           file: path,
           emit_events: false,
           source_roots: source_roots
         ) do
      {:ok, module} ->
        if function_exported?(module, :main, 0) do
          result = module.main()
          if result != :ok and result != nil, do: IO.inspect(result)
        else
          info("Module #{module} compiled (no main/0 function)")
        end

      {:error, reason} ->
        emit_host_diagnostic(reason, path)
        exit({:shutdown, 1})
    end
  end

  # -- draw (v0.31.0) ----------------------------------------------------------

  defp cmd_draw([], _opts) do
    usage_error("Usage: cure draw <path.cure> [--filter lifted|all]")
  end

  defp cmd_draw([kind, path], opts) when kind in ["lifted", "all"] do
    do_draw(path, Keyword.put(opts, :filter, String.to_atom(kind)))
  end

  defp cmd_draw([path | _rest], opts) do
    filter =
      case Keyword.get(opts, :filter) do
        nil -> :all
        "lifted" -> :lifted
        "all" -> :all
        atom when is_atom(atom) -> atom
        _ -> :all
      end

    do_draw(path, Keyword.put(opts, :filter, filter))
  end

  defp do_draw(path, opts) do
    filter = Keyword.get(opts, :filter, :all)

    case Cure.Doc.Ascii.render_file(path, filter: filter) do
      {:ok, ""} ->
        info("#{path}: no lifted modules to draw")

      {:ok, source} ->
        IO.puts(source)

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_write(path, reason))
        exit({:shutdown, 1})
    end
  end

  # Load stdlib .beam files from _build/cure/ebin (plus any Cure.* example
  # modules previously compiled into _build/cure/ex_ebin) into the VM.
  #
  # The dedicated helper avoids adding the output directories to the
  # global Erlang code path, so stale leftover lowercase beams (e.g. a
  # pre-rename examples/math.cure -> math.beam) can't shadow OTP modules.
  #
  # When a `Cure.Project.t()` is given, its `[compiler] stdlib_path`
  # takes the highest priority; falling back to `$CURE_LIB`, then the
  # standard candidate chain in `Cure.Stdlib.Paths`.
  defp preload_stdlib(project, modules \\ nil) do
    # CLI entry points (`cure run`, `cure compile`) want every stdlib
    # module available so user sources can `use Std.X` without thinking
    # about groups. The REPL is the only caller with a narrower default
    # (`:none`); see `Cure.REPL.start/1`.
    opts =
      case modules do
        nil -> [examples: false, kind: :all]
        modules -> [examples: false, kind: :none, modules: modules]
      end

    opts =
      case project do
        %Cure.Project{} ->
          case Cure.Project.stdlib_path(project) do
            path when is_binary(path) and path != "" -> Keyword.put(opts, :stdlib_ebin, path)
            _ -> opts
          end

        _ ->
          opts
      end

    Cure.Stdlib.Preload.preload(opts)
  end

  defp preload_project_dependencies(%Cure.Project{} = project) do
    project
    |> Cure.Project.dependency_ebin_paths()
    |> Enum.reduce_while(:ok, fn ebin, :ok ->
      case Cure.Compiler.Artifacts.load_verified_set(ebin) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  defp preload_project_dependencies(_project), do: :ok

  defp dependency_artifact_sets(%Cure.Project{} = project) do
    Cure.Project.dependency_artifact_sets(project)
  end

  defp dependency_artifact_sets(_project), do: {:ok, %{}}

  defp source_path_for_target(target, paths) do
    if is_binary(target) and File.regular?(target) do
      target
    else
      module = to_string(target)

      Enum.find(paths, hd(paths), fn path ->
        case Cure.Compiler.DepGraph.scan([path]) do
          {:ok, %{modules: modules}} -> Map.has_key?(modules, module)
          _ -> false
        end
      end)
    end
  end

  defp preload_runtime_dependencies!(project, modules \\ nil) do
    with :ok <- preload_stdlib(project, modules),
         :ok <- preload_project_dependencies(project) do
      :ok
    else
      {:error, reason} ->
        error_diagnostic(
          Cure.Diagnostic.Operational.artifact_error(
            "A runtime dependency artifact set failed verification: #{inspect(reason)}",
            %{reason: inspect(reason)}
          )
        )

        exit({:shutdown, 1})
    end
  end

  defp dependency_source_roots(%Cure.Project{} = project),
    do: Cure.Project.dependency_source_paths(project)

  defp dependency_source_roots(_project), do: []

  defp source_roots(paths) do
    paths
    |> Enum.map(fn path -> if File.dir?(path), do: path, else: Path.dirname(path) end)
    |> Enum.map(&Path.expand/1)
    |> Enum.uniq()
  end

  # -- check -------------------------------------------------------------------

  @dialyzer {:nowarn_function, cmd_check: 2}
  defp cmd_check(path, _opts) do
    source =
      case File.read(path) do
        {:ok, s} ->
          s

        {:error, reason} ->
          error_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason))
          exit({:shutdown, 1})
      end

    with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false),
         {:ok, ast} <- Cure.Elab.Program.expand_declaration_uses(ast),
         {:ok, _lifted_requests} <- Cure.Compiler.LiftModule.collect(ast),
         {:ok, _env} <- Cure.Elab.Program.check_ast(ast) do
      info("#{path}: OK")
    else
      {:error, reason} ->
        # The dependent checker returns a tagged `{:error, term}`; funnel it
        # through the shared structured sink.
        emit_host_diagnostic(reason, path)
        exit({:shutdown, 1})
    end
  end

  # -- lsp ---------------------------------------------------------------------

  defp cmd_lsp do
    {:ok, _pid} = Cure.LSP.Server.start_link()
    Process.sleep(:infinity)
  end

  # -- stdlib ------------------------------------------------------------------

  defp cmd_stdlib(opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    stdlib_dir = Path.join([:code.priv_dir(:cure) |> to_string(), "..", "lib", "std"])

    stdlib_dir =
      if File.dir?(stdlib_dir) do
        stdlib_dir
      else
        Path.join(["lib", "std"])
      end

    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure")) |> Enum.sort()

    if cure_files == [] do
      info("No .cure files found in #{stdlib_dir}")
    else
      info("Compiling Cure standard library (#{length(cure_files)} modules)")

      case Cure.Compiler.compile_files(cure_files,
             module_pipeline: :canonical,
             package: "stdlib",
             output_dir: output_dir,
             kind: :stdlib,
             emit_events: false,
             source_roots: [stdlib_dir],
             continue_on_error: true
           ) do
        {:ok, result} ->
          Enum.each(result.compiled, fn {path, module, _warnings} ->
            info("  #{Path.basename(path, ".cure")} -> #{module}")
          end)

          Enum.each(result.errors, fn {path, reason} ->
            info("  #{Path.basename(path, ".cure")}: compilation failed")
            emit_host_diagnostic(reason, path)
          end)

          info("Output: #{output_dir}")
          if result.errors != [], do: exit({:shutdown, 1})

        {:error, reason} ->
          emit_host_diagnostic(reason, stdlib_dir)
          exit({:shutdown, 1})
      end
    end
  end

  # -- init --------------------------------------------------------------------

  defp cmd_init(name) do
    Cure.Project.init(name)
    info("Created project '#{name}' with Cure.toml, lib/main.cure")
  end

  # -- deps --------------------------------------------------------------------

  defp cmd_deps do
    case Cure.Project.load() do
      {:ok, project} ->
        # `cure deps` may have to compile path/git dependencies that
        # `use Std.*`. Preload the full stdlib up front so those
        # imports resolve at compile time without extra plumbing.
        preload_stdlib(project)

        case project.dependencies do
          [] ->
            Cure.Project.write_lock(project)
            info("No dependencies declared in Cure.toml; lockfile is up to date.")

          deps ->
            info("Resolving #{length(deps)} dependency(ies) for #{project.name}...")

            case Cure.Project.resolve_deps(project) do
              :ok ->
                Cure.Project.write_lock(project)
                info("Dependencies resolved. Cure.lock written.")

              {:error, reason} ->
                error_diagnostic(Cure.Diagnostic.Operational.dependency(reason))
                exit({:shutdown, 1})
            end
        end

      {:error, :no_project_file} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent))
        exit({:shutdown, 1})

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", reason))
        exit({:shutdown, 1})
    end
  end

  defp cmd_deps_update do
    case Cure.Project.load() do
      {:ok, project} ->
        preload_stdlib(project)

        case project.dependencies do
          [] ->
            info("No dependencies to update.")

          deps ->
            info("Updating #{length(deps)} dependency(ies) for #{project.name}...")

            Enum.each(deps, fn dep ->
              # `resolve_git_dep/2` clones into `_build/deps/<name>` and compiles
              # the dep's `lib/`. It now returns `{:error, _}` for a dep whose own
              # edition is unknown (dependency_edition_error) — report and abort
              # like `cmd_deps` rather than crashing with a MatchError.
              if Map.get(dep, :git) do
                case Cure.Project.resolve_git_dep(dep, project.root) do
                  :ok ->
                    :ok

                  {:error, reason} ->
                    error_diagnostic(Cure.Diagnostic.Operational.dependency(reason))
                    exit({:shutdown, 1})
                end
              end
            end)

            Cure.Project.write_lock(project)
            info("Lockfile updated.")
        end

      {:error, :no_project_file} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent))
        exit({:shutdown, 1})

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", reason))
        exit({:shutdown, 1})
    end
  end

  defp cmd_deps_tree do
    case Cure.Project.load() do
      {:ok, project} ->
        IO.puts(Cure.Project.dep_tree(project))

      {:error, :no_project_file} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent))
        exit({:shutdown, 1})

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", reason))
        exit({:shutdown, 1})
    end
  end

  # -- test --------------------------------------------------------------------

  defp cmd_test(opts) do
    filter = Keyword.get(opts, :filter, nil)
    doctests? = Keyword.get(opts, :doctests, false)
    cover? = Keyword.get(opts, :cover, false)

    # Tests typically reference both stdlib helpers (`Std.Test.assert_eq`)
    # and modules defined in the project's own `lib/`. The escript starts
    # with neither loaded, so without this step every test that calls
    # into `lib/` or `Std.*` would crash with `:undef`. Mirror what
    # `cmd_run/2` does for stdlib, then JIT-compile every `lib/**/*.cure`
    # so user modules (`Money.hello/0`, etc.) are reachable from the
    # test bodies below.
    project =
      case Cure.Project.load() do
        {:ok, p} -> p
        _ -> nil
      end

    preload_runtime_dependencies!(project)
    dependency_roots = dependency_source_roots(project)
    load_project_lib(project)

    if cover? do
      Cure.Cover.start("_build/cure/project/ebin")
    end

    test_files =
      Path.wildcard("test/**/*.cure")
      # Oracle and fixture sources are compiled by their dedicated regression
      # runners; many are intentionally invalid and must not be executable
      # project tests.
      |> Enum.reject(&non_runnable_test_source?/1)

    results =
      if test_files == [] do
        info("No runnable test files found in test/ (oracle and fixture sources are excluded)")
        []
      else
        Enum.map(test_files, fn file ->
          source = File.read!(file)

          case Cure.Compiler.compile_and_load(source,
                 file: file,
                 emit_events: false,
                 source_roots: [Path.dirname(Path.expand(file)) | dependency_roots]
               ) do
            {:ok, mod} ->
              # Run all test_ functions
              exports = mod.module_info(:exports)

              test_fns =
                exports
                |> Enum.filter(fn {name, arity} ->
                  String.starts_with?(Atom.to_string(name), "test") and arity == 0
                end)
                |> Enum.filter(fn {name, _} ->
                  filter == nil or String.contains?(Atom.to_string(name), filter)
                end)

              Enum.map(test_fns, fn {name, _} ->
                try do
                  apply(mod, name, [])
                  {:pass, "#{file}: #{name}"}
                catch
                  kind, reason ->
                    emit_host_diagnostic(
                      {:command_failed, "test #{name}", {kind, reason}},
                      file,
                      source
                    )

                    {:fail, "#{file}: #{name}"}
                end
              end)

            {:error, reason} ->
              emit_host_diagnostic(reason, file, source)
              [{:fail, "#{file}: compilation failed"}]
          end
        end)
        |> List.flatten()
      end

    results =
      if doctests? do
        results ++ run_doctests(filter)
      else
        results
      end

    pass = Enum.count(results, fn {s, _} -> s == :pass end)
    fail = Enum.count(results, fn {s, _} -> s == :fail end)

    Enum.each(results, fn
      {:pass, name} -> info("  PASS #{name}")
      {:fail, name} -> info("  FAIL #{name}")
    end)

    info("#{pass} passed, #{fail} failed")

    if cover? do
      results_cov = Cure.Cover.collect()
      _ = Cure.Cover.summary(results_cov)
      _ = Cure.Cover.report(results_cov)
      info("Coverage HTML written to _build/cure/cover/index.html")
    end

    if fail > 0, do: exit({:shutdown, 1})
  end

  defp non_runnable_test_source?(path) do
    expanded = Path.expand(path)
    String.contains?(expanded, "/test/oracle/") or String.contains?(expanded, "/test/fixtures/")
  end

  # Compile and load every `lib/**/*.cure` in the current project so
  # test bodies can call into user modules without each test having to
  # bootstrap the project itself. Failures are surfaced as warnings
  # rather than aborting the whole `cure test` run -- a broken module
  # in `lib/` will already produce a follow-up `:undef` from the test
  # that depends on it, which is more actionable than a single
  # "compilation error" line.
  defp load_project_lib(project) do
    files = Path.wildcard("lib/**/*.cure")

    result =
      case project do
        %Cure.Project{} ->
          Cure.Project.compile_project(project,
            output_dir: "_build/cure/project/ebin",
            emit_events: false
          )

        _ ->
          Cure.Compiler.compile_files(files,
            module_pipeline: :canonical,
            output_dir: "_build/cure/project/ebin",
            emit_events: false,
            source_roots: ["lib"],
            continue_on_error: true,
            verify_stdlib: true,
            stdlib_artifact_digest: Cure.Compiler.Artifacts.stdlib_fingerprint()
          )
      end

    case result do
      {:ok, result} ->
        Enum.each(Map.get(result, :errors, []), fn {file, reason} ->
          emit_host_diagnostic(reason, file)
        end)

        case Cure.Compiler.Artifacts.open_verified_set("_build/cure/project/ebin") do
          {:ok, set} -> Cure.Compiler.Artifacts.load_verified_set(set.artifact_root)
          {:error, _reason} when files == [] -> :ok
          {:error, reason} -> emit_host_diagnostic(reason, "lib")
        end

      {:error, reason} ->
        emit_host_diagnostic(reason, "lib")
    end
  end

  defp run_doctests(filter) do
    Path.wildcard("lib/**/*.cure")
    |> Enum.flat_map(fn file ->
      case Cure.Doc.Doctests.extract(file) do
        [] ->
          []

        cases ->
          cases
          |> Enum.filter(fn %{name: n} -> filter == nil or String.contains?(n, filter) end)
          |> Enum.map(fn %{name: name, expr: expr, expected: expected} ->
            case Cure.Doc.Doctests.run_one(expr, expected, file) do
              :ok ->
                {:pass, "#{file}: doctest #{name}"}

              {:fail, diagnostic, registry} ->
                emit_diagnostic(diagnostic, registry)

                {:fail, "#{file}: doctest #{name}"}
            end
          end)
      end
    end)
  end

  # -- doc ---------------------------------------------------------------------
  #
  # `cure doc` reads `Cure.toml`'s optional `[doc]` table, lets the
  # user override the most interesting fields (`--title`, `--main`,
  # `--extras`) from the command line, then hands everything to the
  # generator. When `Cure.toml` is absent we fall back to sensible
  # defaults (title = "Cure Documentation", no extras, no groups).
  defp cmd_doc(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/doc")
    project_root = File.cwd!()
    {project_doc, project_title} = load_doc_config(project_root)

    cli_extras = Keyword.get_values(opts, :extras)

    doc_config =
      project_doc
      |> Map.put(
        :extras,
        if(cli_extras == [], do: Map.get(project_doc, :extras, []), else: cli_extras)
      )
      |> Map.put(:main, Keyword.get(opts, :main, Map.get(project_doc, :main)))

    title =
      Keyword.get(opts, :title) ||
        Map.get(project_doc, :title) ||
        project_title

    cure_files =
      case paths do
        [] ->
          Path.wildcard("lib/**/*.cure") ++ Path.wildcard("lib/std/*.cure")

        _ ->
          expand_cure_targets(paths)
      end

    if cure_files == [] do
      info("No .cure files found")
    else
      info("Generating documentation for #{length(cure_files)} files")

      modules =
        Enum.flat_map(cure_files, fn file ->
          source = read_source_or_exit(file)

          with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false),
               {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false) do
            doc = Cure.Doc.Extractor.extract(ast)

            if doc.module != "Unknown" do
              [doc]
            else
              []
            end
          else
            _ -> []
          end
        end)

      Cure.Doc.HTMLGenerator.generate(modules, output_dir,
        title: title,
        doc_config: doc_config,
        project_root: project_root,
        cure_version: Cure.version()
      )

      extras_count = length(Map.get(doc_config, :extras, []))

      info("Documentation written to #{output_dir}/ (#{length(modules)} modules, #{extras_count} extras)")
    end
  end

  # Load the `[doc]` table from `Cure.toml`, returning `{doc_map,
  # fallback_title}`. The fallback title is derived from `[project]`
  # so a bare `Cure.toml` still produces a branded docset.
  defp load_doc_config(root) do
    case Cure.Project.load(root) do
      {:ok, project} ->
        title =
          case project.name do
            n when is_binary(n) and n != "" ->
              String.capitalize(n) <> " Documentation"

            _ ->
              "Cure Documentation"
          end

        {project.doc, title}

      _ ->
        {%{}, "Cure Documentation"}
    end
  end

  # -- repl --------------------------------------------------------------------

  defp cmd_repl(opts) do
    repl_keys = Keyword.keys(Cure.REPL.Options.switches())
    {repl_opts, warnings} = opts |> Keyword.take(repl_keys) |> Cure.REPL.Options.build_opts()

    if warnings != [] do
      usage_error(Enum.join(warnings, "\n"))
    end

    Cure.REPL.start(repl_opts)
  end

  # -- fmt ---------------------------------------------------------------------

  # Four modes:
  #
  #   * (default, v0.21.0) algebra pretty-printer. Reformats from the
  #     AST using `Cure.Compiler.Algebra` + `Cure.Compiler.AlgebraFormatter`,
  #     with round-trip verification that falls back to the original
  #     source when the rewrite would change program structure. Plain
  #     `#` comment nodes and doc comments survive the round-trip.
  #
  #   * `--safe`: legacy byte-level formatter from v0.20.0, kept as an
  #     escape hatch for sources that have layout the algebra formatter
  #     does not yet support.
  #
  #   * `--algebra`: explicit opt-in; synonymous with the default.
  #
  #   * `--aggressive` / `--ast`: canonicalising AST pretty printer.
  #     Reformats the buffer from the parse tree through
  #     `Cure.Compiler.Printer`, which strips plain `#` comments and
  #     any layout that doesn't survive a parser round-trip. Prints a
  #     banner before touching disk so users know what they're opting
  #     into.
  #
  #   * `--check`: dry-run that prints which files would change without
  #     rewriting them. Uses the algebra formatter in v0.21.0.
  # Expand explicit path arguments (for `fmt`/`doc`) to a list of .cure files: a
  # directory expands to its .cure files, a plain path is kept. A path that does
  # not exist is a user error (a typo'd filename) — report it and exit non-zero,
  # rather than passing it to a worker whose File.read! would crash with a raw
  # BEAM stacktrace. Mirrors how `run`/`check`/`compile` treat a missing file.
  defp expand_cure_targets(paths) do
    case Enum.reject(paths, &File.exists?/1) do
      [] ->
        Enum.flat_map(paths, fn p ->
          if File.dir?(p), do: Path.wildcard(Path.join(p, "**/*.cure")), else: [p]
        end)

      missing ->
        Enum.each(missing, fn path ->
          error_diagnostic(Cure.Diagnostic.Operational.file_read(path, :enoent))
        end)

        exit({:shutdown, 1})
    end
  end

  # Read a source file for a fmt/doc worker, degrading ANY read error to a clean
  # non-zero exit instead of a raw File.Error stacktrace. `expand_cure_targets`
  # rejects a *missing* explicit target up front, but `File.exists?` is true for
  # a file that exists yet is unreadable (chmod 000), and the no-argument
  # wildcard scan does not go through that guard at all — so the workers still
  # need a tolerant read. Mirrors how run/check/compile read with File.read.
  defp read_source_or_exit(file) do
    case File.read(file) do
      {:ok, source} ->
        source

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read(file, reason))
        exit({:shutdown, 1})
    end
  end

  defp cmd_fmt(paths, opts) do
    cure_files =
      case paths do
        [] ->
          Path.wildcard("lib/**/*.cure") ++ Path.wildcard("test/**/*.cure")

        _ ->
          expand_cure_targets(paths)
      end

    cond do
      cure_files == [] ->
        info("No .cure files found")

      Keyword.get(opts, :aggressive, false) or Keyword.get(opts, :ast, false) ->
        fmt_aggressive(cure_files)

      Keyword.get(opts, :safe, false) ->
        fmt_safe(cure_files)

      Keyword.get(opts, :check, false) ->
        fmt_check(cure_files)

      Keyword.get(opts, :dry_run, false) ->
        fmt_diff(cure_files)

      true ->
        # v0.21.0: algebra formatter is the default. The explicit
        # `--algebra` flag is kept for symmetry with `--safe` but
        # otherwise a no-op.
        fmt_algebra(cure_files)
    end
  end

  # `cure audit trust <Module>` — print the unproved assumptions reachable from a
  # module. `Cure.Audit.CLI.run/2` is pure; the `System.halt/1` lives here.
  defp cmd_audit_trust(module, opts) do
    # `Source.locate/1` finds the module via a compile-time-baked absolute path,
    # but the elaborator resolves a module's `use Std.X` imports through
    # `Cure.Stdlib.Paths`, whose search chain is empty for a plain dev checkout
    # invoked from outside the repo — so the module would locate but silently
    # fail to elaborate and land in UNAUDITED, looking like a clean zero-axiom
    # report. Seed the resolver with the known stdlib dir ONLY when nothing else
    # already resolves (so a user's CURE_HOME/CURE_LIB is never shadowed).
    case Cure.Audit.Source.import_seed_dir() do
      nil -> :ok
      dir -> Application.put_env(:cure, :stdlib_source_dir, dir)
    end

    audit_opts = [
      strict: Keyword.get(opts, :strict, false),
      format: Keyword.get(opts, :format, "text"),
      verbose: Keyword.get(opts, :verbose, false)
    ]

    audit_opts =
      case Keyword.get(opts, :target) do
        nil ->
          audit_opts

        t ->
          # `to_existing_atom/1` would raise on an unrecognized target, but
          # `Targets.unavailable/1` already answers "nothing unavailable" for an
          # unknown one. CLI argv is bounded input, not untrusted network input.
          Keyword.put(audit_opts, :target, String.to_atom(t))
      end

    case Cure.Audit.CLI.run(module, audit_opts) do
      {:ok, text} ->
        IO.write(text)
        :ok

      {:strict_failure, text} ->
        IO.write(text)
        exit({:shutdown, 1})

      {:error, :not_found} ->
        error_diagnostic(Cure.Diagnostic.Operational.usage("no such module: #{module}"))

        exit({:shutdown, 1})
    end
  end

  # `cure migrate` — the rewrite-and-write consumer of the migration facility
  # (spec §5.6/§5.8). PUBLIC, deviating from this file's `defp cmd_*` convention,
  # so tests can call it directly and assert on its `:ok | {:error, {reason,
  # detail}}` return without spawning a subprocess or hitting the `System.halt`
  # in `main/1`'s dispatch arm (which is what turns a non-`:ok` return into a
  # non-zero exit for CI).
  @doc false
  def cmd_migrate(paths, opts) do
    check? = Keyword.get(opts, :check, false)
    print? = Keyword.get(opts, :print, false)
    strict? = Keyword.get(opts, :strict, false)

    # Resolve the crossing target: `--edition YYYY` when given, else the compiler
    # default edition (`Cure.Edition.current/0`) — which is deliberately DECOUPLED
    # from the newest *known* edition (staged rollout), so with no flag `migrate`
    # targets the default, NOT necessarily the newest minted edition. A
    # user-supplied value is validated through
    # Cure.Edition.parse/1 BEFORE it can reach plan_migration_source/2 or the
    # phase-2 bump — set_edition/2 writes whatever string it is handed verbatim,
    # so an unvalidated typo would only surface much later on the next project
    # load. plan_migration/1 then refuses a downgrade target before any file is
    # read.
    # Measure the downgrade guard against the PROJECT's declared edition, not
    # always the latest minted one (F4), and print a diagnostic on refusal
    # instead of a silent nonzero exit (F5). An invalid edition DECLARED in the
    # project aborts here (I4) rather than being masked as the compiler default.
    with {:ok, target} <- migrate_resolve_edition(opts),
         {:ok, project_edition} <- migrate_project_edition(".") do
      case plan_migration(target: target, current: project_edition) do
        {:error, :downgrade} ->
          migration_error(:project_downgrade, %{target: target, current: project_edition})

          {:error, :downgrade}

        {:ok, ^target} ->
          case migrate_targets(paths) do
            [] ->
              info("No .cure files found")
              :ok

            files ->
              with :ok <- migrate_git_guard(files, check?, print?),
                   {:ok, results} <- migrate_preflight_all(files, target, project_edition),
                   :ok <- migrate_strict_gate(results, target, strict?) do
                migrate_apply_and_bump(results, target, paths, check?, print?)
              end
          end
      end
    end
  end

  @doc false
  # The project's declared edition (Cure.toml [project].edition), or the compiler
  # default when there is no project / it declares none. The downgrade guard
  # measures the target against THIS, not always the latest minted edition (F4).
  #
  # An INVALID declared edition (a Cure.toml naming an edition the compiler does
  # not know) is surfaced as `{:error, {:unknown_edition, _}}` — NOT masked as
  # the default (I4). Masking would silently defeat the downgrade guard: a broken
  # project edition would read as `current()` and wave through a real downgrade.
  # Only a genuinely absent/unreadable project falls back to the default.
  def migrate_project_edition(dir \\ ".") do
    case Cure.Edition.resolve(%{project_dir: dir}) do
      {:ok, ed} ->
        {:ok, ed}

      {:error, {:unknown_edition, ed}} = err ->
        migration_error(:invalid_project_edition, %{
          edition: ed,
          path: Path.join(dir, "Cure.toml")
        })

        err

      {:error, _} ->
        {:ok, Cure.Edition.current()}
    end
  end

  # `--edition YYYY` (validated against the known-editions allow-list) or the
  # compiler default edition (`Cure.Edition.current/0`) when the flag is absent.
  # NB: the default is decoupled from the newest *known* edition (staged rollout),
  # so an absent flag targets the default, not necessarily the newest minted one.
  defp migrate_resolve_edition(opts) do
    case Keyword.get(opts, :edition) do
      nil ->
        {:ok, Cure.Edition.current()}

      raw ->
        case Cure.Edition.parse(raw) do
          {:ok, _} ->
            {:ok, raw}

          {:error, {:unknown_edition, _}} = err ->
            migration_error(:unknown_target_edition, %{edition: raw})
            err
        end
    end
  end

  @doc false
  # Pure planning: refuse a downgrade target (target older than the project's
  # current declared edition).
  def plan_migration(opts) do
    target = Keyword.fetch!(opts, :target)
    current = Keyword.get(opts, :current, Cure.Edition.current())
    if Cure.Edition.compare(target, current) == :lt, do: {:error, :downgrade}, else: {:ok, target}
  end

  @doc false
  # Pure planning for one source: run the crossing rule set to a fixpoint; if a
  # blocking :manual item fired, report it; else return the migrated source and
  # the pending edition bump. The :blocked clause is checked BEFORE strict?, so a
  # :manual item is never promoted to a :strict_violation — it stays a block
  # (spec §8: --strict does not promote :manual).
  def plan_migration_source(src, opts) do
    {src, _legacy_otp_changed?} = Cure.Migrate.LegacyOtp.normalize(src)
    target = Keyword.fetch!(opts, :target)
    # Parse the INPUT under the SOURCE edition (`:from`, the file's current
    # edition), NOT the target (F-B). A keyword retired *at* target is still a
    # keyword below it; parsing the input under target would lex the to-be-removed
    # construct as a bare identifier, the crossing rule would never match, and the
    # bump would fire on an unrewritten file. Defaults to `target` for callers
    # that predate the split (behaviourally identical while only one edition
    # exists). The verify reparse (below) stays on `target` — the OUTPUT is target
    # syntax (I2/F12).
    from = Keyword.get(opts, :from, target)

    # A file whose current edition (`from`, from its own @edition pragma) is NEWER
    # than the migration target is a per-file DOWNGRADE. The project-level guard
    # (plan_migration/1) only measures the target against the project edition, so a
    # file that pins a newer edition would otherwise be "migrated" downward onto an
    # older keyword set (Finding 2). Refuse it here, mirroring plan_migration/1.
    if Cure.Edition.compare(from, target) == :gt do
      {:error, :downgrade}
    else
      plan_migration_source_crossing(src, target, from, opts)
    end
  end

  defp plan_migration_source_crossing(src, target, from, opts) do
    file = Keyword.get(opts, :file, "nofile")

    {:ok, toks, trivia} =
      Cure.Compiler.Lexer.tokenize(src, file: file, trivia: true, edition: from)

    {:ok, ast} =
      Cure.Compiler.Parser.parse(toks, file: file, emit_events: false, edition: from)

    attached = Cure.Compiler.Trivia.attach(ast, trivia)
    rules = Cure.Migrate.rules_for_crossing(target)

    case Cure.Migrate.run_to_fixpoint(attached, file: file, rules: rules, edition: target) do
      {:ok, out_ast, warns} ->
        blocking =
          Cure.Migrate.blocking_manual(target)
          |> Enum.map(& &1.id)
          |> Enum.filter(fn id -> Enum.any?(warns, &(&1.rule == id)) end)

        strict? = Keyword.get(opts, :strict, false)
        fixable_fired = fixable_tier_warnings(warns, target)

        cond do
          blocking != [] ->
            # :manual blocks the bump regardless of --strict (never promoted, §8)
            {:blocked, blocking}

          strict? and fixable_fired != [] ->
            # --strict promotes fixable-tier (:machine/:review) warnings to errors
            {:error, {:strict_violation, fixable_fired}}

          true ->
            {:ok, Cure.Compiler.Printer.quoted_to_string(out_ast), warns, target}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  # The ids of fired warnings whose rule is a fixable tier (:machine/:review).
  defp fixable_tier_warnings(warns, target) do
    fixable_ids =
      Cure.Migrate.rules_for_crossing(target)
      |> Enum.filter(&(&1.tier in [:machine, :review]))
      |> Enum.map(& &1.id)
      |> MapSet.new()

    warns |> Enum.map(& &1.rule) |> Enum.filter(&MapSet.member?(fixable_ids, &1)) |> Enum.uniq()
  end

  # Target selection mirrors cmd_fmt/2 exactly (explicit paths with dir
  # expansion, else the lib/** + test/** corpus under cwd).
  defp migrate_targets(paths) do
    case paths do
      [] ->
        Path.wildcard("lib/**/*.cure") ++ Path.wildcard("test/**/*.cure")

      _ ->
        Enum.flat_map(paths, fn p ->
          if File.dir?(p), do: Path.wildcard(Path.join(p, "**/*.cure")), else: [p]
        end)
    end
  end

  # --check/--print are read-only and git-guard-exempt; every writing mode runs
  # the preflight guard first and reports git_guard/1's per-file list intact.
  defp migrate_git_guard(_files, true, _print?), do: :ok
  defp migrate_git_guard(_files, _check?, true), do: :ok

  defp migrate_git_guard(files, _check?, _print?) do
    case Cure.Migrate.git_guard(files) do
      :ok ->
        :ok

      {:error, reasons} ->
        Enum.each(reasons, fn {path, reason} ->
          migration_error(:git_guard, %{path: path, reason: reason})
        end)

        {:error, {:git_guard_failed, reasons}}
    end
  end

  # In-memory batch preflight (spec §5.8 / §6.1): run every file through the
  # crossing rule set to a fixpoint (which itself verifies reparse + comment
  # preservation on every pass). Only if ALL files pass is anything written; on
  # any failure, write nothing and report the failing file(s). A file whose
  # migration is blocked by a fired :manual rule is reported per-file (with the
  # hand-port rule ids) as a phase-1 block that skips the write — NOT as a bare
  # parse failure. The :blocked routing here (and in plan_migration_source/2) is
  # what keeps a :manual item from ever reaching the --strict gate, so it is
  # never promoted to a :strict_violation (spec §8).
  defp migrate_preflight_all(files, target, source_edition) do
    results = Enum.map(files, &migrate_preflight_file(&1, target, source_edition))
    failed = for {:error, path} <- results, do: path
    blocked = for {:blocked, path, ids} <- results, do: {path, ids}
    downgraded = for {:downgrade, path, from, tgt} <- results, do: {path, from, tgt}

    cond do
      downgraded != [] ->
        # A file pins an edition newer than the target — refuse the whole run
        # rather than silently downgrade any file (Finding 2), mirroring the
        # project-level downgrade guard in plan_migration/1.
        Enum.each(downgraded, fn {path, from, tgt} ->
          migration_error(:file_downgrade, %{path: path, from: from, target: tgt})
        end)

        {:error, {:downgrade, downgraded}}

      failed != [] ->
        Enum.each(failed, fn path ->
          migration_error(:preflight, %{path: path})
        end)

        {:error, {:preflight_failed, failed}}

      blocked != [] ->
        Enum.each(blocked, fn {path, ids} ->
          migration_error(:manual_required, %{path: path, rules: ids})
        end)

        {:error, {:blocked, blocked}}

      true ->
        {:ok, for({:ok, r} <- results, do: r)}
    end
  end

  defp migrate_preflight_file(file, target, source_edition) do
    with {:ok, source} <- File.read(file),
         {source, _legacy_otp_changed?} <- Cure.Migrate.LegacyOtp.normalize(source),
         # Parse the input under the file's CURRENT edition (its own pragma if it
         # carries one, else the project's edition) — see plan_migration_source/2
         # (F-B). The verify reparse inside the fixpoint stays on `target`.
         from = Cure.Edition.pragma_edition(source) || source_edition,
         {:ok, toks, trivia} <-
           Cure.Compiler.Lexer.tokenize(source, file: file, trivia: true, edition: from),
         {:ok, in_ast} <-
           Cure.Compiler.Parser.parse(toks, file: file, emit_events: false, edition: from) do
      # Baseline = the un-migrated input reprinted the same way plan_migration_source/2
      # prints the migrated AST, so `changed?` reflects a real rule rewrite (the old
      # `new_ast != attached`), not incidental reformatting.
      baseline =
        Cure.Compiler.Printer.quoted_to_string(Cure.Compiler.Trivia.attach(in_ast, trivia))

      case plan_migration_source(source, target: target, from: from, file: file) do
        {:ok, printed, warnings, bump} ->
          output = if String.ends_with?(printed, "\n"), do: printed, else: printed <> "\n"

          {:ok,
           %{
             path: file,
             input: source,
             output: output,
             changed?: printed != baseline,
             warnings: warnings,
             bump: bump
           }}

        {:blocked, ids} ->
          {:blocked, file, ids}

        {:error, :downgrade} ->
          {:downgrade, file, from, target}

        {:error, _reason} ->
          {:error, file}
      end
    else
      _ -> {:error, file}
    end
  end

  # --strict promotes fixable-tier (:machine/:review) warnings to errors; write
  # nothing. A file blocked only by a :manual rule never reaches here — it is
  # already reported by migrate_preflight_all/2's :blocked path (spec §8:
  # --strict does not promote :manual).
  defp migrate_strict_gate(_results, _target, false), do: :ok

  defp migrate_strict_gate(results, target, true) do
    violators =
      for r <- results,
          ids = fixable_tier_warnings(r.warnings, target),
          ids != [],
          do: {r.path, ids}

    if violators == [] do
      :ok
    else
      Enum.each(violators, fn {path, ids} ->
        migration_error(:strict_warning, %{path: path, rules: ids})
      end)

      {:error, {:strict_violation, violators}}
    end
  end

  # Phase 2 of the two-phase migrate: write the rewritten files (unless
  # --check/--print), then, only if every targeted file succeeded, bump the
  # edition marker toward `target`. The bump writes only when it actually raises
  # the edition (target strictly greater than the current marker), so a routine
  # `cure migrate` at the latest edition never gratuitously stamps a pragma or
  # rewrites Cure.toml.
  defp migrate_apply_and_bump(results, target, paths, check?, print?) do
    case migrate_apply(results, check?, print?) do
      :ok ->
        # Propagate a bump failure (e.g. Cure.toml could not be stamped) so the
        # command exits non-zero instead of falsely reporting success.
        migrate_bump(results, target, paths, check?, print?)

      other ->
        other
    end
  end

  defp migrate_apply(results, true, _print?) do
    # --check: report the files a migration would change as reviewable,
    # git-style unified diffs; never writes.
    pending = for r <- results, r.changed?, do: r.path

    Enum.each(results, fn result ->
      if result.changed?, do: print_migration_diff(result)
    end)

    if pending == [], do: :ok, else: {:error, {:pending, pending}}
  end

  defp migrate_apply(results, _check?, true) do
    # --print: emit every file's migrated form to stdout; never writes.
    Enum.each(results, fn r -> IO.puts(r.output) end)
    :ok
  end

  defp migrate_apply(results, _check?, _print?) do
    # Default: write each file a migration actually changed.
    Enum.each(results, fn r ->
      if r.changed? do
        File.write!(r.path, r.output)
        info("migrated: #{r.path}")
      end
    end)

    :ok
  end

  defp print_migration_diff(%{path: path, input: input, output: output}) do
    id = System.unique_integer([:positive])
    dir = Path.join(System.tmp_dir!(), "cure_migrate_diff_#{id}")
    before = Path.join(dir, "before.cure")
    after_path = Path.join(dir, "after.cure")

    label =
      if Path.type(path) == :absolute do
        Path.basename(path)
      else
        Path.relative_to_cwd(path)
      end

    source_label = String.trim_leading(path, "/")

    File.mkdir_p!(dir)
    File.write!(before, input)
    File.write!(after_path, output)

    try do
      {diff, _status} =
        System.cmd(
          "git",
          [
            "diff",
            "--no-index",
            "--no-color",
            "--unified=3",
            "--src-prefix=a/",
            "--dst-prefix=b/",
            before,
            after_path
          ],
          stderr_to_stdout: true
        )

      diff =
        diff
        |> String.replace("a/#{String.trim_leading(before, "/")}", "a/#{label}")
        |> String.replace("b/#{String.trim_leading(after_path, "/")}", "b/#{label}")
        |> String.replace("a//#{String.trim_leading(before, "/")}", "a/#{label}")
        |> String.replace("b//#{String.trim_leading(after_path, "/")}", "b/#{label}")
        |> String.replace("a//#{source_label}", "a/#{label}")
        |> String.replace("b//#{source_label}", "b/#{label}")

      IO.write(diff)
    after
      File.rm_rf!(dir)
    end
  end

  # Bump the edition marker to `target` (phase 2). A whole-project run (no
  # explicit paths) with a resolvable Cure.toml bumps its `edition` key; a
  # standalone-file run splices/replaces each file's leading `@edition` pragma.
  # In every mode the bump only writes when `target` is strictly newer than the
  # existing marker. --check/--print never write; they only report the pending
  # bump when it would raise the edition.
  defp migrate_bump(results, target, paths, check?, print?) do
    # The cond's value is the command result: :ok everywhere except a project
    # edition-stamp failure, which returns {:error, reason} so the caller fails.
    cond do
      check? ->
        if migrate_project_bump?(paths, target) or Enum.any?(results, &migrate_file_bump?(&1.path, target)),
          do: info("would bump edition to #{target}")

        :ok

      print? ->
        if migrate_project_bump?(paths, target) or Enum.any?(results, &migrate_file_bump?(&1.path, target)),
          do: IO.puts("# pending edition bump: #{target}")

        :ok

      paths == [] and migrate_project_bump?(paths, target) ->
        case Cure.Project.set_edition(Path.join(".", "Cure.toml"), target) do
          :ok ->
            info("bumped project edition to #{target}")
            :ok

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("edition bump", reason))

            {:error, reason}
        end

      true ->
        Enum.each(results, fn r ->
          if migrate_file_bump?(r.path, target) do
            File.write!(r.path, migrate_splice_edition(File.read!(r.path), target))
            info("bumped #{r.path} to edition #{target}")
          end
        end)

        :ok
    end
  end

  # A whole-project run whose Cure.toml declares an edition strictly older than
  # `target` (an absent marker means the current edition — no bump).
  defp migrate_project_bump?([], target) do
    case Cure.Project.load(".") do
      {:ok, %{edition: ed}} when is_binary(ed) -> Cure.Edition.compare(target, ed) == :gt
      _ -> false
    end
  end

  defp migrate_project_bump?(_paths, _target), do: false

  # A standalone file whose leading `@edition` pragma (if any) is strictly older
  # than `target`. No pragma means the current edition — no bump.
  defp migrate_file_bump?(path, target) do
    case File.read(path) do
      {:ok, body} ->
        case migrate_edition_pragma(body) do
          nil -> false
          ed -> Cure.Edition.compare(target, ed) == :gt
        end

      _ ->
        false
    end
  end

  @doc false
  # Extract a FILE-LEADING `@edition("YYYY")` marker for the phase-2 bump. Routed
  # through Cure.Edition.pragma_edition so detection is anchored to the first
  # substantive line (skipping leading blank/comment trivia) — an `@edition(...)`
  # buried in a comment or string is NOT a pragma and must not trigger a bump
  # (Finding 1). That helper also mirrors the parser's interior whitespace (F-C)
  # and restricts the capture to a 4-digit year (F9), so a malformed value reads
  # as "no marker" (nil) rather than flowing into compare/2.
  def migrate_edition_pragma(body), do: Cure.Edition.pragma_edition(body)

  @doc false
  # Replace an existing file-leading `@edition("…")` pragma in place, or splice a
  # new one at the very top (the pragma must precede any statement, spec §4). The
  # leading pragma is the first substantive line (Cure.Edition.pragma_edition
  # agrees), so we replace THAT line rather than a whole-body regex match — a
  # global-less regex would otherwise rewrite an earlier in-comment mention
  # (Finding 1). No leading pragma → prepend one at the very top.
  def migrate_splice_edition(body, target) do
    if migrate_edition_pragma(body) do
      replace_leading_pragma_line(body, target)
    else
      "@edition(\"#{target}\")\n" <> body
    end
  end

  # The leading pragma sits on the first substantive line. We locate THAT line
  # via Cure.Edition.leading_line_index/1 — the same fence-aware scan the resolver
  # uses — rather than a local trivia test, so a `###`-fenced doc comment before
  # the pragma (whose body lines need not start with `#`) is skipped identically
  # and we never rewrite a line buried in a comment. Rewrite only the `@edition(…)`
  # TOKEN on that line — NOT the whole line — so anything after the `)` (a trailing
  # comment) survives (A3-F2), and a lone-CR file whose "first line" is the whole
  # body keeps its body (A3-F1). The token regex mirrors Cure.Edition.pragma_capture
  # (anchored `^@`, interior whitespace tolerated); the trailing "\r" of a CRLF/CR
  # line lands after the match and is preserved for free — no separate EOL fixup.
  @edition_token ~r/^@\s*edition\s*\(\s*"\d{4}"\s*\)/
  defp replace_leading_pragma_line(body, target) do
    lines = String.split(body, "\n")
    idx = Cure.Edition.leading_line_index(body)
    rewritten = Regex.replace(@edition_token, Enum.at(lines, idx), "@edition(\"#{target}\")", global: false)
    lines |> List.replace_at(idx, rewritten) |> Enum.join("\n")
  end

  # v0.21.0: algebra formatter is now the default. It renders the
  # buffer from the AST using `Cure.Compiler.Algebra` and
  # `Cure.Compiler.AlgebraFormatter`, with round-trip verification that
  # falls back to the original source when the rewrite would change
  # program structure.
  defp fmt_algebra(files) do
    Enum.each(files, fn file ->
      source = read_source_or_exit(file)

      case Cure.Compiler.Formatter.format_algebra(source) do
        {:ok, ^source} ->
          :ok

        {:ok, formatted} ->
          File.write!(file, formatted)
          info("  formatted (algebra) #{file}")
      end
    end)
  end

  defp fmt_safe(files) do
    Enum.each(files, fn file ->
      source = read_source_or_exit(file)

      case Cure.Compiler.Formatter.format(source) do
        {:ok, ^source} ->
          :ok

        {:ok, formatted} ->
          File.write!(file, formatted)
          info("  formatted #{file}")
      end
    end)
  end

  # `cure fmt --diff` (--dry-run flag): shows a red/green unified diff
  # for every file that would be reformatted, without touching disk.
  # Exits with code 1 when any file has pending changes (CI-friendly).
  defp fmt_diff(files) do
    changed =
      Enum.reduce(files, 0, fn file, count ->
        source = read_source_or_exit(file)
        {:ok, formatted} = Cure.Compiler.Formatter.format_algebra(source)

        if formatted == source do
          count
        else
          render_unified_diff(file, source, formatted)
          count + 1
        end
      end)

    if changed == 0 do
      info("All files are formatted")
    else
      error_diagnostic(
        Cure.Diagnostic.Operational.command_failure(
          "cure fmt --diff",
          "#{changed} file(s) would be reformatted"
        )
      )

      exit({:shutdown, 1})
    end
  end

  # Render a colour-annotated unified diff of two multi-line strings.
  # Red lines (-) are present in `original` but not in `formatted`.
  # Green lines (+) are present in `formatted` but not in `original`.
  # Uses `List.myers_difference/2` so the output is minimal and
  # stable. No external tooling required.
  defp render_unified_diff(file, original, formatted) do
    orig_lines = String.split(original, "\n")
    fmt_lines = String.split(formatted, "\n")

    ansi? = IO.ANSI.enabled?()
    red = if ansi?, do: IO.ANSI.red(), else: ""
    green = if ansi?, do: IO.ANSI.green(), else: ""
    reset = if ansi?, do: IO.ANSI.reset(), else: ""
    dim = if ansi?, do: IO.ANSI.faint(), else: ""

    info("#{dim}--- #{file} (original)#{reset}")
    info("#{dim}+++ #{file} (formatted)#{reset}")

    List.myers_difference(orig_lines, fmt_lines)
    |> Enum.each(fn
      {:eq, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{dim} #{l}#{reset}") end)

      {:del, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{red}-#{l}#{reset}") end)

      {:ins, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{green}+#{l}#{reset}") end)
    end)
  end

  # v0.21.0: `cure fmt --check` runs through the algebra formatter so
  # it agrees with the new default. Falls back to the original source
  # internally when round-trip verification fails, so it never reports
  # a file as "needs formatting" solely because of a known-unsupported
  # layout edge case.
  defp fmt_check(files) do
    mismatched =
      Enum.filter(files, fn file ->
        source = read_source_or_exit(file)
        {:ok, formatted} = Cure.Compiler.Formatter.format_algebra(source)
        formatted != source
      end)

    case mismatched do
      [] ->
        info("All files are formatted")

      _ ->
        Enum.each(mismatched, fn file -> info("  needs formatting: #{file}") end)
        exit({:shutdown, 1})
    end
  end

  defp fmt_aggressive(files) do
    error_diagnostic(Cure.Diagnostic.Operational.destructive_format_warning(%{files: files}))

    outcomes =
      Enum.map(files, fn file ->
        source = read_source_or_exit(file)

        with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false),
             {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false) do
          formatted = Cure.Compiler.Printer.quoted_to_string(ast)
          File.write!(file, formatted <> "\n")
          info("  formatted #{file}")
          :ok
        else
          {:error, reason} ->
            {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)
            emit_diagnostic(diagnostic, registry)

            :error
        end
      end)

    # A file the formatter could not parse must fail the command, not be
    # reported as a successful format run.
    if Enum.any?(outcomes, &(&1 == :error)), do: exit({:shutdown, 1})
  end

  # -- watch ---------------------------------------------------------------------

  defp cmd_watch(paths, opts) do
    path = List.first(paths) || "."

    action =
      case Keyword.get(opts, :action, "compile") do
        "compile" -> :compile
        "check" -> :check
        "test" -> :test
        other -> String.to_atom(other)
      end

    watch_opts = [action: action]

    watch_opts =
      if v = Keyword.get(opts, :poll_ms), do: Keyword.put(watch_opts, :poll_ms, v), else: watch_opts

    watch_opts =
      if v = Keyword.get(opts, :debounce),
        do: Keyword.put(watch_opts, :debounce, v),
        else: watch_opts

    Cure.Watch.start(path, watch_opts)
  end

  # -- new -----------------------------------------------------------------------

  defp cmd_new([], _opts), do: usage_error("Usage: cure new <name> [--lib | --app | --fsm]")

  defp cmd_new([name | _], opts) do
    template =
      cond do
        Keyword.get(opts, :app) -> :app
        Keyword.get(opts, :fsm) -> :fsm
        Keyword.get(opts, :lib) -> :lib
        Keyword.get(opts, :template) -> String.to_atom(Keyword.get(opts, :template))
        true -> :lib
      end

    Cure.Project.scaffold(name, template)
    IO.puts(Cure.CLI.NewMessage.render(name, template))
  end

  # -- bench ---------------------------------------------------------------------

  defp cmd_bench(paths, _opts) do
    files =
      case paths do
        [] -> Path.wildcard("bench/**/*.cure") ++ Path.wildcard("test/**/*_bench.cure")
        _ -> paths
      end

    if files == [] do
      info("No benchmark files found. Place benchmarks under bench/*.cure")
    else
      outcomes =
        Enum.map(files, fn f ->
          case File.read(f) do
            {:ok, src} ->
              case Cure.Compiler.compile_and_load(src, file: f, emit_events: false) do
                {:ok, mod} ->
                  exports = mod.module_info(:exports)

                  bench_fns =
                    Enum.filter(exports, fn {n, a} ->
                      String.starts_with?(Atom.to_string(n), "bench") and a == 0
                    end)

                  Enum.each(bench_fns, fn {name, _} ->
                    {us, _} = :timer.tc(fn -> apply(mod, name, []) end)
                    info("  #{f}:#{name}  #{us / 1000} ms")
                  end)

                  :ok

                {:error, reason} ->
                  emit_host_diagnostic(reason, f, src)

                  :error
              end

            {:error, reason} ->
              error_diagnostic(Cure.Diagnostic.Operational.file_read(f, reason))
              :error
          end
        end)

      # A benchmark file that failed to read or compile must fail the command.
      if Enum.any?(outcomes, &(&1 == :error)), do: exit({:shutdown, 1})
    end
  end

  # -- explain ------------------------------------------------------------------

  defp cmd_explain_all do
    entries = Cure.Compiler.Errors.list_all()
    code_width = entries |> Enum.map(fn {c, _, _} -> String.length(c) end) |> Enum.max(fn -> 4 end)

    info("Known error codes (run 'cure explain <code>' for full details):\n")

    Enum.each(entries, fn {code, title, brief} ->
      padded = String.pad_trailing(code, code_width)
      info("  #{padded}  #{title}")
      if brief != "", do: info("          #{brief}")
    end)
  end

  defp cmd_explain(code) do
    case Cure.Compiler.Errors.explain(code) do
      {:ok, text} -> info(text)
      :error -> usage_error("Unknown error code: #{code}. Run 'cure explain' for a list.")
    end
  end

  # -- doctor -------------------------------------------------------------------

  defp cmd_doctor(_opts) do
    report = Cure.Doctor.run(".")
    _ = Cure.Doctor.render(report)

    unless report.ok?, do: exit({:shutdown, 1})
  end

  # -- fix ----------------------------------------------------------------------

  defp cmd_fix(opts) do
    dry? = Keyword.get(opts, :dry_run, false)
    results = Cure.Fix.run(".", dry_run: dry?)
    changed = Enum.filter(results, & &1.changed?)

    case {changed, dry?} do
      {[], _} ->
        info("cure fix: nothing to change.")

      {_, true} ->
        Enum.each(changed, fn r ->
          info("  would fix #{r.file}: #{Enum.join(Enum.map(r.applied, &Atom.to_string/1), ", ")}")
        end)

        exit({:shutdown, 1})

      {_, false} ->
        Enum.each(changed, fn r ->
          info("  fixed #{r.file}: #{Enum.join(Enum.map(r.applied, &Atom.to_string/1), ", ")}")
        end)

        info("cure fix: #{length(changed)} file(s) rewritten.")
    end
  end

  # -- publish / search / info -----------------------------------------------

  defp cmd_publish(opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    cond do
      Keyword.get(opts, :hex, false) ->
        case Cure.Project.Publisher.build_hex_tarball(".") do
          {:ok, bytes} ->
            path = "_build/cure/publish/hex.tar"
            File.mkdir_p!(Path.dirname(path))
            File.write!(path, bytes)
            info("Hex-compatible tarball written to #{path}")
            info("Next: `mix hex.publish package --replace` with the tarball above.")

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure publish --hex", reason))

            exit({:shutdown, 1})
        end

      Keyword.get(opts, :dry_run, false) ->
        case Cure.Project.Publisher.build_tarball(".") do
          {:ok, bytes, sha, manifest} ->
            info("Would upload #{manifest["name"]} #{manifest["version"]}")
            info("  sha256 = #{sha}")
            info("  size   = #{byte_size(bytes)} bytes")
            info("  files  = #{length(Map.get(manifest, "dependencies", []))} declared deps")

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure publish --dry-run", reason))

            exit({:shutdown, 1})
        end

      true ->
        handle =
          Keyword.get(opts, :handle) ||
            System.get_env("CURE_HANDLE") ||
            prompt("Maintainer handle: ")

        token =
          Keyword.get(opts, :token) ||
            System.get_env("CURE_TOKEN") ||
            prompt("Upload token: ")

        case Cure.Project.Publisher.publish(".", handle, token) do
          {:ok, resp} ->
            info("Published: #{inspect(resp)}")

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure publish", reason))

            exit({:shutdown, 1})
        end
    end
  end

  defp cmd_search(query, opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    case Cure.Project.Registry.search(query) do
      {:ok, hits} ->
        if hits == [] do
          info("No hits for '#{query}'.")
        else
          Enum.each(hits, fn h ->
            info("  #{Map.get(h, "name", "?")} #{Map.get(h, "version", "?")} -- #{Map.get(h, "description", "")}")
          end)
        end

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure search", reason))

        exit({:shutdown, 1})
    end
  end

  defp cmd_info(name_version, opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    {name, maybe_version} =
      case String.split(name_version, ":", parts: 2) do
        [n, v] -> {n, v}
        [n] -> {n, nil}
      end

    case maybe_version do
      nil ->
        case Cure.Project.Registry.list_versions(name) do
          {:ok, versions} ->
            info("#{name}:")

            Enum.each(versions, fn v ->
              info("  #{v.version}  (sha256: #{v.sha256})")
            end)

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure info", reason))

            exit({:shutdown, 1})
        end

      v ->
        case Cure.Project.Registry.fetch_manifest(name, v) do
          {:ok, manifest} ->
            IO.puts(Cure.Project.Json.encode(manifest))

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure info", reason))

            exit({:shutdown, 1})
        end
    end
  end

  defp cmd_keys_generate(handle) do
    try do
      case Cure.Project.Signing.generate_keypair(handle) do
        {:ok, ^handle} ->
          info("Generated keypair for '#{handle}' under ~/.cure/keys/")

        other ->
          raise Cure.Diagnostic.UnhandledError, error: {:unexpected_key_generation_result, other}
          exit({:shutdown, 1})
      end
    rescue
      e ->
        error_diagnostic(Cure.Diagnostic.Operational.internal_exception(e, __STACKTRACE__, context: "key generation"))

        exit({:shutdown, 1})
    end
  end

  # -- release ------------------------------------------------------------------

  defp cmd_release(_rest, opts) do
    case Cure.Project.load() do
      {:ok, project} ->
        release_opts =
          [
            include_erts: Keyword.get(opts, :include_erts, false),
            output_dir: Keyword.get(opts, :output_dir),
            overwrite: Keyword.get(opts, :overwrite, true)
          ]
          |> Enum.reject(fn {_k, v} -> is_nil(v) end)

        case Cure.Release.build(project, release_opts) do
          {:ok, dir} ->
            info("Release built: #{dir}")

          {:error, reason} ->
            error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure release", reason))

            exit({:shutdown, 1})
        end

      {:error, :no_project_file} ->
        error_diagnostic(Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent))
        exit({:shutdown, 1})

      {:error, reason} ->
        error_diagnostic(Cure.Diagnostic.Operational.command_failure("cure release", reason))

        exit({:shutdown, 1})
    end
  end

  defp cmd_keys_list do
    trusted = Cure.Project.Signing.trusted_keys()

    if map_size(trusted) == 0 do
      info("No trusted keys. Generate one with `cure keys generate <handle>`.")
    else
      Enum.each(trusted, fn {h, pub} ->
        info("  #{h}  #{Base.encode16(pub, case: :lower) |> String.slice(0, 16)}...")
      end)
    end
  end

  defp prompt(msg) do
    IO.gets(msg) |> to_string() |> String.trim()
  end

  # -- version / help ----------------------------------------------------------

  defp cmd_version do
    IO.puts("Cure #{version()}")
  end

  defp help do
    IO.puts("""
    Cure #{version()} -- Dependently-typed language for the BEAM

    Usage: cure <command> [options] [arguments]

    Commands:
      compile <file|dir>   Compile .cure files to BEAM bytecode
      run <file>           Compile and execute a .cure file
      check <file>         Type-check without compiling
      lsp                  Start the Language Server Protocol server
      stdlib               Compile the standard library
      doc [path|dir]       Generate HTML documentation
      fmt [path|dir]       Format .cure source files (algebra by default; --safe, --aggressive, --check)
      migrate [path|dir]   Port source to an edition (--check, --print, --strict, --edition YYYY)
      repl                 Interactive Cure session (multi-line, :help for commands)
      watch [path]         Recompile/check/test on every save
      new <name>           Scaffold a new project (--lib | --app | --fsm)
      init <name>          Same as `new --lib`
      deps                 Resolve project dependencies
      test [--cover]       Run .cure tests under test/, optionally with coverage
      bench [path]         Run .cure benchmarks under bench/
      explain <Eddd>       Explain an error code
      why <Eddd>           Alias for `explain`
      doctor               Environment + project + source health report
      fix [--dry-run]      Apply safe project-wide code fixes
      publish [opts]       Package and upload to the Cure registry
      search <query>       Search the registry for packages
      info <name[:ver]>    Show registry manifest / version list
      keys generate <h>    Generate an Ed25519 signing keypair
      keys list            List trusted publisher keys
      release              Build a BEAM release (requires `app`)
      trace <M.f/a>        Typed tracer over :dbg (--duration N)
      john                 Print everything: VM stats, tooling, project, logs
      version              Show version
      help                 Show this help

    Options:
      -o, --output-dir DIR   Output directory (default: _build/cure/project/ebin)
      --action ACTION        Watch action: compile (default) | check | test
      --poll-ms N            Watch poll interval (default 500)
      --debounce N           Watch coalesce window (default 200)
      --check                Report pending formatting or migrations without writing
      --print                Print migrated source without writing
      --strict               Reject review-required migration warnings
      --edition YYYY         Target language edition for `migrate`
      --lib | --app | --fsm  `cure new` template selector
      --filter PATTERN       `cure test` filter
      --doctests             `cure test` includes doctests
      --cover                `cure test --cover` emits _build/cure/cover/index.html
      --dry-run              `cure fix --dry-run`, `cure publish --dry-run`
      --hex                  `cure publish --hex` -- Hex-compatible tarball
      --handle HANDLE        Maintainer handle for `cure publish`
      --token TOKEN          Upload token for `cure publish`
      --registry URL         Override registry base URL
      --include-erts         `cure release --include-erts` bundles ERTS
      --overwrite            `cure release --overwrite` wipes output dir (default)
      -v, --verbose          Verbose output
      -h, --help             Show help
    """)
  end

  # -- verify (v0.32.0) ---------------------------------------------------------

  defp cmd_verify(rest, opts) do
    strict? = Keyword.get(opts, :strict, false)
    path = List.first(rest)

    Mix.Tasks.Cure.Verify.run(
      if(strict?, do: ["--strict"], else: []) ++
        if(path, do: [path], else: [])
    )
  end

  # -- export-types (v0.32.0) ---------------------------------------------------

  defp cmd_export_types(rest, opts) do
    target = Keyword.get(opts, :target, "protobuf")
    out = Keyword.get(opts, :out)
    verbose? = Keyword.get(opts, :verbose, false)

    cli_args =
      ["--target", target] ++
        if(out, do: ["--out", out], else: []) ++
        if(verbose?, do: ["--verbose"], else: []) ++
        rest

    Mix.Tasks.Cure.ExportTypes.run(cli_args)
  end

  # -- snap (v0.32.0) -----------------------------------------------------------

  defp cmd_snap([], _opts) do
    error_diagnostic(Cure.Diagnostic.Operational.usage("Usage: cure snap <save|load|list> [options]"))

    exit({:shutdown, 1})
  end

  defp cmd_snap([sub | rest], opts) do
    out = Keyword.get(opts, :out)

    cli_args =
      [sub] ++
        if(out, do: ["--out", out], else: []) ++
        rest

    Mix.Tasks.Cure.Snap.run(cli_args)
  end

  # -- story (v0.32.0) ----------------------------------------------------------

  defp cmd_story(opts) do
    out = Keyword.get(opts, :out)
    stdout? = Keyword.get(opts, :verbose, false)
    diagrams? = Keyword.get(opts, :diagrams, false)

    cli_args =
      if(out, do: ["--out", out], else: []) ++
        if(stdout?, do: ["--stdout"], else: []) ++
        if diagrams?, do: ["--diagrams"], else: []

    Mix.Tasks.Cure.Story.run(cli_args)
  end

  # -- Output helpers ----------------------------------------------------------

  defp info(msg), do: IO.puts(msg)

  defp format_invalid_options(invalid) do
    Enum.map_join(invalid, ", ", fn
      {option, nil} -> to_string(option)
      {option, value} -> "#{option}=#{value}"
    end)
  end

  defp error_diagnostic(%Cure.Diagnostic{} = diagnostic) do
    emit_diagnostic(diagnostic)
  end

  defp migration_error(kind, details) do
    error_diagnostic(Cure.Diagnostic.Operational.migration_failure(kind, details))
  end

  defp emit_diagnostic(%Cure.Diagnostic{} = diagnostic, registry \\ nil) do
    case Cure.Diagnostic.Host.emit_diagnostic(diagnostic, registry: registry) do
      {:ok, _sink} -> :ok
      {:error, _reason} -> raise "failed to emit diagnostic"
    end
  end

  defp emit_host_diagnostic(reason, path, source \\ nil) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path, source)
    emit_diagnostic(diagnostic, registry)
  end

  # A user-facing usage/lookup error that must fail the command: print to stderr
  # and exit non-zero, so `cure <misuse> && next` stops and CI wrappers see it.
  defp usage_error(msg) do
    error_diagnostic(Cure.Diagnostic.Operational.usage(msg))
    exit({:shutdown, 1})
  end
end
