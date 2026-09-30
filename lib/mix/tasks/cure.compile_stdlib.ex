defmodule Mix.Tasks.Cure.CompileStdlib do
  @moduledoc """
  Compiles the Cure standard library from `lib/std/*.cure` to BEAM bytecode.

  The compiled `.beam` files are placed in `_build/cure/ebin/` (or the
  directory given by `--output-dir`) and added to the Erlang code path so
  they can be used by Cure programs at runtime.

  ## Usage

      mix cure.compile_stdlib
      mix cure.compile_stdlib --output-dir path/to/ebin
  """

  use Mix.Task

  @shortdoc "Compiles the Cure standard library"

  @impl Mix.Task
  def run(args) do
    {opts, _, _} =
      OptionParser.parse(args,
        switches: [output_dir: :string],
        aliases: [o: :output_dir]
      )

    output_dir =
      Keyword.get_lazy(opts, :output_dir, fn ->
        Cure.Stdlib.Paths.build_beam_dir(Mix.env(), System.pid())
      end)

    # Ensure the application is started (for Registry).
    # --no-deps-check prevents dependency-validation loops when
    # cure is compiled as a path dependency (env: :prod by default).
    Mix.Task.run("app.start", ["--no-deps-check"])

    stdlib_dir = Path.join(["lib", "std"])
    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure"))
    regex_files = Cure.Stdlib.Packages.regex_sources()
    all_files = cure_files ++ regex_files

    cond do
      not compiler_available?() ->
        Mix.shell().info("Cure.Compiler not yet available, skipping stdlib compilation")
        :ok

      all_files == [] ->
        Mix.shell().info("No .cure files found in #{stdlib_dir}")
        :ok

      true ->
        Mix.shell().info("Compiling Cure standard library (#{length(all_files)} modules)")

        seed_isolated_test_output(output_dir, opts)
        File.mkdir_p!(output_dir)

        progress_key = {__MODULE__, make_ref()}
        diagnostics_key = {__MODULE__, make_ref()}
        Process.put(progress_key, %{count: 0, seen: MapSet.new()})
        Process.put(diagnostics_key, [])

        progress = fn {:compile_started, module, _path} ->
          %{count: count, seen: seen} = Process.get(progress_key)

          if MapSet.member?(seen, module) do
            Mix.shell().info("  [recheck] #{module}")
          else
            current = count + 1
            Process.put(progress_key, %{count: current, seen: MapSet.put(seen, module)})
            Mix.shell().info("  [#{current}/#{length(all_files)}] #{module}")
          end
        end

        collect_diagnostics = fn diagnostics, registry ->
          Process.put(
            diagnostics_key,
            [{diagnostics, registry} | Process.get(diagnostics_key, [])]
          )
        end

        {result, diagnostic_batches} =
          try do
            result =
              Cure.Stdlib.Packages.compile(cure_files, output_dir,
                progress: progress,
                migration_diagnostic_sink: collect_diagnostics,
                compile_opts: [emit_events: false]
              )

            {result, diagnostics_key |> Process.get([]) |> Enum.reverse()}
          after
            Process.delete(progress_key)
            Process.delete(diagnostics_key)
          end

        flush_migration_diagnostics(diagnostic_batches)

        case result do
          {:ok, result} ->
            # Every subsequent consumer in this VM must use the exact verified
            # generation this task produced. In test, that generation is
            # process-local so concurrent Mix VMs cannot mutate it.
            Application.put_env(:cure, :stdlib_beam_dir, result.artifact_root)
            Application.put_env(:cure, :stdlib_compiled_in_vm, result.artifact_root)

            Enum.each(result.cycles, fn walk ->
              Mix.shell().error(render_host_diagnostic({:import_cycle, walk}, stdlib_dir))
            end)

            Mix.shell().info(
              "  #{map_size(result.rebuilt)} compiled, " <>
                "#{length(result.reused)} up-to-date, " <>
                "#{map_size(result.removed)} removed"
            )

            Mix.shell().info("  Output: #{output_dir}")

          {:error, reason} ->
            render_sweep_error(reason, all_files, stdlib_dir)
            exit({:shutdown, 1})
        end
    end
  end

  defp compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end

  # A test VM owns its mutable generation, but it need not rebuild the entire
  # stdlib to obtain one. Seed a new container from the last verified canonical
  # development generation; the sweep immediately below revalidates source and
  # dependency hashes and rebuilds only what changed. Explicit output dirs are
  # caller-owned and are never seeded implicitly.
  defp seed_isolated_test_output(output_dir, opts) do
    canonical = Cure.Stdlib.Paths.build_beam_dir(:dev, :canonical)

    if Mix.env() == :test and not Keyword.has_key?(opts, :output_dir) and
         Cure.Compiler.Artifacts.Writer.resolve(output_dir) == output_dir and
         Path.expand(output_dir) != Path.expand(canonical) do
      case Cure.Compiler.Artifacts.copy_verified_set(canonical, output_dir) do
        {:ok, _generation} -> :ok
        {:error, _reason} -> :ok
      end
    end
  end

  defp flush_migration_diagnostics(batches) do
    Enum.each(batches, fn {diagnostics, registry} ->
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
    end)
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)

    Cure.Diagnostic.Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  defp source_path_for(target, files) do
    if File.exists?(target) do
      target
    else
      module = target |> to_string() |> String.split(".") |> List.last()
      stem = Macro.underscore(module)

      Enum.find(files, target, fn path ->
        basename = Path.basename(path, ".cure")
        basename == stem or String.ends_with?(basename, "_" <> stem)
      end)
    end
  end

  defp render_sweep_error({:artifact_sweep_failed, errors}, files, _default) do
    Enum.each(errors, fn {target, reason} ->
      Mix.shell().error(render_host_diagnostic(reason, source_path_for(target, files)))
    end)
  end

  defp render_sweep_error(reason, _files, default) do
    Mix.shell().error(render_host_diagnostic(reason, default))
  end
end
