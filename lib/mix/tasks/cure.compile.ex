defmodule Mix.Tasks.Cure.Compile do
  @moduledoc """
  Compiles Cure source files to BEAM bytecode.

  ## Usage

      mix cure.compile path/to/file.cure
      mix cure.compile path/to/directory/

  ## Options

  - `--output-dir` -- artifact-set root (default: `_build/cure/project/ebin`)
  - `--warn-import-cycles` -- report legal `use` cycles after compilation
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Compiles Cure source files to BEAM bytecode"

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [output_dir: :string, warn_import_cycles: :boolean],
        aliases: [o: :output_dir]
      )

    if invalid != [] do
      usage_error("Invalid options for mix cure.compile: #{inspect(invalid)}")
    end

    output_dir = Keyword.get(opts, :output_dir, "_build/cure/project/ebin")
    warn_import_cycles? = Keyword.get(opts, :warn_import_cycles, false)

    if paths == [] do
      usage_error("Usage: mix cure.compile <path> [--output-dir DIR]")
    end

    # Ensure the application is started (for Registry)
    Mix.Task.run("app.start", [])

    Enum.each(paths, fn path ->
      if File.dir?(path) do
        compile_dir(path, output_dir, warn_import_cycles?)
      else
        compile_one(path, output_dir, warn_import_cycles?)
      end
    end)
  end

  defp compile_dir(path, output_dir, warn_import_cycles?) do
    files = path |> Path.join("**/*.cure") |> Path.wildcard()

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           source_roots: [path],
           output_dir: output_dir,
           kind: :project,
           repair: true,
           verify_stdlib: true,
           stdlib_artifact_digest: Cure.Compiler.Artifacts.stdlib_fingerprint()
         ) do
      {:ok, result} ->
        if warn_import_cycles? do
          Enum.each(result.cycles, fn walk ->
            Mix.shell().error(render_host_diagnostic({:import_cycle, walk}, path))
          end)
        end

        Mix.shell().info(
          "  #{map_size(result.rebuilt)} compiled, " <>
            "#{length(result.reused)} up-to-date, " <>
            "#{map_size(result.removed)} removed"
        )

      {:error, reason} ->
        render_sweep_error(reason, files, path)
        exit({:shutdown, 1})
    end
  end

  defp compile_one(path, output_dir, warn_import_cycles?) do
    Mix.shell().info("Compiling #{path}")

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           source_roots: [Path.dirname(path)],
           source_paths: [path],
           output_dir: output_dir,
           kind: :project,
           repair: true,
           verify_stdlib: true,
           stdlib_artifact_digest: Cure.Compiler.Artifacts.stdlib_fingerprint()
         ) do
      {:ok, result} ->
        if warn_import_cycles? do
          Enum.each(result.cycles, fn walk ->
            Mix.shell().error(render_host_diagnostic({:import_cycle, walk}, path))
          end)
        end

        Mix.shell().info("  -> #{result.rebuilt |> Map.keys() |> Enum.join(", ")}")

      {:error, reason} ->
        render_sweep_error(reason, [path], path)
    end
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)
    render_diagnostic(diagnostic, registry)
  end

  defp render_diagnostic(diagnostic, registry \\ nil) do
    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.usage(message)))
    exit({:shutdown, 1})
  end

  defp source_path_for(target, files) do
    if File.exists?(target) do
      target
    else
      module = target |> to_string() |> String.split(".") |> List.last()
      stem = module |> Macro.underscore()

      Enum.find(files, fn path ->
        basename = Path.basename(path, ".cure")
        basename == stem or String.ends_with?(basename, "_" <> stem)
      end) || single_source_or_target(files, target)
    end
  end

  # A standalone source without an enclosing `mod` is represented internally
  # by a synthetic module name which need not resemble its filename. The sweep
  # still has an unambiguous authored source when exactly one file was requested.
  defp single_source_or_target([path], _target), do: path
  defp single_source_or_target(_files, target), do: target

  defp render_sweep_error({:artifact_sweep_failed, errors}, files, _default) do
    Enum.each(errors, fn {target, reason} ->
      Mix.shell().error(render_host_diagnostic(reason, source_path_for(target, files)))
    end)
  end

  defp render_sweep_error(reason, _files, default) do
    Mix.shell().error(render_host_diagnostic(reason, default))
  end
end
