defmodule Mix.Tasks.Cure.Check.Stdlib do
  @moduledoc """
  Regression task: compiles every `.cure` file in `lib/std/` and fails
  if any module fails to produce a `.beam` or emits a compiler warning.

  Invoke as:

      mix cure.check.stdlib

  This is intentionally stricter than `mix cure.compile_stdlib`:

  - any error is fatal,
  - any warning is fatal too (the stdlib must be warning-free so
    downstream programs can rely on clean `erl_lint` output).

  CI consumes the exit code to gate merges.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}

  @shortdoc "Compile every Std.* module and reject errors or warnings"

  @stdlib_dir "lib/std"
  @output_dir "_build/cure/ebin"

  @impl Mix.Task
  def run(args) do
    if args != [] do
      usage_error("Usage: mix cure.check.stdlib")
    end

    Application.ensure_all_started(:cure)

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           package: "stdlib",
           kind: :stdlib,
           source_roots: [@stdlib_dir],
           output_dir: @output_dir,
           repair: true,
           compile_opts: [emit_events: false]
         ) do
      {:ok, result} ->
        {:ok, set} = Cure.Compiler.Artifacts.open_verified_set(result.artifact_root)

        Enum.each(set.modules, fn {name, _entry} ->
          IO.puts("  ok  #{pad(name)} -> Cure.#{name}")
        end)

        if map_size(result.warnings) == 0 do
          IO.puts("\nstdlib: #{map_size(set.modules)} passed, 0 failed")
          :ok
        else
          Enum.each(result.warnings, fn {name, warnings} ->
            path = get_in(set.modules, [name, :source, :path]) || @stdlib_dir
            IO.puts("  FAIL #{pad(name)} #{length(warnings)} compiler warning(s)")

            Enum.each(warnings, fn
              {:persisted_warning_count, count} ->
                Mix.shell().error(
                  render_host_diagnostic(
                    {:artifact_error, "The verified module was built with compiler warnings.",
                     %{module: name, warning_count: count}},
                    path
                  )
                )

              warning ->
                Mix.shell().error(render_host_diagnostic({:compiler_warning, warning}, path))
            end)
          end)

          IO.puts(
            "\nstdlib: #{map_size(set.modules) - map_size(result.warnings)} passed, #{map_size(result.warnings)} failed"
          )

          exit({:shutdown, 1})
        end

      {:error, {:artifact_sweep_failed, errors}} ->
        Enum.each(errors, fn {target, reason} ->
          Mix.shell().error(render_host_diagnostic(reason, source_path_for(target, stdlib_files())))
        end)

        IO.puts("\nstdlib: 0 passed, #{length(errors)} failed")
        exit({:shutdown, 1})

      {:error, reason} ->
        Mix.shell().error(render_host_diagnostic(reason, @stdlib_dir))
        IO.puts("\nstdlib: 0 passed, 1 failed")
        exit({:shutdown, 1})
    end
  end

  defp pad(name), do: String.pad_trailing(name, 20)

  defp source_path_for(target, files) do
    cond do
      is_binary(target) and File.regular?(target) ->
        target

      true ->
        Enum.find(files, @stdlib_dir, fn path ->
          case Cure.Compiler.DepGraph.scan([path]) do
            {:ok, %{modules: modules}} -> Map.has_key?(modules, to_string(target))
            _ -> false
          end
        end)
    end
  end

  defp stdlib_files, do: Path.wildcard(Path.join(@stdlib_dir, "**/*.cure"))

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path)

    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
    |> Mix.shell().error()

    exit({:shutdown, 1})
  end
end
