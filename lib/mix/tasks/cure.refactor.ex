defmodule Mix.Tasks.Cure.Refactor do
  @shortdoc "Analyze Cure modules and emit deterministic refactor plans"

  @moduledoc """
  Read-only structural analysis for large Cure source modules.

  The analysis phase reports declarations and imports without modifying source.
  Use `--recursive` to include nested declarations, `--stats` for deterministic
  size/kind counts, and `--verbose` to print import details. `--checked` runs the
  canonical compiler pipeline before producing the report.

      mix cure.refactor path/to/module.cure
      mix cure.refactor --recursive --stats path/to/module.cure
      mix cure.refactor --json --checked path/to/module.cure
  """

  use Mix.Task

  alias Cure.Refactor.Analysis

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [
          json: :boolean,
          checked: :boolean,
          recursive: :boolean,
          stats: :boolean,
          verbose: :boolean,
          max_depth: :integer,
          prelude_macros: :boolean
        ],
        aliases: [j: :json, c: :checked, r: :recursive, v: :verbose]
      )

    start_app(opts)

    cond do
      invalid != [] ->
        usage_error("Invalid options for mix cure.refactor: #{inspect(invalid)}")

      length(paths) != 1 ->
        usage_error(
          "Usage: mix cure.refactor [--json] [--checked] [--recursive] [--stats] " <>
            "[--verbose] [--max-depth N] <path.cure>"
        )

      true ->
        analyze(Path.expand(hd(paths)), opts)
    end
  end

  defp start_app(opts) do
    if Keyword.get(opts, :json, false) do
      # Mix has already compiled the task before invoking it. Starting the
      # application directly avoids re-entering the project's compile alias,
      # whose stdlib/escript progress output would corrupt a JSON document.
      case Application.ensure_all_started(:cure) do
        {:ok, _started} -> :ok
        {:error, reason} -> Mix.raise("could not start Cure: #{inspect(reason)}")
      end
    else
      Mix.Task.run("app.start", [])
    end
  end

  defp analyze(path, opts) do
    analysis_opts =
      Keyword.take(opts, [:checked, :recursive, :stats, :verbose, :max_depth, :prelude_macros])

    case Analysis.analyze(path, analysis_opts) do
      {:ok, report} ->
        if Keyword.get(opts, :json, false),
          do: IO.puts(Analysis.to_json(report)),
          else: IO.puts(Analysis.format(report, opts))

        :ok

      {:error, reason} ->
        Mix.shell().error(Cure.Diagnostic.Host.render(reason, path))
        Mix.raise("refactor analysis failed")
    end
  end

  defp usage_error(message) do
    Mix.shell().error(Cure.Diagnostic.Host.render({:usage_error, message}, "nofile"))
    Mix.raise(message)
  end
end
