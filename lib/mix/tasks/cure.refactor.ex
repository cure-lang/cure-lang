defmodule Mix.Tasks.Cure.Refactor do
  @shortdoc "Analyze Cure modules and emit deterministic refactor plans"

  @moduledoc """
  Read-only structural analysis for large Cure source modules.

  The first phase intentionally reports declarations and imports only. It does
  not move source text or infer a split from line ranges. Use `--json` for
  machine-readable output and `--checked` to mark a report as checked by the
  caller's requested mode once declaration-level dependency analysis is added.

      mix cure.refactor path/to/module.cure
      mix cure.refactor --json path/to/module.cure
  """

  use Mix.Task

  alias Cure.Refactor.Analysis

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [json: :boolean, checked: :boolean],
        aliases: [j: :json, c: :checked]
      )

    start_app(opts)

    cond do
      invalid != [] -> usage_error("Invalid options for mix cure.refactor: #{inspect(invalid)}")
      length(paths) != 1 -> usage_error("Usage: mix cure.refactor [--json] [--checked] <path.cure>")
      true -> analyze(Path.expand(hd(paths)), opts)
    end
  end

  defp start_app(opts) do
    if Keyword.get(opts, :json, false) do
      previous_shell = Mix.shell()
      Mix.shell(Mix.Shell.Quiet)

      try do
        Mix.Task.run("app.start", [])
      after
        Mix.shell(previous_shell)
      end
    else
      Mix.Task.run("app.start", [])
    end
  end

  defp analyze(path, opts) do
    case Analysis.analyze(path, checked: Keyword.get(opts, :checked, false)) do
      {:ok, report} ->
        if Keyword.get(opts, :json, false),
          do: IO.puts(Analysis.to_json(report)),
          else: IO.puts(Analysis.format(report))

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
