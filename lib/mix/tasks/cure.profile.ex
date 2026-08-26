defmodule Mix.Tasks.Cure.Profile do
  @moduledoc """
  Profile the compilation of a Cure source file.

  Shows timing data per pipeline stage and event counts.

  ## Usage

      mix cure.profile path/to/file.cure
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Profile compilation of a Cure source file"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start", [])

    case args do
      [path | _] ->
        case Cure.Profiler.profile_file(path) do
          {:ok, report} ->
            IO.puts(Cure.Profiler.format_report(report))

            case report.diagnostic do
              %{diagnostic: diagnostic, registry: registry} ->
                Mix.shell().error(render_diagnostic(diagnostic, registry))

              nil ->
                :ok
            end

          {:error, reason} ->
            Mix.shell().error(render_host_diagnostic(reason, path))
        end

      [] ->
        Mix.shell().error(
          render_diagnostic(Cure.Diagnostic.Operational.usage("Usage: mix cure.profile <file.cure>"), nil)
        )
    end
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)
    render_diagnostic(diagnostic, registry)
  end

  defp render_diagnostic(diagnostic, registry) do
    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end
end
