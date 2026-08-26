defmodule Mix.Tasks.Cure.Release do
  @moduledoc """
  Build a BEAM release for a Cure project.

  ## Usage

      mix cure.release
      mix cure.release --include-erts
      mix cure.release --output _build/cure/rel/custom

  ## Options

  - `--include-erts` -- bundle ERTS with the release (default: false)
  - `--output DIR`   -- override the output directory
  - `--overwrite`    -- wipe the output directory first (default: true)

  The project must define an `app` container (see `docs/APP.md`) and
  ideally a `[release]` table in `Cure.toml`. Minimal projects without
  a `[release]` table work too, with defaults derived from
  `[project]` and `[application]`.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Builds a BEAM release for a Cure project"

  @impl Mix.Task
  def run(args) do
    {opts, _rest, _} =
      OptionParser.parse(args,
        switches: [
          include_erts: :boolean,
          output: :string,
          overwrite: :boolean
        ]
      )

    Mix.Task.run("app.start", [])

    case Cure.Project.load() do
      {:ok, project} ->
        release_opts = [
          include_erts: Keyword.get(opts, :include_erts, false),
          output_dir: Keyword.get(opts, :output),
          overwrite: Keyword.get(opts, :overwrite, true)
        ]

        release_opts = Enum.reject(release_opts, fn {_k, v} -> is_nil(v) end)

        case Cure.Release.build(project, release_opts) do
          {:ok, dir} ->
            Mix.shell().info("Release built: #{dir}")

          {:error, reason} ->
            Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.command_failure("cure release", reason)))

            exit({:shutdown, 1})
        end

      {:error, :no_project_file} ->
        Mix.shell().error(
          render_diagnostic(Cure.Diagnostic.Operational.artifact_error("No Cure.toml found in current directory."))
        )

        exit({:shutdown, 1})

      {:error, reason} ->
        Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.command_failure("cure release", reason)))

        exit({:shutdown, 1})
    end
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
