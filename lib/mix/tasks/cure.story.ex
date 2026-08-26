defmodule Mix.Tasks.Cure.Story do
  @moduledoc """
  Generate a narrative `STORY.md` for the current Cure project (v0.32.0).

  Reads every `.cure` file under `lib/`, builds a structural outline
  (apps -> supervisors -> actors -> FSMs -> types), and emits a Markdown
  document introducing the system top-down.

  ## Usage

      mix cure.story
      mix cure.story --out docs/ARCHITECTURE.md
      mix cure.story --stdout
      mix cure.story --diagrams
      mix cure.story --format html --out docs/story.html

  ## Options

    * `--out` -- output file path. Default: `STORY.md` at the project root.
    * `--stdout` -- print the document to stdout instead of writing a file.
    * `--diagrams` -- embed Mermaid `stateDiagram-v2` blocks for each FSM.
    * `--format md|html` -- output format. Default: `md`.
    * `--project-name` -- override the project name in the document title.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Generate a narrative STORY.md for the current Cure project"

  @impl Mix.Task
  def run(args) do
    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [
          out: :string,
          stdout: :boolean,
          diagrams: :boolean,
          format: :string,
          project_name: :string
        ]
      )

    if rest != [] or invalid != [] do
      usage_error("Invalid arguments for mix cure.story: #{inspect(rest ++ invalid)}")
    end

    Application.ensure_all_started(:cure)

    root = File.cwd!()

    generate_opts =
      []
      |> maybe_put(:out, Keyword.get(opts, :out))
      |> maybe_put_pred(:stdout, Keyword.get(opts, :stdout, false), & &1)
      |> maybe_put_pred(:diagrams, Keyword.get(opts, :diagrams, false), & &1)
      |> maybe_put(:format, parse_format(Keyword.get(opts, :format, "md")))
      |> maybe_put(:project_name, Keyword.get(opts, :project_name))

    case Cure.Story.generate(root, generate_opts) do
      {:ok, result} ->
        if Keyword.get(generate_opts, :stdout, false) do
          IO.puts(result)
        else
          Mix.shell().info("cure.story: wrote #{result}")
        end

      {:error, {:file_write_error, path, reason}} ->
        diagnostic = Cure.Diagnostic.Operational.file_write(path, reason)
        Mix.shell().error(render_diagnostic(diagnostic))
        exit({:shutdown, 1})
    end
  end

  defp parse_format("html"), do: :html
  defp parse_format("md"), do: :md

  defp parse_format(other) do
    usage_error("Unknown story format '#{other}'. Supported formats: md, html")
  end

  defp usage_error(message) do
    Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.usage(message)))
    exit({:shutdown, 1})
  end

  defp maybe_put(opts, _key, nil), do: opts
  defp maybe_put(opts, key, value), do: Keyword.put(opts, key, value)

  defp maybe_put_pred(opts, key, value, pred) do
    if pred.(value), do: Keyword.put(opts, key, value), else: opts
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
