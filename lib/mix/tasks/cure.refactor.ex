defmodule Mix.Tasks.Cure.Refactor do
  @shortdoc "Analyze and structurally refactor Cure modules"

  @moduledoc """
  Structural analysis and machine-applicable refactoring for Cure source modules.

  The analysis phase reports declarations and imports without modifying source.
  Use `--recursive` to include nested declarations, `--stats` for deterministic
  size/kind counts, `--dependencies` for declaration-level call references, and
  `--plan` to derive dependency components and isolated split candidates, and
  `--verbose` to print import details. `--checked` runs the canonical compiler
  pipeline before producing the report. `--split` applies a verified top-level
  declaration extraction modelled after Rhizoid. Split specifications name the
  destination module because Cure definition identities include the module:
  `Target.cure:Target.Module:Declaration|OtherDeclaration`. Use `--dry-run` to
  inspect the generated buffers without writing them.

      mix cure.refactor path/to/module.cure
      mix cure.refactor --recursive --stats --dependencies path/to/module.cure
      mix cure.refactor --plan path/to/module.cure
      mix cure.refactor --json --checked path/to/module.cure
      mix cure.refactor path/to/module.cure --output-directory ./src \\
        --split "Helpers.cure:My.Helpers:helper|parse"
  """

  use Mix.Task

  alias Cure.Refactor.{Analysis, Rewrite}

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [
          json: :boolean,
          checked: :boolean,
          recursive: :boolean,
          stats: :boolean,
          dependencies: :boolean,
          plan: :boolean,
          verbose: :boolean,
          split: :keep,
          output_directory: :string,
          dry_run: :boolean,
          overwrite: :boolean,
          remove_from_source: :boolean,
          max_depth: :integer,
          prelude_macros: :boolean
        ],
        aliases: [j: :json, c: :checked, r: :recursive, d: :dependencies, p: :plan, v: :verbose]
      )

    cond do
      invalid != [] ->
        usage_error("Invalid options for mix cure.refactor: #{inspect(invalid)}")

      length(paths) != 1 ->
        usage_error(
          "Usage: mix cure.refactor [--json] [--checked] [--recursive] [--stats] " <>
            "[--dependencies] [--plan] [--verbose] [--split SPEC] [--dry-run] " <>
            "[--output-directory DIR] [--max-depth N] <path.cure>"
        )

      true ->
        start_app(opts)
        path = Path.expand(hd(paths))

        if Keyword.has_key?(opts, :split),
          do: split(path, opts),
          else: analyze(path, opts)
    end
  end

  defp split(path, opts) do
    split_opts = [
      output_directory: Keyword.get(opts, :output_directory, Path.dirname(path)),
      overwrite: Keyword.get(opts, :overwrite, false),
      remove_from_source: Keyword.get(opts, :remove_from_source, true),
      write: not Keyword.get(opts, :dry_run, false)
    ]

    case Enum.reduce_while(Keyword.get_values(opts, :split), [], fn spec, results ->
           case Rewrite.split(path, spec, split_opts) do
             {:ok, result} ->
               {:cont, [result | results]}

             {:error, reason} ->
               Mix.shell().error(Cure.Diagnostic.Host.render(reason, path))
               {:halt, {:error, reason}}
           end
         end) do
      {:error, _reason} ->
        Mix.raise("refactor split failed")

      results ->
        results = Enum.reverse(results)

        if Keyword.get(opts, :json, false) do
          IO.puts(Jason.encode!(Enum.map(results, &Rewrite.to_map/1)))
        else
          Enum.each(results, fn result ->
            status = if result.applied?, do: "written", else: "dry-run"

            Mix.shell().info(
              "split #{result.source_path} -> #{result.target_path} (#{status}): #{Enum.join(result.selected, ", ")}"
            )
          end)
        end

        :ok
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
      Keyword.take(opts, [:checked, :recursive, :stats, :dependencies, :plan, :verbose, :max_depth, :prelude_macros])

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
