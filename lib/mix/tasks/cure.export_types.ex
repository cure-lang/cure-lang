defmodule Mix.Tasks.Cure.ExportTypes do
  @moduledoc """
  Export Cure type declarations to a target schema language (v0.32.0).

  ## Usage

      mix cure.export_types [--target protobuf] [--out <dir>] [files...]

  Without explicit `files`, processes every `lib/**/*.cure` file in the
  current project.

  ## Options

    * `--target` -- target language schema. Currently only `protobuf`
      (proto3) is supported. Default: `protobuf`.
    * `--out` -- output directory. Default:
      `_build/cure/export/<target>`.
    * `--verbose` / `-v` -- print one line per file processed.
    * `--dry-run` -- print generated content to stdout instead of
      writing files.

  ## Examples

      # Export all project types to proto3
      mix cure.export_types --target protobuf

      # Export specific files only
      mix cure.export_types --target protobuf lib/types.cure lib/events.cure

      # Preview without writing
      mix cure.export_types --dry-run

  Unmappable types (refinements, dependent types) emit an E068 warning
  and are replaced by a `bytes` field with an explanatory comment in the
  generated output.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Export Cure type declarations to proto3 (or other schema languages)"

  @impl Mix.Task
  def run(args) do
    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [
          target: :string,
          out: :string,
          verbose: :boolean,
          dry_run: :boolean
        ],
        aliases: [v: :verbose]
      )

    if invalid != [] do
      usage_error("Invalid options for mix cure.export_types: #{inspect(invalid)}")
    end

    target = parse_target(Keyword.get(opts, :target, "protobuf"))
    verbose? = Keyword.get(opts, :verbose, false)
    dry_run? = Keyword.get(opts, :dry_run, false)

    root = File.cwd!()

    export_opts =
      [target: target, verbose: verbose?]
      |> maybe_put(:files, rest, &(not Enum.empty?(&1)))
      |> maybe_put(:out, Keyword.get(opts, :out), &(not is_nil(&1)))

    Application.ensure_all_started(:cure)

    result = Cure.ExportTypes.export(root, export_opts)

    case result do
      {:ok, []} ->
        Mix.shell().info("cure.export_types: no type definitions found")

      {:ok, outputs} ->
        if dry_run? do
          Enum.each(outputs, fn {path, content} ->
            Mix.shell().info("==> #{path}\n#{content}")
          end)
        else
          out_dir = Keyword.get(export_opts, :out, Path.join(root, "_build/cure/export/#{target}"))
          File.mkdir_p!(out_dir)

          Enum.each(outputs, fn {path, content} ->
            File.mkdir_p!(Path.dirname(path))
            File.write!(path, content)
            if verbose?, do: Mix.shell().info("  wrote #{path}")
          end)

          Mix.shell().info("cure.export_types: wrote #{length(outputs)} file(s) to #{out_dir}")
        end
    end
  end

  defp parse_target("protobuf"), do: :protobuf

  defp parse_target(other) do
    usage_error("Unknown export target '#{other}'. Supported targets: protobuf")
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    rendered =
      Sink.new(format: :plain, color: :auto, width: 80)
      |> Sink.render(diagnostic)

    Mix.shell().error(rendered)
    exit({:shutdown, 1})
  end

  defp maybe_put(opts, key, value, pred) do
    if pred.(value), do: Keyword.put(opts, key, value), else: opts
  end
end
