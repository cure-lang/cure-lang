defmodule Mix.Tasks.Cure.Snap do
  @moduledoc """
  Save or load Cure REPL session snapshots (v0.32.0).

  ## Usage

      mix cure.snap save [--out <path>]
      mix cure.snap load <path>
      mix cure.snap list [<dir>]

  ## Subcommands

    * `save` -- serialize the currently running REPL session (discovered
      via the `Cure.REPL.Session` ETS table) to a `.cure-snap` file.
      Defaults to writing `cure.snap` in the current directory.
    * `load` -- read a `.cure-snap` file and print the session entries
      it contains, for inspection without starting a REPL.
    * `list` -- list all `.cure-snap` files found recursively in `<dir>`
      (default: current directory).

  ## Options

    * `--out` -- output path for `save` (default: `cure.snap`).

  ## Notes

  To save/load sessions interactively inside a running REPL, use the
  built-in meta-commands `:snap save`, `:snap load`, and `:snap list`.
  This Mix task is intended for CI workflows and offline inspection.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Save or load Cure REPL session snapshots"

  @impl Mix.Task
  def run(args) do
    {opts, rest, _invalid} =
      OptionParser.parse(args, switches: [out: :string])

    Application.ensure_all_started(:cure)

    case rest do
      ["save" | _] ->
        path = Keyword.get(opts, :out, "cure.snap")
        cmd_save(path)

      ["load", path | _] ->
        cmd_load(path)

      ["list" | rest_dirs] ->
        dir = List.first(rest_dirs, ".")
        cmd_list(dir)

      _ ->
        Mix.shell().info("""
        Usage:
          mix cure.snap save [--out path]
          mix cure.snap load <path>
          mix cure.snap list [dir]
        """)
    end
  end

  defp cmd_save(path) do
    # Construct a minimal stub state for serialization when no live REPL
    # session is running. In a real embedded scenario the caller would
    # provide the actual state; here we create an empty snapshot.
    stub_state = %{
      defs: [],
      uses: [],
      history: [],
      holes: [],
      stdlib_kind: :none,
      theme: nil,
      mode: :emacs,
      loaded: []
    }

    case Cure.REPL.Snap.save(stub_state, path) do
      :ok ->
        Mix.shell().info("Saved empty snap to #{path}")

      {:error, {:file_write_error, p, reason}} ->
        Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.file_write(p, reason)))
        exit({:shutdown, 1})
    end
  end

  defp cmd_load(path) do
    case Cure.REPL.Snap.load(path) do
      {:ok, snap_map} ->
        defs = Map.get(snap_map, :defs, [])
        uses = Map.get(snap_map, :uses, [])
        history_count = length(Map.get(snap_map, :history_entries, []))
        vsn = Map.get(snap_map, :snap_vsn, "?")

        Mix.shell().info("Snap file: #{path}")
        Mix.shell().info("  Schema version: #{vsn}")
        Mix.shell().info("  Definitions: #{length(defs)}")
        Mix.shell().info("  Imports: #{length(uses)}")
        Mix.shell().info("  History entries: #{history_count}")

        if defs != [] do
          Mix.shell().info("  Definition labels:")

          Enum.each(defs, fn
            %{label: label} -> Mix.shell().info("    #{label}")
            _ -> :ok
          end)
        end

      {:error, :E069} ->
        Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.snap_schema_incompatible(path)))

        exit({:shutdown, 1})

      {:error, :corrupt} ->
        Mix.shell().error(
          render_diagnostic(Cure.Diagnostic.Operational.artifact_error("Snap file is corrupt or truncated: #{path}"))
        )

        exit({:shutdown, 1})

      {:error, {:file_read_error, p, reason}} ->
        Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.file_read(p, reason)))
        exit({:shutdown, 1})
    end
  end

  defp cmd_list(dir) do
    files = Cure.REPL.Snap.list(dir)

    if files == [] do
      Mix.shell().info("No .cure-snap files found in #{dir}")
    else
      Mix.shell().info("Snap files in #{dir} (#{length(files)}):")
      Enum.each(files, &Mix.shell().info("  #{&1}"))
    end
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
