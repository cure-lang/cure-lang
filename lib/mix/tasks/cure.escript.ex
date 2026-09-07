defmodule Mix.Tasks.Cure.Escript do
  @moduledoc """
  Builds the `cure` escript binary.

  Compiles the project and produces a self-contained escript at `./cure`
  (or the path given by `--output`). The resulting file can be placed on
  `$PATH` and invoked directly:

      ./cure compile path/to/file.cure
      ./cure run     path/to/file.cure
      ./cure version

  ## Usage

      mix cure.escript
      mix cure.escript --output /usr/local/bin/cure

  ## Options

  - `--output PATH` -- destination path for the escript (default: `./cure`)

  ## No-op when nothing changed

  `mix escript.build` itself has no staleness tracking -- unlike `mix
  compile`, it repackages the whole escript on every invocation regardless of
  whether anything it would embed actually changed. This task adds that
  check: if the target escript already exists and is newer than every beam
  under `_build/*/lib/*/ebin` (this app and its full dependency tree, in
  every environment escript.build might build from), the staged stdlib beam
  bundle (`priv/ebin`), and `mix.exs`/`mix.lock`, the existing escript is left
  untouched and `escript.build` is not invoked. `cure.bundle_stdlib_beams`
  still runs first regardless -- it has its own cheap, content-addressed
  no-op path (see its own moduledoc) and must run for `priv/ebin` to be
  current before the staleness check above can trust it.
  """

  use Mix.Task

  @shortdoc "Builds the cure escript binary"

  @impl Mix.Task
  def run(args) do
    {opts, _, _} =
      OptionParser.parse(args,
        switches: [output: :string],
        aliases: [o: :output]
      )

    # mix escript.build names the output after the app (:cure -> "cure").
    default_path = Atom.to_string(Mix.Project.config()[:app])
    output = Keyword.get(opts, :output, default_path)

    Mix.Task.run("cure.bundle_stdlib_beams", [])

    case Cure.Compiler.Artifacts.open_verified_set(
           kind: :stdlib,
           candidates: [Cure.Stdlib.Paths.beam_bundle_destination()]
         ) do
      {:ok, _set} ->
        if up_to_date?(output) do
          Mix.shell().info("Escript up to date: #{output} (#{format_bytes(File.stat!(output).size)})")
        else
          Mix.Task.run("escript.build", [])
          report_built(output, default_path)
        end

      {:error, reason} ->
        Mix.raise("refusing to build an escript with an invalid stdlib artifact set: #{inspect(reason)}")
    end
  end

  defp report_built(output, default_path) do
    built_path =
      if output != default_path and File.regular?(default_path) do
        File.rename!(default_path, output)
        output
      else
        output
      end

    if File.regular?(built_path) do
      size = File.stat!(built_path).size
      Mix.shell().info("Escript built: #{built_path} (#{format_bytes(size)})")
    end
  end

  # `target` is stale (and escript.build must run) whenever it does not yet
  # exist, or any of `source_paths/0` is newer than it. `Mix.Utils.stale?/2`
  # is the same mtime-comparison primitive Mix's own compiler tasks use to
  # decide whether they have anything to do; nothing here re-derives
  # freshness from raw file times by hand.
  defp up_to_date?(target) do
    File.regular?(target) and not Mix.Utils.stale?(source_paths(), [target])
  end

  # A conservative superset of what `mix escript.build` actually reads:
  # every beam under every environment's build tree (escript.build forces a
  # `MIX_ENV=prod`-equivalent rebuild by default regardless of the env this
  # task itself runs under, so `_build/dev` alone is not enough to trust),
  # plus the staged stdlib beam bundle it does not otherwise know about, plus
  # the two files (`mix.exs`, `mix.lock`) whose edits can add, remove, or
  # reconfigure what gets embedded without touching a single beam's mtime.
  # Overcounting sources only costs an occasional unnecessary rebuild;
  # undercounting them would silently reuse a stale escript, so this errs wide.
  defp source_paths do
    build_beams = Path.wildcard(Path.join(["_build", "*", "lib", "*", "ebin", "*.beam"]))
    stdlib_beams = Path.wildcard(Path.join(Cure.Stdlib.Paths.beam_bundle_destination(), "**/*.beam"))
    project_files = Enum.filter(["mix.exs", "mix.lock"], &File.regular?/1)

    project_files ++ build_beams ++ stdlib_beams
  end

  defp format_bytes(bytes) when bytes >= 1_048_576,
    do: "#{Float.round(bytes / 1_048_576, 1)} MB"

  defp format_bytes(bytes) when bytes >= 1_024,
    do: "#{Float.round(bytes / 1_024, 1)} KB"

  defp format_bytes(bytes),
    do: "#{bytes} B"
end
