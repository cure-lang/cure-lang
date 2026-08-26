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
        Mix.Task.run("escript.build", [])

      {:error, reason} ->
        Mix.raise("refusing to build an escript with an invalid stdlib artifact set: #{inspect(reason)}")
    end

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

  defp format_bytes(bytes) when bytes >= 1_048_576,
    do: "#{Float.round(bytes / 1_048_576, 1)} MB"

  defp format_bytes(bytes) when bytes >= 1_024,
    do: "#{Float.round(bytes / 1_024, 1)} KB"

  defp format_bytes(bytes),
    do: "#{bytes} B"
end
