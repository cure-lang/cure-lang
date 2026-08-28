defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files and adds the output to the code path.

  Looks for `.cure` files in `cure_src/` and compiles them to
  `_build/cure/ebin/` using the Cure compiler with events disabled.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  @impl Mix.Task
  def run(_args) do
    cure_files = Path.wildcard(Path.join(@cure_src, "**/*.cure"))

    if cure_files != [] do
      File.mkdir_p!(@output_dir)
      ebin = Path.expand(@output_dir)

      unless ebin in :code.get_path() do
        :code.add_patha(~c"#{ebin}")
      end

      Application.ensure_all_started(:cure)
      preload_stdlib!()

      Enum.each(cure_files, fn path ->
        case Cure.Compiler.compile_file(path,
               output_dir: @output_dir,
               emit_events: false,
               check_types: true
             ) do
          {:ok, module, _warnings} ->
            Mix.shell().info("Compiled #{path} -> #{module}")

          {:error, reason} ->
            Mix.raise("Failed to compile #{path}: #{inspect(reason)}")
        end
      end)
    end
  end

  defp preload_stdlib! do
    case Cure.Stdlib.Preload.preload(kind: :all) do
      :ok -> :ok
      {:error, reason} -> Mix.raise("Failed to load Cure stdlib: #{inspect(reason)}")
    end
  end
end
