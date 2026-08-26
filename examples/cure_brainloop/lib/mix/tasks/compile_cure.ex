defmodule Mix.Tasks.CompileCure do
  use Mix.Task

  @shortdoc "Compiles .cure source files"
  @output_dir "_build/cure/ebin"

  @impl Mix.Task
  def run(_args) do
    files = Path.wildcard("cure_src/**/*.cure") |> Enum.sort()

    if files != [] do
      File.mkdir_p!(@output_dir)
      ebin = Path.expand(@output_dir)
      if ebin not in :code.get_path(), do: :code.add_patha(~c"#{ebin}")
      Application.ensure_all_started(:cure)
      preload_stdlib!()

      Enum.each(files, fn path ->
        case Cure.Compiler.compile_file(path,
               output_dir: @output_dir,
               emit_events: false,
               check_types: true
             ) do
          {:ok, module, _warnings} -> Mix.shell().info("Compiled #{path} -> #{module}")
          {:error, reason} -> Mix.raise("Failed to compile #{path}: #{inspect(reason)}")
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
