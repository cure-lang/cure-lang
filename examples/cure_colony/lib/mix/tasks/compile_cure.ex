defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files for the Cure colony example.

  The standard-library `actor` and `sup` macros expand to lifted modules
  and are emitted through the common Cure BEAM writer. The task runs before
  the Elixir compile step and before each test run so those generated modules
  are available when the application supervisor starts.

  Ordering matters at runtime, not at compile time: the `Cure.Colony`
  child specs reference `Cure.Worker` and `Cure.Echo` as
  atoms, so compile order is irrelevant, but actor modules must be
  loaded before the supervisor is *started*. Since every actor file is
  compiled in this same pass, the ordering inside the pass is
  academic; we still compile actors first for clarity.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files for cure_colony"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  # Actors first, supervisor last. Any file not listed is compiled
  # after the named ones in alphabetical order.
  @preferred_order ["worker.cure", "echo.cure", "colony.cure"]

  @impl Mix.Task
  def run(_args) do
    cure_files =
      Path.wildcard(Path.join(@cure_src, "**/*.cure"))
      |> Enum.sort_by(&order_key/1)

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

  defp order_key(path) do
    basename = Path.basename(path)

    case Enum.find_index(@preferred_order, &(&1 == basename)) do
      nil -> {1, basename}
      idx -> {0, idx}
    end
  end
end
