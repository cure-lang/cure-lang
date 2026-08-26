defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files for the Cure forge example.

  The standard-library `actor`, `sup`, and `app` macros expand to lifted
  modules and are emitted through the common Cure BEAM writer. The task
  runs before the Elixir compile step and before each test run so the
  generated modules are available when the application supervisor starts.

  Ordering matters at runtime, not at compile time: the
  `Cure.Forge.Root` child specs reference `Cure.Metrics`,
  `Cure.Logger`, `Cure.Queue`, and `Cure.Pool` as
  atoms, so compile order is irrelevant. Still, we compile actors
  first for clarity, then the supervisor, then the application
  container.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files for cure_forge"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  # Actors first, supervisor in the middle, app container last. Any
  # file not listed here is compiled after the named ones in
  # alphabetical order.
  @preferred_order [
    "metrics.cure",
    "logger.cure",
    "queue.cure",
    "pool.cure",
    "forge_root.cure",
    "forge_app.cure"
  ]

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
