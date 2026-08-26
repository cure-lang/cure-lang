defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files for the Cure motif example.

  The Cure actor, supervisor, FSM, and app forms expand to ordinary lifted
  modules. This task emits those generated units under `_build/cure/ebin/`
  before the Elixir compile step (and before each test run) so every compiled
  module is live in the VM when the application supervisor starts.

  Actor and FSM lifted modules have no forward references between files, so
  compile order matters only for readability. We compile the pure module
  first (it is the biggest and all other files refer to its types),
  then the FSM, the actor containers, the supervisor, and finally the app
  container.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files for cure_motif"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  @preferred_order [
    "motif.cure",
    "envelope.cure",
    "voice.cure",
    "sequencer.cure",
    "clock.cure",
    "orchestra.cure",
    "motif_app.cure"
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

          {:error, {:computed_macro_error, _metadata, detail}} ->
            Mix.raise("Failed to expand #{path}: #{inspect(detail)}")

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
