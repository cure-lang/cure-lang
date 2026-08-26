defmodule CureMotif.Application do
  @moduledoc """
  OTP application callback for the Cure motif example.

  Starts a plain `Supervisor` that supervises three children:

    * `:"Cure.Motif.Orchestra"` -- the Cure-compiled supervisor declared
      in `cure_src/orchestra.cure`, which in turn starts the `Clock`,
      `Sequencer`, and `Voice` actors declared in `cure_src/*.cure`.
    * `CureMotif.MidiOut` -- a tiny Elixir Agent that collects NoteOn /
      NoteOff events emitted by the sequencer (see `lib/cure_motif/midi_out.ex`).

  The compiled Cure modules are loaded from `_build/cure/ebin/` by the
  `compile_cure` Mix task, which `mix.exs` wires into both the `compile`
  and `test` aliases.
  """

  use Application

  require Logger

  @cure_sup :"Cure.Motif.Orchestra"
  @cure_app :"Cure.Main.CureMotif"
  @compile {:no_warn_undefined, @cure_sup}
  @compile {:no_warn_undefined, @cure_app}

  @impl Application
  def start(_type, _args) do
    ensure_code_paths!()

    children = [
      CureMotif.MidiOut,
      %{
        id: @cure_sup,
        start: {@cure_sup, :start_link, []},
        type: :supervisor,
        restart: :permanent
      }
    ]

    opts = [strategy: :one_for_one, name: CureMotif.Supervisor]

    case Supervisor.start_link(children, opts) do
      {:ok, pid} ->
        Logger.info("CureMotif booted at #{Application.get_env(:cure_motif, :bpm)} bpm")
        {:ok, pid}

      other ->
        other
    end
  end

  @impl Application
  def start_phase(phase, start_type, phase_args) do
    if Code.ensure_loaded?(@cure_app) and function_exported?(@cure_app, :start_phase, 3) do
      @cure_app.start_phase(phase, start_type, phase_args)
    else
      :ok
    end
  end

  @impl Application
  def stop(_state), do: :ok

  # The Cure stdlib is compiled into `<cure_root>/_build/cure/ebin/`
  # rather than into the consumer's own `_build/`. The compile_cure
  # Mix task handles this at compile time; we replicate the step here
  # so `iex -S mix` and `mix test` pick up `:"Cure.Std.*"` modules
  # without requiring a fresh `mix compile_cure`.
  defp ensure_code_paths! do
    for rel <- ["_build/cure/ebin", "../../_build/cure/ebin"] do
      path = Path.expand(rel)

      if File.dir?(path) and path not in :code.get_path() do
        :code.add_patha(~c"#{path}")
      end
    end

    :ok
  end
end
