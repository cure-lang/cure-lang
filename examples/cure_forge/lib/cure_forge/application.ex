defmodule CureForge.Application do
  @moduledoc """
  OTP application callback for the Cure forge example.

  Conceptually, the OTP application for this project is the
  `Cure.Main.CureForge` module emitted by `cure_src/forge_app.cure`,
  which is loaded into the VM by the `compile_cure` Mix task (see
  `lib/mix/tasks/compile_cure.ex`). That module is the artefact that
  `cure release` packages into `_build/cure/rel/cure_forge/`.

  Under plain Mix (`mix test`, `iex -S mix`), however, we also need
  an Elixir `Application` callback so that the project can be started
  with `Application.ensure_all_started(:cure_forge)`. This module
  bridges the two worlds:

    * `start/2` starts a plain `Supervisor` that supervises
      `:"Cure.Forge.Root"` (the BEAM module compiled from
      `cure_src/forge_root.cure`). That supervisor in turn starts the
      four actors declared in the root `sup` container.
    * `start_phase/3` invokes the matching `start_phase/3` callback
      on the Cure-compiled `Cure.Main.CureForge` module.
    * `stop/1` is a no-op.

  In production, none of this bridge is necessary: `cure release`
  emits a boot script that lists `:"Cure.Main.CureForge"` as the
  application's `mod`, and OTP calls its `start/2` directly, bypassing
  this Elixir facade entirely.
  """

  use Application

  require Logger

  @cure_sup :"Cure.Forge.Root"
  @cure_app :"Cure.Main.CureForge"

  @impl Application
  def start(_type, _args) do
    children = [
      %{
        id: @cure_sup,
        start: {@cure_sup, :start_link, []},
        type: :supervisor,
        restart: :permanent
      }
    ]

    opts = [strategy: :one_for_one, name: CureForge.Supervisor]

    case Supervisor.start_link(children, opts) do
      {:ok, pid} ->
        Logger.info("CureForge booted: #{Application.get_env(:cure_forge, :greeting)}")
        {:ok, pid}

      other ->
        other
    end
  end

  @impl Application
  def start_phase(phase, start_type, phase_args) do
    if Code.ensure_loaded?(@cure_app) and function_exported?(@cure_app, :start_phase, 3) do
      apply(@cure_app, :start_phase, [phase, start_type, phase_args])
    else
      :ok
    end
  end

  @impl Application
  def stop(_state), do: :ok
end
