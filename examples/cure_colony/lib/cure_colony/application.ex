defmodule CureColony.Application do
  @moduledoc """
  OTP application for the Cure colony example.

  Starts a plain `Supervisor` that in turn starts the compiled Cure
  supervisor `:"Cure.Main.Colony"` as a child. The Cure supervisor
  module itself implements the `Supervisor` behaviour, so a standard
  child-spec tuple is enough.

  `mix.exs` declares `compile: ["compile_cure", "compile"]` and
  `test: ["compile_cure", "test"]`, so the `:"Cure.Main.Colony"`,
  `:"Cure.Main.Worker"`, and `:"Cure.Main.Echo"` modules are already
  loaded into the VM by the time this callback runs.
  """

  use Application

  @cure_sup :"Cure.Main.Colony"

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

    opts = [strategy: :one_for_one, name: CureColony.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
