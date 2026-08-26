defmodule Cure.Application do
  @moduledoc false

  use Application

  @impl Application
  def start(_type, _args) do
    children = [
      {Registry, keys: :duplicate, name: Cure.Pipeline.Events.Registry}
    ]

    opts = [strategy: :one_for_one, name: Cure.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
