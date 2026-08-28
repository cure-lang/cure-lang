defmodule CureExchange.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      CureExchange.Ledger,
      {DynamicSupervisor, name: CureExchange.TradeSupervisor, strategy: :one_for_one}
    ]

    opts = [strategy: :one_for_all, name: CureExchange.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
