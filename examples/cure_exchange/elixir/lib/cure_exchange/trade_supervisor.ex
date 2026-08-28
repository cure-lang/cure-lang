defmodule CureExchange.TradeSupervisor do
  @moduledoc """
  A `DynamicSupervisor` holding one `CureExchange.TradeWorker` per open
  trade. Each worker is `:transient`: it exits normally once its escrow
  reaches a terminal state (or the caller stops it), and only an abnormal
  exit (the worker crashing, or its owned FSM process crashing under it)
  triggers a restart.
  """

  @doc "Start a new trade worker under this supervisor."
  @spec start_trade(keyword()) :: DynamicSupervisor.on_start_child()
  def start_trade(opts) do
    DynamicSupervisor.start_child(__MODULE__, {CureExchange.TradeWorker, opts})
  end
end
