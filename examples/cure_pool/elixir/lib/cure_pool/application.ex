defmodule CurePool.Application do
  @moduledoc """
  The `cure_pool` OTP application.

  Starts a supervised, named pool with a small default capacity so the example
  is usable from `iex -S mix` without any setup:

      CurePool.Pool.stats(CurePool)
      # => %{capacity: 2, available: 2, in_use: 0}
  """

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {CurePool.Pool, name: CurePool, capacity: 2}
    ]

    opts = [strategy: :one_for_one, name: CurePool.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
