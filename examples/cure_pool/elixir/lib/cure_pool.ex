defmodule CurePool do
  @moduledoc """
  Ergonomic Elixir API over the Safe Linear Resource Pool.

  `cure_pool` has two halves:

    * a **pure-Cure core** (`../cure`) where the pool's counts are a dependent
      type and the lease is a linear capability -- the compiler proves no
      over-checkout, no double-return, and no leak; and
    * this **Elixir-hosted runtime**, which runs the pool as a supervised OTP
      process and proves the crash-reclaim guarantee: a client or worker dying
      mid-lease does not strand a slot.

  The Cure FSM that models each worker's lifecycle is compiled from
  `cure_src/worker_fsm.cure` to the raw BEAM module `:"Cure.Main.WorkerFsm"`
  and is verified at Cure compile time.

  ## Quick start

      {:ok, pool} = CurePool.start_pool(capacity: 3)

      {:ok, lease} = CurePool.checkout(pool)
      {:ok, worker} = CurePool.run(lease, fn w -> w end)
      :ok          = CurePool.checkin(pool, lease)

      CurePool.stats(pool)
      # => %{capacity: 3, available: 3, in_use: 0}
  """

  @doc "Start a standalone pool (not under the application supervisor)."
  @spec start_pool(keyword()) :: GenServer.on_start()
  def start_pool(opts), do: CurePool.Pool.start_link(opts)

  @doc "Check out a resource. `holder` defaults to the calling process."
  @spec checkout(GenServer.server(), pid()) ::
          {:ok, CurePool.Pool.lease()} | {:error, :empty}
  def checkout(pool, holder \\ self()), do: CurePool.Pool.checkout(pool, holder)

  @doc "Run `fun` on the leased worker."
  @spec run(CurePool.Pool.lease(), (pid() -> result)) :: {:ok, result}
        when result: term()
  def run(lease, fun), do: CurePool.Pool.run(lease, fun)

  @doc "Return a resource to the pool."
  @spec checkin(GenServer.server(), CurePool.Pool.lease()) :: :ok | {:error, :stale}
  def checkin(pool, lease), do: CurePool.Pool.checkin(pool, lease)

  @doc "A snapshot of the pool's counts."
  @spec stats(GenServer.server()) :: map()
  def stats(pool), do: CurePool.Pool.stats(pool)

  @doc "The raw BEAM atom of the Cure-compiled worker FSM."
  @spec worker_fsm_module() :: atom()
  def worker_fsm_module, do: :"Cure.Main.WorkerFsm"
end
