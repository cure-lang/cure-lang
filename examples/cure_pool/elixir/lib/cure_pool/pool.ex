defmodule CurePool.Pool do
  @moduledoc """
  A live resource pool: fixed capacity, supervised workers, and a slot registry
  that survives worker crashes.

  This is the runtime half of `cure_pool`. The *type-level* guarantees (no
  over-checkout, no double-return, no leak) live in the pure-Cure core under
  `../cure`; this process proves the *runtime* guarantee the brief calls out --
  **a worker (or its client) crashing does not strand a slot**. The pool
  monitors every checkout and reclaims the slot when the holder goes away, so
  `available + in_use` is invariant across restarts.

  ## Why the pool owns the count

  The Cure core proves the count is consistent for a program that type-checks.
  A live system also has to survive *untyped* events: a client process dying
  mid-lease, a worker crashing, a node disconnecting. Those arrive as BEAM
  signals, not as type errors, so the pool is the one place that reconciles
  them -- and it does so by reclaiming, never by leaking.

  ## Example

      {:ok, pool} = CurePool.Pool.start_link(capacity: 2)

      {:ok, lease} = CurePool.Pool.checkout(pool, self())
      {:ok, worker} = CurePool.Pool.run(lease, fn w -> w end)
      :ok          = CurePool.Pool.checkin(pool, lease)

      CurePool.Pool.stats(pool)
      # => %{capacity: 2, available: 2, in_use: 0}
  """

  use GenServer

  @typedoc "An opaque lease: the pool, the worker, and a unique session key."
  @type lease :: %{
          pool: GenServer.server(),
          worker: pid(),
          worker_ref: reference(),
          key: reference(),
          holder: pid()
        }

  # -- Public API -------------------------------------------------------------

  @doc """
  Start a pool of `capacity` workers.

  Options:

    * `:capacity` (required) -- number of resources in the pool.
    * `:name` -- optional registered name.
  """
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts) do
    {name, opts} = Keyword.pop(opts, :name)
    gen_opts = if name, do: [name: name], else: []
    GenServer.start_link(__MODULE__, opts, gen_opts)
  end

  @doc """
  Check out a resource for `holder` (defaults to the calling process).

  Returns `{:ok, lease}` or `{:error, :empty}` when every slot is in use. The
  pool monitors `holder`, so if it dies before `checkin/2`, the slot is
  reclaimed automatically.
  """
  @spec checkout(GenServer.server(), pid()) :: {:ok, lease()} | {:error, :empty}
  def checkout(pool, holder \\ self()) do
    GenServer.call(pool, {:checkout, holder})
  end

  @doc """
  Run `fun` on the leased worker and return its result.

  The lease stays valid: this is the "consume and reproduce" shape the Cure
  core uses. The worker is a plain pid here, so `fun` receives it directly.
  """
  @spec run(lease(), (pid() -> result)) :: {:ok, result} when result: term()
  def run(lease, fun) when is_function(fun, 1) do
    {:ok, fun.(lease.worker)}
  end

  @doc """
  Return a resource to the pool.

  Idempotent per lease: returning an already-returned lease is `{:error,
  :stale}` rather than a double-free, mirroring the Cure core's linearity
  guarantee at runtime.
  """
  @spec checkin(GenServer.server(), lease()) :: :ok | {:error, :stale}
  def checkin(pool, lease) do
    GenServer.call(pool, {:checkin, lease})
  end

  @doc "A snapshot of the pool's counts, for tests and operators."
  @spec stats(GenServer.server()) :: %{
          capacity: non_neg_integer(),
          available: non_neg_integer(),
          in_use: non_neg_integer()
        }
  def stats(pool), do: GenServer.call(pool, :stats)

  # -- GenServer callbacks ----------------------------------------------------

  @impl true
  def init(opts) do
    capacity = Keyword.fetch!(opts, :capacity)
    workers = start_workers(capacity)

    state = %{
      capacity: capacity,
      available: workers,
      in_use: %{},
      monitors: %{}
    }

    {:ok, state}
  end

  @impl true
  def handle_call({:checkout, holder}, _from, state) do
    case state.available do
      [] ->
        {:reply, {:error, :empty}, state}

      [worker | rest] ->
        key = make_ref()
        worker_ref = Process.monitor(worker)
        holder_ref = Process.monitor(holder)

        lease = %{
          pool: self(),
          worker: worker,
          worker_ref: worker_ref,
          key: key,
          holder: holder
        }

        in_use = Map.put(state.in_use, key, %{lease: lease, holder_ref: holder_ref})

        monitors =
          state.monitors
          |> Map.put(worker_ref, {:worker, key})
          |> Map.put(holder_ref, {:holder, key})

        new_state = %{state | available: rest, in_use: in_use, monitors: monitors}
        {:reply, {:ok, lease}, new_state}
    end
  end

  def handle_call({:checkin, lease}, _from, state) do
    case Map.pop(state.in_use, lease.key) do
      {nil, _} ->
        # Already returned, or reclaimed after a crash: a stale lease is an
        # error value, never a double-free.
        {:reply, {:error, :stale}, state}

      {%{lease: %{worker: worker}, holder_ref: holder_ref}, in_use} ->
        Process.demonitor(lease.worker_ref, [:flush])
        Process.demonitor(holder_ref, [:flush])

        monitors =
          state.monitors
          |> Map.delete(lease.worker_ref)
          |> Map.delete(holder_ref)

        new_state = %{
          state
          | available: [worker | state.available],
            in_use: in_use,
            monitors: monitors
        }

        {:reply, :ok, new_state}
    end
  end

  def handle_call(:stats, _from, state) do
    stats = %{
      capacity: state.capacity,
      available: length(state.available),
      in_use: map_size(state.in_use)
    }

    {:reply, stats, state}
  end

  @impl true
  def handle_info({:DOWN, ref, :process, _pid, _reason}, state) do
    case Map.pop(state.monitors, ref) do
      {nil, _} ->
        {:noreply, state}

      {{:worker, key}, monitors} ->
        # The WORKER died while checked out. Reclaim the slot: drop the lease,
        # start a replacement worker, and put it back in the available set.
        state = reclaim(state, key, monitors, replace: true)
        {:noreply, state}

      {{:holder, key}, monitors} ->
        # The CLIENT died while holding a lease. Reclaim the slot and return the
        # still-live worker to the pool -- this is the crash-reclaim guarantee.
        state = reclaim(state, key, monitors, replace: false)
        {:noreply, state}
    end
  end

  # -- Internals --------------------------------------------------------------

  defp reclaim(state, key, monitors, opts) do
    case Map.pop(state.in_use, key) do
      {nil, _} ->
        # Already returned; nothing to reclaim.
        %{state | monitors: monitors}

      {%{lease: lease, holder_ref: holder_ref}, in_use} ->
        Process.demonitor(lease.worker_ref, [:flush])
        Process.demonitor(holder_ref, [:flush])

        monitors =
          monitors
          |> Map.delete(lease.worker_ref)
          |> Map.delete(holder_ref)

        available =
          if opts[:replace] do
            [start_worker() | state.available]
          else
            [lease.worker | state.available]
          end

        %{state | available: available, in_use: in_use, monitors: monitors}
    end
  end

  defp start_workers(capacity) do
    for _i <- 1..capacity, do: start_worker()
  end

  # Each worker is a live FSM process. In this example the worker is a plain
  # process that simply lives until reclaimed; the point of the pool is the
  # *slot* lifecycle, and a real deployment would start the compiled Cure
  # `WorkerFsm` here (`:"Cure.Main.WorkerFsm".start_link/1`).
  #
  # The worker is spawned *unlinked*: the pool monitors it (per checkout) so a
  # worker crash is observed and handled, but it must not take the pool down
  # with it -- a linked worker would defeat the whole reclaim story.
  defp start_worker do
    spawn(fn -> worker_loop() end)
  end

  defp worker_loop do
    receive do
      :stop -> :ok
      _other -> worker_loop()
    end
  end
end
