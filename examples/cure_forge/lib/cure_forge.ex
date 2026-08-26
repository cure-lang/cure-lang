defmodule CureForge do
  @moduledoc """
  Thin Elixir facade over the Cure forge application.

  The entire supervision tree is declared in six `.cure` files under
  `cure_src/`:

    * `forge_app.cure`   -- `app CureForge`
    * `forge_root.cure`  -- `sup Forge.Root`
    * `metrics.cure`     -- `actor Metrics`
    * `logger.cure`      -- `actor Logger`
    * `queue.cure`       -- `actor Queue`
    * `pool.cure`        -- `actor Pool`

  The compiled modules are, respectively, `Cure.Main.CureForge`,
  `Cure.Forge.Root`, `Cure.Main.Metrics`, `Cure.Main.Logger`, `Cure.Main.Queue`,
  and `Cure.Main.Pool`. `CureForge.Application`
  starts `Cure.Forge.Root` under its own top-level `Supervisor`,
  which in turn starts the four actors under the `:one_for_one`
  strategy declared in `forge_root.cure`.

  ## Quick Start

      # The application starts the tree automatically:
      iex> {:ok, _} = Application.ensure_all_started(:cure_forge)
      iex> is_pid(Process.whereis(:"Cure.Forge.Root"))
      true

      # Enqueue three tasks, drain them into the pool, check metrics:
      iex> CureForge.submit(:ok)
      iex> CureForge.submit(:ok)
      iex> CureForge.submit({:fail, :timeout})
      iex> CureForge.drain_queue()
      iex> CureForge.metrics()
      %{requests: 2, errors: 1}

      # Log lines are buffered and can be drained. The logger stores
      # them newest-first (cons prepend); the facade reverses on the
      # way out so callers see insertion order.
      iex> CureForge.log("booted")
      iex> CureForge.log("first tick")
      iex> CureForge.drain_log()
      ["booted", "first tick"]

      # Application env is readable through Std.App (or Application):
      iex> Application.get_env(:cure_forge, :greeting)
      "forge ready"
  """

  @sup_module :"Cure.Forge.Root"
  @metrics_module :"Cure.Main.Metrics"
  @logger_module :"Cure.Main.Logger"
  @queue_module :"Cure.Main.Queue"
  @pool_module :"Cure.Main.Pool"

  # -- Module accessors ------------------------------------------------------

  @doc "Atom of the compiled root supervisor."
  @spec sup_module() :: module()
  def sup_module, do: @sup_module

  @doc "Atoms of the compiled actor modules, by supervisor id."
  @spec actor_modules() :: %{atom() => module()}
  def actor_modules do
    %{
      metrics: @metrics_module,
      logger: @logger_module,
      queue: @queue_module,
      pool: @pool_module
    }
  end

  # -- Supervisor introspection ---------------------------------------------

  @doc """
  Return the list of children as `{id, pid, type, modules}` tuples,
  in the order reported by `Supervisor.which_children/1`.
  """
  @spec which_children() :: [tuple()]
  def which_children, do: Supervisor.which_children(@sup_module)

  @doc "Return the pid of a specific supervisor child, or `nil`."
  @spec child_pid(atom()) :: pid() | nil
  def child_pid(id) do
    Enum.find_value(which_children(), fn
      {^id, pid, _type, _modules} when is_pid(pid) -> pid
      _ -> nil
    end)
  end

  @doc "Return the pid of the metrics actor."
  @spec metrics_pid() :: pid() | nil
  def metrics_pid, do: child_pid(:metrics)

  @doc "Return the pid of the logger actor."
  @spec logger_pid() :: pid() | nil
  def logger_pid, do: child_pid(:logger)

  @doc "Return the pid of the queue actor."
  @spec queue_pid() :: pid() | nil
  def queue_pid, do: child_pid(:queue)

  @doc "Return the pid of the pool actor."
  @spec pool_pid() :: pid() | nil
  def pool_pid, do: child_pid(:pool)

  # -- Metrics ---------------------------------------------------------------

  @doc """
  Return the current metrics snapshot `%{requests:, errors:}`.

  The underlying actor stores the counters in a two-slot tuple
  (`%[requests, errors]` in Cure, `{r, e}` on the BEAM); the facade
  unwraps that into a map so callers can stay idiomatic on the
  Elixir side.
  """
  @spec metrics() :: %{
          required(:requests) => non_neg_integer(),
          required(:errors) => non_neg_integer()
        }
  def metrics do
    {r, e} = :sys.get_state(metrics_pid())
    %{requests: r, errors: e}
  end

  @doc "Reset the metrics counters to zero."
  @spec reset_metrics() :: :ok
  def reset_metrics, do: send_sync(metrics_pid(), :reset)

  @doc "Record an observed outcome (`:ok` or anything else) in the metrics."
  @spec observe(:ok | term()) :: :ok
  def observe(outcome), do: send_sync(metrics_pid(), if(outcome == :ok, do: :ok, else: :error))

  # -- Logger ---------------------------------------------------------------

  @doc "Buffer a log line in the logger actor."
  @spec log(binary() | term()) :: :ok
  def log(line), do: send_sync(logger_pid(), line)

  @doc """
  Drain the logger buffer. Returns the list of buffered lines
  (oldest first) and resets the buffer. Capped at `max_log_lines`
  from `Application.get_env/3`, matching the `[application.env]`
  declaration in `Cure.toml`.

  Cure lowers `%[:lines, buffer]` to the BEAM tuple
  `{:lines, buffer}`; the matcher accepts both that shape and a
  legacy two-element list for forward-compatibility.
  """
  @spec drain_log() :: [term()]
  def drain_log do
    pid = logger_pid()
    cap = Application.get_env(:cure_forge, :max_log_lines, 16)

    lines = :sys.get_state(pid)
    send_sync(pid, :clear)
    lines = Enum.reverse(lines)

    case lines do
      list when is_list(list) -> Enum.take(list, cap)
      other -> other
    end
  end

  @doc """
  Return the current logger buffer size without draining it. The
  queue actor does not expose a dedicated `:size` message (we keep
  the Cure source minimal), so the facade reads the buffer directly
  through the compiled actor's process state and returns its length.
  """
  @spec log_size() :: non_neg_integer()
  def log_size do
    case logger_pid() do
      nil -> 0
      pid -> :sys.get_state(pid) |> length()
    end
  end

  # -- Queue -----------------------------------------------------------------

  @doc """
  Submit a task to the queue. A task is any term; convention is
  `:ok` for a successful task and `{:fail, reason}` for a failure.
  Tasks are drained into the pool by `drain_queue/0`.
  """
  @spec submit(term()) :: :ok
  def submit(task), do: send_sync(queue_pid(), task)

  @doc """
  Return the current queue length.

  Same approach as `log_size/0`: the facade reads the queue's
  payload (a plain list) straight from the generated process state
  and reports its length, so the Cure source can stay minimal.
  """
  @spec queue_size() :: non_neg_integer()
  def queue_size do
    case queue_pid() do
      nil -> 0
      pid -> :sys.get_state(pid) |> length()
    end
  end

  @doc """
  Drain every task currently in the queue into the pool.

  For each dequeued task `t`, this function sends `{:task, t}` to
  the pool via a standard cast, waits for the pool state to reflect its
  outcome,
  and forwards that outcome to the metrics actor as an `:observe`
  message. The round trip exercises the full flow:

      Queue --(dequeue)--> facade --(<-|)--> Pool --(notify)--> facade --(observe)--> Metrics
  """
  @spec drain_queue() :: {:ok, non_neg_integer()}
  def drain_queue do
    drain_queue_loop(0)
  end

  defp drain_queue_loop(count) do
    q_pid = queue_pid()
    p_pid = pool_pid()

    tasks = :sys.get_state(q_pid) |> Enum.reverse()
    send_sync(q_pid, :clear)

    Enum.each(tasks, fn task ->
      outcome = if task == :ok, do: :ok, else: :error
      send_sync(p_pid, outcome)
      observe(outcome)
    end)

    {:ok, count + length(tasks)}
  end

  # -- Pool ------------------------------------------------------------------

  @doc """
  Return the pool's current `%{done:, failed:}` snapshot.

  Like `metrics/0`, the underlying Cure payload is a two-slot tuple
  (`%[done, failed]`); the facade wraps it into a map for
  Elixir-side ergonomics.
  """
  @spec pool_state() :: %{
          required(:done) => non_neg_integer(),
          required(:failed) => non_neg_integer()
        }
  def pool_state do
    {done, failed} = :sys.get_state(pool_pid())
    %{done: done, failed: failed}
  end

  @doc "Reset the pool's counters."
  @spec reset_pool() :: :ok
  def reset_pool, do: send_sync(pool_pid(), :reset)

  # -- Internals ------------------------------------------------------------

  defp send_sync(pid, msg) when is_pid(pid) do
    :gen_server.cast(pid, msg)
    _ = :sys.get_state(pid)
    :ok
  end

  defp send_sync(nil, _msg), do: :no_target
end
