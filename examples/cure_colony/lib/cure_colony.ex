defmodule CureColony do
  @moduledoc """
  Thin Elixir facade over the Cure colony supervision tree.

  The entire supervision tree is declared in three `.cure` files:

    * `cure_src/worker.cure` -- `actor Worker`
    * `cure_src/echo.cure`   -- `actor Echo`
    * `cure_src/colony.cure` -- `sup Colony`

  The compiled modules are, respectively, `Cure.Main.Worker`, `Cure.Main.Echo`,
  and `Cure.Main.Colony`. `CureColony.Application`
  starts `Cure.Main.Colony` under its own top-level `Supervisor`, which
  in turn starts two `Worker` instances and one `Echo` instance.

  ## Quick Start

      # The application starts the tree automatically:
      iex> is_pid(Process.whereis(:"Cure.Main.Colony"))
      true

      # Each child can be addressed by its supervisor id:
      iex> worker = CureColony.worker_a()
      iex> CureColony.inc(worker)
      iex> CureColony.inc(worker)
      iex> CureColony.worker_state(worker)
      2

      # Echo stores the last message it saw:
      iex> CureColony.echo_message(:ping)
      iex> CureColony.echo_state()
      :ping
  """

  @sup_module :"Cure.Main.Colony"
  @worker_module :"Cure.Main.Worker"
  @echo_module :"Cure.Main.Echo"

  @doc "Atom of the compiled supervisor module."
  @spec sup_module() :: module()
  def sup_module, do: @sup_module

  @doc "Atom of the compiled Worker actor module."
  @spec worker_module() :: module()
  def worker_module, do: @worker_module

  @doc "Atom of the compiled Echo actor module."
  @spec echo_module() :: module()
  def echo_module, do: @echo_module

  @doc """
  Return the list of children as `{id, pid, type, modules}` tuples,
  in the order reported by `Supervisor.which_children/1`.
  """
  @spec which_children() :: [tuple()]
  def which_children do
    Supervisor.which_children(@sup_module)
  end

  @doc "Return the pid of the `worker_a` child."
  @spec worker_a() :: pid() | nil
  def worker_a, do: child_pid(:worker_a)

  @doc "Return the pid of the `worker_b` child."
  @spec worker_b() :: pid() | nil
  def worker_b, do: child_pid(:worker_b)

  @doc "Return the pid of the `echo` child."
  @spec echo() :: pid() | nil
  def echo, do: child_pid(:echo)

  @doc "Increment `worker`'s counter and wait for the message to be handled."
  @spec inc(pid()) :: :ok
  def inc(worker), do: send_sync(worker, :inc)

  @doc "Reset `worker`'s counter to zero."
  @spec reset(pid()) :: :ok
  def reset(worker), do: send_sync(worker, :reset)

  @doc """
  Ask `worker` for its counter value. `notify(%[:value, n])` inside
  the `:get` clause would normally target the process that spawned
  the actor; under a supervisor that caller is the supervisor itself,
  so callers typically use `worker_state/1` instead.
  """
  @spec get(pid()) :: :ok
  def get(worker), do: send_sync(worker, :get)

  @doc "Send `message` to the echo actor."
  @spec echo_message(term()) :: :ok
  def echo_message(message) do
    case echo() do
      nil -> :no_echo
      pid -> send_sync(pid, message)
    end
  end

  @doc "Return the current payload for a worker pid."
  @spec worker_state(pid()) :: integer()
  def worker_state(worker), do: :sys.get_state(worker)

  @doc "Return the echo actor's current payload (the last message it saw)."
  @spec echo_state() :: term()
  def echo_state do
    case echo() do
      nil -> nil
      pid -> :sys.get_state(pid)
    end
  end

  # -- Internals ------------------------------------------------------------

  defp send_sync(pid, msg) do
    :gen_server.cast(pid, msg)
    _ = :sys.get_state(pid)
    :ok
  end

  defp child_pid(id) do
    Enum.find_value(which_children(), fn
      {^id, pid, _type, _modules} when is_pid(pid) -> pid
      _ -> nil
    end)
  end
end
