defmodule Cure.Observe.Journal do
  @moduledoc """
  ETS-backed trace journal for `@record`-annotated lifted process modules.

  Every opted-in transition or message callback appends an entry to an
  in-memory ETS table. Entries are flushed to disk as Erlang term
  files under `.cure-trace/<pid>.journal` so they survive process death
  and can be replayed later with `cure replay`.

  ## Entry format

  Each journal entry is a 5-tuple:

      {actor_id, state_before, event, state_after, timestamp_us}

  where:
  - `actor_id`   -- the PID (or a registered name atom) of the recorded process
  - `state_before` -- the FSM state atom before the transition
  - `event`      -- the event atom that triggered the transition
  - `state_after`  -- the FSM state atom after the transition (`:same` when
                      the callback retained the current state)
  - `timestamp_us` -- `:erlang.monotonic_time(:microsecond)` when recorded

  ## Usage

  Journal entries are written by generated process code when the lifted
  module carries an `@record` decorator. Users do not interact with this
  module directly; instead they use `cure replay <path>` or the REPL
  `:replay <path>` command after producing a trace.
  """

  @table :cure_journal
  @trace_dir ".cure-trace"

  # -- ETS management ----------------------------------------------------------

  @doc "Ensure the ETS journal table exists. Called from the FSM process init."
  @spec ensure_started() :: :ok
  def ensure_started do
    if :ets.whereis(@table) == :undefined do
      :ets.new(@table, [:named_table, :public, :ordered_set, write_concurrency: true])
    end

    :ok
  rescue
    ArgumentError -> :ok
  end

  @doc """
  Append one trace entry to the journal.

  `actor_id` is normally `self()` from the recording FSM process.
  """
  @spec record(term(), atom(), atom(), atom()) :: :ok
  def record(actor_id, state_before, event, state_after) do
    ensure_started()
    ts = :erlang.monotonic_time(:microsecond)
    entry = {actor_id, state_before, event, state_after, ts}
    :ets.insert(@table, {ts, entry})
    :ok
  end

  @doc "Return all journal entries in chronological order."
  @spec entries() :: [{term(), atom(), atom(), atom(), integer()}]
  def entries do
    ensure_started()
    :ets.tab2list(@table) |> Enum.sort_by(fn {ts, _} -> ts end) |> Enum.map(&elem(&1, 1))
  end

  @doc "Return journal entries for a specific actor process."
  @spec entries(term()) :: [{term(), atom(), atom(), atom(), integer()}]
  def entries(actor_id) do
    entries() |> Enum.filter(fn {id, _, _, _, _} -> id == actor_id end)
  end

  @doc "Clear all journal entries."
  @spec clear() :: :ok
  def clear do
    ensure_started()
    :ets.delete_all_objects(@table)
    :ok
  end

  @doc """
  Flush all journal entries for `actor_id` to
  `.cure-trace/<hex_pid>.journal` and return the path.
  """
  @spec flush(term()) :: {:ok, String.t()} | {:error, term()}
  def flush(actor_id) do
    ensure_started()
    File.mkdir_p!(@trace_dir)

    hex = actor_id |> :erlang.term_to_binary() |> Base.encode16(case: :lower)
    path = Path.join(@trace_dir, "#{hex}.journal")
    data = entries(actor_id)

    case :file.write_file(path, :erlang.term_to_binary(data)) do
      :ok -> {:ok, path}
      {:error, _} = err -> err
    end
  end

  @doc "Load a journal file from disk. Returns the list of entries."
  @spec load(String.t()) :: {:ok, list()} | {:error, term()}
  def load(path) do
    case File.read(path) do
      {:ok, bin} ->
        try do
          {:ok, :erlang.binary_to_term(bin)}
        rescue
          _ -> {:error, :invalid_format}
        end

      {:error, _} = err ->
        err
    end
  end
end
