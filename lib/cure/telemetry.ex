defmodule Cure.Telemetry do
  @moduledoc """
  `:telemetry` bridge for `Cure.Pipeline.Events` (v0.23.0).

  Started automatically when `Cure.Telemetry.start/0` is called from
  the host application. Subscribes to every pipeline stage on
  `Cure.Pipeline.Events` and re-emits events as `:telemetry` metrics
  so production deployments can feed compilation and Z3 latencies into
  whatever observability stack they already run.

  ## Event namespace

      [:cure, :pipeline, <stage>]  (lexer / parser / type_checker / codegen /
                                   registry)

  Each event carries:

  - `measurements`: `%{timestamp_us: integer, payload_size: non_neg_integer}`
  - `metadata`:     the original `{event_type, payload, meta}` tuple

  ## Starting

  `:telemetry` is an optional dependency. `start/0` returns `:ok`
  whether the library is available or not; when it is missing, the
  subscription silently becomes a no-op.
  """

  use GenServer

  @stages [:lexer, :parser, :type_checker, :codegen, :registry]

  # -- Public API -------------------------------------------------------------

  @doc """
  Start the telemetry bridge. Subscribes to every known pipeline stage.

  Idempotent: calling `start/0` twice in the same VM is safe.
  """
  @spec start() :: {:ok, pid()} | {:error, term()}
  def start, do: GenServer.start_link(__MODULE__, [], name: __MODULE__)

  @doc """
  Stop the bridge.
  """
  @spec stop() :: :ok
  def stop do
    case Process.whereis(__MODULE__) do
      nil ->
        :ok

      pid ->
        # `start/0` links the bridge to its caller, so it can already be dying by
        # the time a later `stop/0` (e.g. an ExUnit `on_exit` callback) runs — the
        # `whereis` above still returns a pid, but `GenServer.stop` then races the
        # termination and exits with `:noproc`. Swallow that so `stop/0` is truly
        # idempotent, as its `:: :ok` spec promises.
        try do
          GenServer.stop(pid)
        catch
          :exit, _ -> :ok
        end
    end
  end

  # -- GenServer callbacks ----------------------------------------------------

  @impl GenServer
  def init(_args) do
    Enum.each(@stages, fn stage ->
      try do
        Cure.Pipeline.Events.subscribe(stage)
      rescue
        _ -> :ok
      end
    end)

    {:ok, %{telemetry?: telemetry_loaded?()}}
  end

  @impl GenServer
  def handle_info({Cure.Pipeline.Events, stage, event_type, payload, meta}, state) do
    if state.telemetry? do
      dispatch_event(stage, event_type, payload, meta)
    end

    {:noreply, state}
  end

  def handle_info(_, state), do: {:noreply, state}

  # -- Internals --------------------------------------------------------------

  defp dispatch_event(stage, event_type, payload, meta) do
    name = [:cure, :pipeline, stage, event_type]

    measurements = %{
      timestamp_us: Map.get(meta, :timestamp, System.monotonic_time(:microsecond)),
      payload_size: :erlang.external_size(payload)
    }

    metadata = %{
      stage: stage,
      event_type: event_type,
      payload: payload,
      file: Map.get(meta, :file, "nofile"),
      line: Map.get(meta, :line, 0)
    }

    apply(:telemetry, :execute, [name, measurements, metadata])
  end

  defp telemetry_loaded? do
    Code.ensure_loaded?(:telemetry) and function_exported?(:telemetry, :execute, 3)
  end
end
