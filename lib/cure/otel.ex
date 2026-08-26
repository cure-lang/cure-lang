defmodule Cure.OTel do
  @moduledoc """
  OpenTelemetry bridge for Cure (v0.27.0).

  Every pipeline event on `Cure.Pipeline.Events` plus every span
  opened manually by compiler / runtime code is emitted as an OTel
  span. Three delivery backends are supported, in priority order:

    1. A user-supplied exporter function (`exporter: &fun/1`).
    2. The `:opentelemetry_api` library if it is on the load path.
    3. The bundled `Cure.OTel.MemoryExporter`, which stashes every
       span in an ETS table keyed by trace id. Intended for tests
       and the `examples/cure_atelier/` showcase.

  The bridge is an optional, idempotent GenServer -- calling
  `Cure.OTel.start/0` twice is safe. Without a running bridge, the
  public helpers (`span/3`, `inject_ctx/1`, `extract_ctx/1`) degrade
  to no-ops so library and application code never needs to branch on
  availability.

  ## Event namespace

  Span names follow `cure.<stage>.<event_type>` for pipeline events
  (`cure.type_checker.function_checked`, `cure.registry.fetch_ok`, ...)
  and `cure.<domain>.<op>` for manually-opened spans
  (`cure.process.send`, `cure.state.transition`, `cure.smt.query`).

  ## Span envelope

  Every emitted span is a map:

      %{
        name: "cure.process.send",
        trace_id: binary,
        span_id: binary,
        parent_span_id: binary | nil,
        start_us: integer,
        end_us: integer,
        attributes: %{...},
        status: :ok | :error
      }

  Exporters receive one such map per span.

  ## Cross-process context

  `inject_ctx/1` returns a context map suitable to be carried alongside
  a Melquiades Operator message. `extract_ctx/1` consumes such a map
  and re-seeds the caller process's current span so that
  `Cure.OTel.span/3` nested there becomes a child of the originating
  span. The raw wire shape is `{:cure_otel, trace_id, span_id}`.
  """

  use GenServer

  alias Cure.Pipeline.Events

  @stages [:lexer, :parser, :type_checker, :codegen, :registry]

  @ctx_key {__MODULE__, :ctx}

  # -- Public API -------------------------------------------------------------

  @doc """
  Start the OTel bridge.

  ## Options

    * `:exporter` -- a 1-ary function called as `exporter.(span)`
      for every completed span. If absent, the bundled
      `Cure.OTel.MemoryExporter` is used.
    * `:service_name` -- stamped on every span's attributes. Default:
      `"cure"`.
    * `:sample_ratio` -- float in `[0.0, 1.0]`. Default: `1.0`.

  Idempotent: returns the existing pid if the bridge is already up.
  """
  @spec start(keyword()) :: {:ok, pid()} | {:error, term()}
  def start(opts \\ []) do
    case Process.whereis(__MODULE__) do
      nil -> GenServer.start(__MODULE__, opts, name: __MODULE__)
      pid -> {:ok, pid}
    end
  end

  @doc "Stop the OTel bridge. Idempotent and tolerant of races."
  @spec stop() :: :ok
  def stop do
    case Process.whereis(__MODULE__) do
      nil ->
        :ok

      pid ->
        try do
          GenServer.stop(pid, :normal, 500)
        catch
          :exit, _ -> :ok
        end
    end

    :ok
  end

  @doc """
  True when an OTel bridge is currently running.
  """
  @spec running?() :: boolean()
  def running?, do: Process.whereis(__MODULE__) != nil

  @doc """
  Open a span `name` for the duration of `fun`, passing the span
  attributes. Returns whatever `fun` returns.

  When no bridge is running, simply evaluates `fun` with no
  observability side effect.
  """
  @spec span(String.t(), map(), (-> any())) :: any()
  def span(name, attributes, fun)
      when is_binary(name) and is_map(attributes) and is_function(fun, 0) do
    if running?() do
      start_us = System.monotonic_time(:microsecond)
      {trace_id, parent_span_id} = current_ctx()
      span_id = fresh_span_id()
      set_ctx({trace_id, span_id})

      try do
        result = fun.()
        record_span(name, trace_id, span_id, parent_span_id, start_us, attributes, :ok)
        result
      rescue
        e ->
          record_span(name, trace_id, span_id, parent_span_id, start_us, attributes, :error)
          reraise e, __STACKTRACE__
      after
        set_ctx({trace_id, parent_span_id})
      end
    else
      fun.()
    end
  end

  @doc """
  Return a context token that can be injected into a message so the
  receiving side can continue the current span chain via `extract_ctx/1`.
  """
  @spec inject_ctx(keyword()) :: {:cure_otel, binary(), binary()} | :none
  def inject_ctx(_opts \\ []) do
    case Process.get(@ctx_key) do
      {trace_id, span_id} -> {:cure_otel, trace_id, span_id}
      _ -> :none
    end
  end

  @doc """
  Adopt the given context token as the current span.
  """
  @spec extract_ctx({:cure_otel, binary(), binary()} | :none) :: :ok
  def extract_ctx({:cure_otel, trace_id, span_id})
      when is_binary(trace_id) and is_binary(span_id) do
    set_ctx({trace_id, span_id})
    :ok
  end

  def extract_ctx(:none), do: :ok
  def extract_ctx(_), do: :ok

  @doc """
  Clear the current span context from the process dictionary.
  """
  @spec clear_ctx() :: :ok
  def clear_ctx do
    Process.delete(@ctx_key)
    :ok
  end

  @doc """
  Force a fresh trace id so the next `span/3` call roots a new trace.
  """
  @spec new_trace() :: :ok
  def new_trace do
    set_ctx({fresh_trace_id(), nil})
    :ok
  end

  # -- GenServer callbacks ----------------------------------------------------

  @impl GenServer
  def init(opts) do
    exporter = Keyword.get(opts, :exporter) || default_exporter()
    service_name = Keyword.get(opts, :service_name, "cure")
    sample_ratio = Keyword.get(opts, :sample_ratio, 1.0)

    Enum.each(@stages, fn stage ->
      try do
        Events.subscribe(stage)
      rescue
        _ -> :ok
      end
    end)

    {:ok,
     %{
       exporter: exporter,
       service_name: service_name,
       sample_ratio: sample_ratio
     }}
  end

  @impl GenServer
  def handle_info(
        {Cure.Pipeline.Events, stage, event_type, payload, meta},
        state
      ) do
    name = "cure.#{stage}.#{event_type}"
    attributes = build_attributes(payload, meta, state.service_name)
    now = meta_us(meta)

    span = %{
      name: name,
      trace_id: fresh_trace_id(),
      span_id: fresh_span_id(),
      parent_span_id: nil,
      start_us: now,
      end_us: now,
      attributes: attributes,
      status: if(event_type in error_events(), do: :error, else: :ok)
    }

    deliver(span, state)

    {:noreply, state}
  end

  def handle_info(_, state), do: {:noreply, state}

  @impl GenServer
  def handle_cast({:export, span}, state) do
    deliver(span, state)
    {:noreply, state}
  end

  # -- Internals --------------------------------------------------------------

  defp deliver(span, %{exporter: exporter, sample_ratio: ratio}) do
    if sample?(ratio) do
      try do
        exporter.(span)
      rescue
        _ -> :ok
      end
    end

    :ok
  end

  defp sample?(ratio) when ratio >= 1.0, do: true
  defp sample?(ratio) when ratio <= 0.0, do: false
  defp sample?(ratio), do: :rand.uniform() < ratio

  defp record_span(name, trace_id, span_id, parent, start_us, attrs, status) do
    end_us = System.monotonic_time(:microsecond)

    span = %{
      name: name,
      trace_id: trace_id,
      span_id: span_id,
      parent_span_id: parent,
      start_us: start_us,
      end_us: end_us,
      attributes: attrs,
      status: status
    }

    GenServer.cast(__MODULE__, {:export, span})
    :ok
  end

  defp current_ctx do
    case Process.get(@ctx_key) do
      {trace_id, parent_span_id} -> {trace_id, parent_span_id}
      _ -> {fresh_trace_id(), nil}
    end
  end

  defp set_ctx({_trace_id, _span_id} = ctx), do: Process.put(@ctx_key, ctx)

  defp fresh_trace_id, do: :crypto.strong_rand_bytes(16)
  defp fresh_span_id, do: :crypto.strong_rand_bytes(8)

  defp default_exporter do
    Cure.OTel.MemoryExporter.start()
    &Cure.OTel.MemoryExporter.record/1
  end

  defp build_attributes(payload, meta, service_name) do
    %{
      "service.name" => service_name,
      "cure.file" => Map.get(meta, :file, "nofile"),
      "cure.line" => Map.get(meta, :line, 0),
      "cure.payload_size" => :erlang.external_size(payload)
    }
  end

  defp meta_us(meta) do
    case Map.get(meta, :timestamp) do
      nil -> System.monotonic_time(:microsecond)
      ts when is_integer(ts) -> ts
      _ -> System.monotonic_time(:microsecond)
    end
  end

  defp error_events do
    [
      :error,
      :fetch_failed,
      :hash_mismatch,
      :signature_invalid,
      :transparency_failed,
      :type_error,
      :parse_error,
      :lex_error,
      :codegen_error
    ]
  end
end
