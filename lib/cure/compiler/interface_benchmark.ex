defmodule Cure.Compiler.InterfaceBenchmark do
  @moduledoc """
  Reproducible cold/warm timing for the canonical module pipeline.

  A cold sample starts without a checked-interface cache. Warm samples compile
  the identical source universe against the cache published by the preceding
  run. Reports retain the pipeline's own phase and SCC/component timings plus
  `rebuilt_modules`, so a fast-looking sample cannot masquerade as cache reuse.

  Measurements are diagnostics, not correctness thresholds. Persist reports
  from representative machines and compare like-for-like source universes.
  """

  alias Cure.Compiler.ModulePipeline
  alias Cure.Core.Kernel
  alias Cure.Elab.CallAttemptProfile

  @type sample :: %{
          total_us: non_neg_integer(),
          phases: %{atom() => non_neg_integer()},
          components: [%{modules: [String.t()], elapsed_us: non_neg_integer()}],
          declarations: [declaration_timing()],
          declaration_stages: [declaration_stage_timing()],
          kernel_certificate_stages: [kernel_certificate_stage_timing()],
          totality_metrics: [map()],
          call_attempts: [map()],
          rebuilt_modules: [String.t()]
        }

  @type declaration_timing :: %{
          module: String.t(),
          declaration: String.t(),
          elapsed_us: non_neg_integer()
        }

  @type declaration_stage_timing :: %{
          module: String.t(),
          declaration: String.t(),
          stage: atom(),
          elapsed_us: non_neg_integer()
        }

  @type kernel_certificate_stage_timing :: %{
          definition: atom(),
          stage: atom(),
          elapsed_us: non_neg_integer()
        }

  @spec run([Path.t()], keyword()) :: {:ok, map()} | {:error, term()}
  def run(paths, opts \\ []) when is_list(paths) do
    iterations = Keyword.get(opts, :warm_iterations, 3)
    profile_call_attempts? = Keyword.get(opts, :profile_call_attempts, false)

    with true <- is_integer(iterations) and iterations > 0,
         expanded when expanded != [] <- paths |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort() do
      subscribe_totality_metrics()

      cache_root =
        Path.join(
          System.tmp_dir!(),
          "cure_canonical_interface_benchmark_#{System.unique_integer([:positive, :monotonic])}"
        )

      try do
        File.rm_rf!(cache_root)

        pipeline_opts = [
          module_pipeline: :canonical,
          package: "interface-benchmark",
          source_roots: expanded |> Enum.map(&Path.dirname/1) |> Enum.uniq(),
          cache: cache_root
        ]

        with {:ok, cold} <- timed_run(expanded, pipeline_opts, profile_call_attempts?),
             {:ok, warm} <- warm_samples(expanded, pipeline_opts, iterations, profile_call_attempts?) do
          {:ok,
           %{
             pipeline: :canonical,
             source_count: length(expanded),
             warm_iterations: iterations,
             cold: cold,
             warm: warm
           }}
        end
      after
        File.rm_rf!(cache_root)
      end
    else
      false -> {:error, {:invalid_warm_iterations, iterations}}
      [] -> {:error, :no_sources}
    end
  end

  @doc "Returns the slowest timing entries with stable tie ordering."
  @spec slowest([map()], non_neg_integer()) :: [map()]
  def slowest(timings, limit) when is_list(timings) and is_integer(limit) and limit >= 0 do
    timings
    |> Enum.sort_by(fn timing ->
      {-Map.fetch!(timing, :elapsed_us), Map.get(timing, :module, ""), Map.get(timing, :declaration, ""),
       Map.get(timing, :stage, :none)}
    end)
    |> Enum.take(limit)
  end

  defp warm_samples(paths, opts, iterations, profile_call_attempts?) do
    Enum.reduce_while(1..iterations, {:ok, []}, fn _, {:ok, samples} ->
      case timed_run(paths, opts, profile_call_attempts?) do
        {:ok, sample} -> {:cont, {:ok, [sample | samples]}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, samples} -> {:ok, Enum.reverse(samples)}
      error -> error
    end
  end

  defp timed_run(paths, opts, profile_call_attempts?) do
    owner = self()
    reference = make_ref()
    event_sink = &send(owner, {reference, &1})
    started = System.monotonic_time(:microsecond)

    operation = fn ->
      Kernel.with_certificate_timing_sink(event_sink, fn ->
        ModulePipeline.check(paths, Keyword.put(opts, :event_sink, event_sink))
      end)
    end

    {pipeline_result, call_attempts} =
      if profile_call_attempts? do
        CallAttemptProfile.run(operation)
      else
        {operation.(), []}
      end

    case pipeline_result do
      {:ok, result} ->
        total = System.monotonic_time(:microsecond) - started
        events = drain_events(reference, [])
        totality_metrics = drain_totality_metrics([])

        {:ok,
         %{
           total_us: total,
           phases: phase_timings(events),
           components: component_timings(events),
           declarations: declaration_timings(events),
           declaration_stages: declaration_stage_timings(events),
           kernel_certificate_stages: kernel_certificate_stage_timings(events),
           totality_metrics: totality_metrics,
           call_attempts: call_attempts,
           rebuilt_modules: ModulePipeline.rebuilt_modules(result)
         }}

      {:error, reason} ->
        _discarded = drain_events(reference, [])
        _discarded_totality = drain_totality_metrics([])
        {:error, {:canonical_interface_benchmark_failed, reason}}
    end
  end

  defp subscribe_totality_metrics do
    subscribe_once(:kernel)
    subscribe_once(:type_checker)
  end

  defp subscribe_once(stage) do
    case Registry.register(Cure.Pipeline.Events.Registry, stage, :all) do
      {:ok, _} -> :ok
      {:error, {:already_registered, _pid}} -> :ok
    end
  end

  defp drain_totality_metrics(events) do
    receive do
      {Cure.Pipeline.Events, stage, :totality_metric, payload, _metadata}
      when stage in [:kernel, :type_checker] ->
        drain_totality_metrics([Map.put(payload, :stage, stage) | events])
    after
      0 -> Enum.reverse(events)
    end
  end

  defp drain_events(reference, events) do
    receive do
      {^reference, event} -> drain_events(reference, [event | events])
    after
      0 -> Enum.reverse(events)
    end
  end

  defp phase_timings(events) do
    for {:module_pipeline_timing, phase, elapsed, _metadata} <- events,
        phase in [:interface_load, :manifest, :expansion, :module_check, :emission, :publication],
        into: %{} do
      {phase, elapsed}
    end
  end

  defp component_timings(events) do
    for {:module_pipeline_timing, :component, elapsed, %{modules: modules}} <- events do
      %{modules: modules, elapsed_us: elapsed}
    end
  end

  defp declaration_timings(events) do
    for {:module_pipeline_timing, :declaration, elapsed, %{module: module, declaration: declaration}} <- events do
      %{module: module, declaration: declaration, elapsed_us: elapsed}
    end
  end

  defp declaration_stage_timings(events) do
    for {:module_pipeline_timing, :declaration_stage, elapsed,
         %{module: module, declaration: declaration, stage: stage}} <- events do
      %{module: module, declaration: declaration, stage: stage, elapsed_us: elapsed}
    end
  end

  defp kernel_certificate_stage_timings(events) do
    for {:kernel_certificate_timing, stage, elapsed, %{definition: definition}} <- events do
      %{definition: definition, stage: stage, elapsed_us: elapsed}
    end
  end
end
