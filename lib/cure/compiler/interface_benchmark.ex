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
          sample_kind: :cold | :warm,
          source_universe_hash: String.t(),
          stdlib_source_hashes: %{String.t() => String.t()},
          component_members: [[String.t()]],
          component_edges: [%{source: String.t(), target: String.t(), kind: atom()}],
          component_stage_us: [%{modules: [String.t()], phase: atom(), elapsed_us: non_neg_integer()}],
          phases: %{atom() => non_neg_integer()},
          components: [%{modules: [String.t()], elapsed_us: non_neg_integer()}],
          declarations: [declaration_timing()],
          declaration_stages: [declaration_stage_timing()],
          kernel_certificate_stages: [kernel_certificate_stage_timing()],
          totality_metrics: [map()],
          call_attempts: [map()],
          call_metrics: %{optional(atom()) => non_neg_integer()},
          rebuilt_modules: [String.t()]
        }

  @type declaration_timing :: %{
          module: String.t(),
          declaration: String.t(),
          canonical_declaration: String.t(),
          arity: non_neg_integer(),
          fingerprint: String.t(),
          elapsed_us: non_neg_integer(),
          call_metrics: %{optional(atom()) => non_neg_integer()}
        }

  @type declaration_stage_timing :: %{
          module: String.t(),
          declaration: String.t(),
          canonical_declaration: String.t(),
          arity: non_neg_integer(),
          fingerprint: String.t(),
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

    with :ok <- validate_iterations(:warm_iterations, iterations),
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

        with {:ok, cold} <- timed_run(expanded, pipeline_opts, profile_call_attempts?, :cold),
             {:ok, warm} <- warm_samples(expanded, pipeline_opts, iterations, profile_call_attempts?) do
          {:ok,
           %{
             pipeline: :canonical,
             source_count: length(expanded),
             warm_iterations: iterations,
             doc_fence_setting: doc_fence_setting(),
             cold: cold,
             warm: warm
           }}
        end
      after
        File.rm_rf!(cache_root)
      end
    else
      {:error, _} = error -> error
      [] -> {:error, :no_sources}
    end
  end

  @doc "Run serialized cold/warm pairs against fresh cache generations."
  @spec run_repeated([Path.t()], keyword()) :: {:ok, map()} | {:error, term()}
  def run_repeated(paths, opts \\ []) when is_list(paths) do
    samples = Keyword.get(opts, :samples, 3)

    if not (is_integer(samples) and samples > 0) do
      {:error, {:invalid_samples, samples}}
    else
      opts = opts |> Keyword.delete(:samples) |> Keyword.put(:warm_iterations, 1)

      with {:ok, reports} <- repeated_reports(paths, opts, samples),
           :ok <- same_source_universe?(reports),
           :ok <- same_doc_fence_setting?(reports) do
        first = List.first(reports)
        cold_samples = Enum.map(reports, & &1.cold)
        warm_samples = Enum.flat_map(reports, & &1.warm)

        {:ok,
         first
         |> Map.put(:samples, samples)
         |> Map.put(:reports, reports)
         |> Map.put(:cold_samples, cold_samples)
         |> Map.put(:warm_samples, warm_samples)
         |> Map.put(:cold_summary, timing_summary(cold_samples))
         |> Map.put(:warm_summary, timing_summary(warm_samples))
         |> Map.put(
           :regex_component_summary,
           cold_samples |> Enum.map(&regex_component_us/1) |> Enum.map(&%{total_us: &1}) |> timing_summary()
         )}
      end
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
      case timed_run(paths, opts, profile_call_attempts?, :warm) do
        {:ok, sample} -> {:cont, {:ok, [sample | samples]}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, samples} -> {:ok, Enum.reverse(samples)}
      error -> error
    end
  end

  defp repeated_reports(paths, opts, count) do
    Enum.reduce_while(1..count, {:ok, []}, fn _, {:ok, reports} ->
      case run_isolated(paths, opts) do
        {:ok, report} -> {:cont, {:ok, [report | reports]}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, reports} -> {:ok, Enum.reverse(reports)}
      error -> error
    end
  end

  # A clean sample must not inherit process-local loader state, normalisation
  # lenses, or large interface terms from the previous sample. The samples are
  # still strictly serial: the next worker is not spawned until this one has
  # returned. A worker also gives the VM a natural reclamation boundary instead
  # of requiring benchmark code to know every process-dictionary key used by
  # the elaborator.
  defp run_isolated(paths, opts) do
    parent = self()
    reference = make_ref()

    {pid, monitor} =
      spawn_monitor(fn ->
        send(parent, {reference, run(paths, opts)})
      end)

    receive do
      {^reference, result} ->
        Process.demonitor(monitor, [:flush])
        result

      {:DOWN, ^monitor, :process, ^pid, reason} ->
        {:error, {:benchmark_worker_failed, reason}}
    after
      30 * 60 * 1_000 ->
        Process.exit(pid, :kill)
        {:error, {:benchmark_worker_timeout, 30 * 60}}
    end
  end

  defp same_source_universe?(reports) do
    hashes = reports |> Enum.map(& &1.cold.source_universe_hash) |> Enum.uniq()
    if length(hashes) == 1, do: :ok, else: {:error, {:source_universe_changed, hashes}}
  end

  defp same_doc_fence_setting?(reports) do
    settings = reports |> Enum.map(& &1.doc_fence_setting) |> Enum.uniq()
    if length(settings) == 1, do: :ok, else: {:error, {:doc_fence_setting_changed, settings}}
  end

  defp timing_summary([]), do: %{median_us: 0, minimum_us: 0, maximum_us: 0, samples: 0}

  defp timing_summary(samples) do
    values = samples |> Enum.map(& &1.total_us) |> Enum.sort()
    %{median_us: median(values), minimum_us: List.first(values), maximum_us: List.last(values), samples: length(values)}
  end

  defp regex_component_us(sample) do
    sample.components
    |> Enum.filter(fn %{modules: modules} -> Enum.any?(modules, &String.starts_with?(&1, "Std.Regex")) end)
    |> Enum.reduce(0, &(&2 + &1.elapsed_us))
  end

  defp median(values) do
    middle = div(length(values), 2)

    if rem(length(values), 2) == 1,
      do: Enum.at(values, middle),
      else: div(Enum.at(values, middle - 1) + Enum.at(values, middle), 2)
  end

  defp validate_iterations(name, value) do
    if is_integer(value) and value > 0,
      do: :ok,
      else: {:error, {String.to_atom("invalid_" <> Atom.to_string(name)), value}}
  end

  defp timed_run(paths, opts, profile_call_attempts?, sample_kind) do
    owner = self()
    reference = make_ref()
    event_sink = &send(owner, {reference, &1})
    started = System.monotonic_time(:microsecond)

    operation = fn ->
      Kernel.with_certificate_timing_sink(event_sink, fn ->
        ModulePipeline.check(paths, Keyword.put(opts, :event_sink, event_sink))
      end)
    end

    {pipeline_result, call_attempts, call_metrics} =
      if profile_call_attempts? do
        {{result, metrics}, attempts} =
          CallAttemptProfile.run(fn ->
            result = operation.()
            {result, CallAttemptProfile.metrics()}
          end)

        {result, attempts, metrics}
      else
        {operation.(), [], %{}}
      end

    case pipeline_result do
      {:ok, result} ->
        total = System.monotonic_time(:microsecond) - started
        events = drain_events(reference, [])
        totality_metrics = drain_totality_metrics([])

        {:ok,
         %{
           total_us: total,
           sample_kind: sample_kind,
           source_universe_hash: source_universe_hash(result),
           stdlib_source_hashes: stdlib_source_hashes(result),
           component_members: component_members(result),
           component_edges: component_edges(result),
           component_stage_us: component_stage_timings(events),
           phases: phase_timings(events),
           components: component_timings(events),
           declarations: declaration_timings(events),
           declaration_stages: declaration_stage_timings(events),
           kernel_certificate_stages: kernel_certificate_stage_timings(events),
           totality_metrics: totality_metrics,
           call_attempts: call_attempts,
           call_metrics: call_metrics,
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

  defp component_stage_timings(events) do
    for {:module_pipeline_timing, phase, elapsed, %{modules: modules}} <- events,
        phase in [:component_register, :component_merge, :component_bodies, :component_freeze] do
      %{modules: modules, phase: phase, elapsed_us: elapsed}
    end
  end

  defp declaration_timings(events) do
    for {:module_pipeline_timing, :declaration, elapsed, metadata} <- events do
      %{
        module: metadata.module,
        declaration: metadata.declaration,
        canonical_declaration: metadata.canonical_declaration,
        arity: metadata.arity,
        fingerprint: metadata.fingerprint,
        elapsed_us: elapsed,
        call_metrics: Map.get(metadata, :call_metrics, %{})
      }
    end
  end

  defp declaration_stage_timings(events) do
    for {:module_pipeline_timing, :declaration_stage, elapsed, metadata} <- events do
      %{
        module: metadata.module,
        declaration: metadata.declaration,
        canonical_declaration: metadata.canonical_declaration,
        arity: metadata.arity,
        fingerprint: metadata.fingerprint,
        stage: metadata.stage,
        elapsed_us: elapsed
      }
    end
  end

  defp kernel_certificate_stage_timings(events) do
    for {:kernel_certificate_timing, stage, elapsed, %{definition: definition}} <- events do
      %{definition: definition, stage: stage, elapsed_us: elapsed}
    end
  end

  defp source_universe_hash(%{manifest: manifest}) do
    canonical = manifest |> Cure.Compiler.ModuleManifest.canonical_dump() |> :erlang.term_to_binary([:deterministic])
    canonical |> then(&:crypto.hash(:sha256, &1)) |> Base.encode16(case: :lower)
  end

  defp stdlib_source_hashes(%{manifest: %{entries: entries}}) do
    entries
    |> Enum.map(fn {_identity, entry} -> {entry.module_name, Base.encode16(entry.source_hash, case: :lower)} end)
    |> Map.new()
  end

  defp component_members(%{components: components}) do
    Enum.map(components, fn component -> Enum.map(component, &elem(&1, 1)) |> Enum.sort() end)
  end

  defp component_edges(%{manifest: manifest}) do
    manifest
    |> Cure.Compiler.ModuleManifest.semantic_dump()
    |> Enum.flat_map(fn entry ->
      Enum.map(entry.dependencies, fn dependency ->
        %{source: elem(entry.identity, 1), target: elem(dependency.target, 1), kind: dependency.kind}
      end)
    end)
    |> Enum.uniq()
    |> Enum.sort_by(&{&1.source, &1.target, &1.kind})
  end

  defp doc_fence_setting do
    case System.get_env("CURE_SKIP_DOC_FENCES") do
      nil -> :enabled
      value -> {:skipped, value}
    end
  end
end
