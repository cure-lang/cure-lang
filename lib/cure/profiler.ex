defmodule Cure.Profiler do
  @moduledoc """
  Compilation profiler for the Cure pipeline.

  Measures time spent in each compilation stage (lex, parse, type check,
  optimize, codegen, beam write) by subscribing to pipeline events.

  ## Usage

      # Profile a compilation
      {:ok, report} = Cure.Profiler.profile_file("hello.cure")
      IO.puts(Cure.Profiler.format_report(report))

      # Profile a string
      {:ok, report} = Cure.Profiler.profile_string(source)
  """

  alias Cure.Pipeline.Events

  @stages [:lexer, :parser, :type_checker, :codegen]

  @doc """
  Profile the compilation of a .cure file.

  Returns `{:ok, report}` where report contains timing data per stage.
  """
  @spec profile_file(String.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def profile_file(path, opts \\ []) do
    case File.read(path) do
      {:ok, source} -> profile_string(source, Keyword.put(opts, :file, path))
      {:error, reason} -> {:error, {:file_read_error, path, reason}}
    end
  end

  @doc """
  Profile the compilation of a source string.
  """
  @spec profile_string(String.t(), keyword()) :: {:ok, map()}
  def profile_string(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")

    # Subscribe to all pipeline events
    Enum.each(@stages, fn stage ->
      Events.subscribe(stage)
    end)

    # Run compilation with events enabled
    t_start = System.monotonic_time(:microsecond)

    compile_result =
      Cure.Compiler.compile_string(source,
        file: file,
        emit_events: true,
        check_types: Keyword.get(opts, :check_types, false),
        optimize: Keyword.get(opts, :optimize, false)
      )

    t_end = System.monotonic_time(:microsecond)

    # Collect events
    events = drain_events()

    # Build timing report
    stage_times = compute_stage_times(events)

    {result, diagnostic} =
      case compile_result do
        {:ok, _module, _warnings} ->
          {compile_result_summary(compile_result), nil}

        {:error, reason} ->
          {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)
          {"error [#{diagnostic.code}]", %{diagnostic: diagnostic, registry: registry}}
      end

    report = %{
      file: file,
      source_bytes: byte_size(source),
      total_us: t_end - t_start,
      stages: stage_times,
      event_count: length(events),
      result: result,
      diagnostic: diagnostic
    }

    report =
      case diagnostic do
        %{diagnostic: _diagnostic, registry: _registry} = details ->
          Map.put(report, :diagnostic, details)

        nil ->
          report
      end

    {:ok, report}
  end

  @doc """
  Format a profile report as a human-readable string.
  """
  @spec format_report(map()) :: String.t()
  def format_report(report) do
    total_ms = report.total_us / 1000

    stage_lines =
      report.stages
      |> Enum.sort_by(fn {_stage, data} -> -(data[:count] || 0) end)
      |> Enum.map(fn {stage, data} ->
        count = data[:count] || 0
        "  #{pad(Atom.to_string(stage), 20)} #{pad(Integer.to_string(count), 6)} events"
      end)

    """
    Cure Compilation Profile
    ========================
    File:         #{report.file}
    Source:       #{report.source_bytes} bytes
    Total time:   #{Float.round(total_ms, 2)} ms
    Events:       #{report.event_count}
    Result:       #{report.result}

    Pipeline Stages:
    #{Enum.join(stage_lines, "\n")}
    """
  end

  # -- Internal ----------------------------------------------------------------

  defp drain_events do
    drain_events([])
  end

  defp drain_events(acc) do
    receive do
      {Cure.Pipeline.Events, stage, event_type, payload, meta} ->
        event = %{
          stage: stage,
          type: event_type,
          payload_type: payload_type(payload),
          timestamp: Map.get(meta || %{}, :timestamp, 0)
        }

        drain_events([event | acc])
    after
      0 -> Enum.reverse(acc)
    end
  end

  defp compute_stage_times(events) do
    events
    |> Enum.group_by(& &1.stage)
    |> Enum.map(fn {stage, stage_events} ->
      {stage, %{count: length(stage_events)}}
    end)
    |> Map.new()
  end

  defp compile_result_summary({:ok, _module, warnings}) do
    if warnings == [], do: "success", else: "success (#{length(warnings)} warnings)"
  end

  defp payload_type(payload) when is_tuple(payload), do: elem(payload, 0)
  defp payload_type(payload) when is_atom(payload), do: payload
  defp payload_type(payload) when is_list(payload), do: :list
  defp payload_type(_), do: :other

  defp pad(str, width) do
    String.pad_trailing(str, width)
  end
end
