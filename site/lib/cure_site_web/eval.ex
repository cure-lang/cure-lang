defmodule CureSiteWeb.Eval do
  @moduledoc """
  Sandboxed server-side evaluator for the Cure Playground.

  Each evaluation request spawns an isolated BEAM process with hard
  resource limits (`:max_heap_size`, message queue limit, 2-second
  wall-clock kill timer). The child process compiles the submitted
  source, loads the resulting module, and calls `main/0` if it exists.
  The captured stdout and the function return value are returned to the
  caller as `{:ok, output, result}` or `{:error, reason}`.

  ## Security model

  This evaluator is **not** a hardened sandbox -- it runs user-supplied
  Cure source on the BEAM with process-level limits only. It is
  suitable for a public-facing playground only when:

  1. Each request is short-lived (< 2 s wall clock).
  2. Memory usage is bounded (64 MB heap limit).
  3. The BEAM process cannot access the file system, network, or OS
     (no NIF or port ops in the Cure stdlib).

  For production deployment, run `cure_site` in an OCI container or
  similar isolated environment.
  """

  alias Cure.Diagnostic.{Host, Operational}

  @timeout_ms 2_000
  @max_heap_words 8_000_000

  @type result :: {:ok, String.t(), term()} | {:error, String.t()}

  @doc """
  Evaluate Cure source in a sandboxed process.

  Returns `{:ok, stdout_output, return_value}` on success,
  or `{:error, error_message}` on compile/runtime failure or timeout.
  """
  @spec eval(String.t()) :: result()
  def eval(source) when is_binary(source) do
    parent = self()
    ref = make_ref()

    child =
      :erlang.spawn_opt(
        fn ->
          result = do_eval(source)
          send(parent, {ref, result})
        end,
        max_heap_size: @max_heap_words,
        message_queue_data: :off_heap
      )

    monitor_ref = Process.monitor(child)

    receive do
      {^ref, result} ->
        Process.demonitor(monitor_ref, [:flush])
        result

      {:DOWN, ^monitor_ref, :process, ^child, reason} ->
        format_exit_reason(reason)
    after
      @timeout_ms ->
        Process.demonitor(monitor_ref, [:flush])
        Process.exit(child, :kill)
        {:error, "Evaluation timed out after #{@timeout_ms} ms"}
    end
  end

  # -- Internal ----------------------------------------------------------------

  defp do_eval(source) do
    # Capture stdout from the compiled module's execution.
    output =
      capture_io(fn ->
        case compile_and_run(source) do
          {:ok, value} -> send(self(), {:eval_result, {:ok, value}})
          {:error, _} = err -> send(self(), {:eval_result, err})
        end
      end)

    receive do
      {:eval_result, {:ok, value}} ->
        {:ok, output, inspect(value)}

      {:eval_result, {:error, reason}} ->
        {:error, reason}
    after
      100 ->
        {:error, "Internal eval timeout"}
    end
  rescue
    e -> {:error, render_exception(e, __STACKTRACE__)}
  end

  # Lightweight stdout capture that does not depend on ExUnit (which is not
  # started outside the :test environment). Redirects the current process's
  # group leader to a `StringIO` device for the duration of `fun`.
  defp capture_io(fun) when is_function(fun, 0) do
    {:ok, string_io} = StringIO.open("")
    original_gl = Process.group_leader()
    true = Process.group_leader(self(), string_io)

    try do
      fun.()
    after
      Process.group_leader(self(), original_gl)
    end

    {:ok, {_input, output}} = StringIO.close(string_io)
    output
  end

  defp compile_and_run(source) do
    with {:ok, module} <-
           Cure.Compiler.compile_and_load(source,
             file: "playground.cure",
             emit_events: false
           ) do
      run_main(module)
    else
      {:error, reason} ->
        {:error, format_compile_error(reason)}
    end
  end

  defp run_main(module) do
    if function_exported?(module, :main, 0) do
      result = module.main()
      {:ok, result}
    else
      {:ok, :no_main}
    end
  rescue
    e -> {:error, render_exception(e, __STACKTRACE__)}
  end

  defp format_compile_error(reason) when is_binary(reason), do: reason
  defp format_compile_error(reason), do: Cure.Diagnostic.Host.render(reason, "playground.cure")

  defp format_exit_reason(:normal), do: {:ok, "", ":ok"}

  defp format_exit_reason(:killed),
    do: {:error, render_operational("playground evaluation", :killed)}

  defp format_exit_reason(reason),
    do: {:error, render_operational("playground evaluation", reason)}

  defp render_exception(exception, stacktrace) do
    exception
    |> Operational.internal_exception(stacktrace, context: "playground evaluation")
    |> Host.render_diagnostic(color: :never)
  end

  defp render_operational(command, reason) do
    Operational.command_failure(command, reason)
    |> Host.render_diagnostic(color: :never)
  end
end
