defmodule CureSiteWeb.Yeesh.CallableRunner do
  @moduledoc """
  Mix-free analogue of `Yeesh.MixRunner` for the Cure site.

  Hosts an arbitrary 0-arity function under a `Yeesh.IOServer` group
  leader so its `IO.puts`/`IO.gets` traffic is transparently captured
  and surfaced through the Yeesh browser terminal. Unlike
  `Yeesh.MixRunner`, this runner does **not** depend on `Mix` at
  runtime, which is what lets the `repl` command keep working inside
  a `MIX_ENV=prod` release where `:mix` is intentionally absent from
  the application list.

  The return shape deliberately mirrors `Yeesh.MixRunner.run/3`:

    * `{:completed, output}` -- the function returned without asking
      for input.
    * `{:interactive, io_server, task_pid, output, prompt}` -- the
      function called `IO.gets` and is now blocked waiting for a
      reply. The caller stashes `io_server` and `task_pid` in the
      Yeesh session context under the same keys (`:mix_io_server`,
      `:mix_task_pid`, `:mix_prompt`, `:mix_original_shell`) so the
      executor's existing `:mix_task` mode plumbing resumes it
      identically to a Mix task.
    * `{:error, reason}` -- the runner itself failed to bootstrap
      (e.g. `Yeesh.IOServer.start_link/1` returned an error).
  """

  alias Yeesh.IOServer
  alias Cure.Diagnostic.{Host, Operational}

  @typedoc "Result tuple compatible with the Yeesh executor's `:mix_task` mode."
  @type run_result ::
          {:completed, String.t()}
          | {:interactive, pid(), pid(), String.t(), String.t()}
          | {:error, term()}

  @default_timeout 30_000

  @doc """
  Runs `fun` in a separate process whose group leader is a freshly
  started `Yeesh.IOServer`. Returns a result tuple compatible with
  the Yeesh executor's `:mix_task` session mode.

  ## Options

    * `:timeout` -- how long to wait for the function to produce
      initial output or request input (default:
      `#{@default_timeout}`ms).
  """
  @spec run((-> any()), keyword()) :: run_result()
  def run(fun, opts \\ []) when is_function(fun, 0) do
    with {:ok, io_server} <- IOServer.start_link() do
      do_run(io_server, fun, opts)
    end
  rescue
    e -> {:error, render_exception(e, __STACKTRACE__)}
  end

  defp do_run(io_server, fun, opts) do
    task_pid =
      spawn(fn ->
        Process.group_leader(self(), io_server)

        try do
          fun.()
        rescue
          e -> IO.puts(render_exception(e, __STACKTRACE__))
        end
      end)

    :ok = IOServer.monitor_task(io_server, task_pid)

    case IOServer.start_and_wait(io_server, opts) do
      {output, :waiting, prompt} ->
        {:interactive, io_server, task_pid, output, prompt}

      {output, :done} ->
        _ = stop(io_server)
        {:completed, output}
    end
  end

  @doc """
  Stops the `Yeesh.IOServer` started by `run/2`. The runner calls
  this automatically for non-interactive completions; callers are
  responsible for invoking it after an `:interactive` result, mirroring
  `Yeesh.MixRunner.cleanup/2`.
  """
  @spec stop(pid()) :: :ok
  def stop(io_server) do
    if Process.alive?(io_server) do
      IOServer.stop(io_server)
    end

    :ok
  end

  defp render_exception(exception, stacktrace) do
    diagnostic = Operational.internal_exception(exception, stacktrace, context: "site callable")
    Host.render_diagnostic(diagnostic, color: :never)
  end
end
