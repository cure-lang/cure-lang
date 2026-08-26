defmodule Mix.Tasks.Cure.Repl do
  @moduledoc """
  Launches the interactive Cure REPL from inside a Mix project.

  Functionally identical to `./cure repl`, but usable from any Elixir
  project that has `:cure` on its dependency path. The task starts the
  `:cure` application, parses a small set of options, and delegates to
  `Cure.REPL.start/1`.

  ## Usage

      mix cure.repl
      mix cure.repl --theme=light
      mix cure.repl --no-raw --error-device=stdio
      mix cure.repl --history=/tmp/cure.history
      mix cure.repl --no-history

  ## Options

    * `--raw` / `--no-raw` -- force raw-mode line editing on or off.
      Default is `:auto`: the REPL detects whether it is attached to a
      controlling tty. Embedders that route I/O through a custom group
      leader (for example `Yeesh.IOServer`) should pass `--no-raw` so
      the line-mode fallback kicks in.
    * `--theme` -- one of `dark`, `light`, `mono`, `auto`. Default `auto`.
    * `--mode` -- initial editing mode: `emacs` or `vi`. Default `emacs`.
    * `--history` -- path to the history file. Default `~/.cure_history`.
    * `--no-history` -- disable history persistence.
    * `--error-device` -- where compiler diagnostics go: `stderr`
      (default) or `stdio`. Embedders that rely on the task's group
      leader should pass `--error-device=stdio`.

  ## Examples

      # Standalone, full raw-mode experience.
      mix cure.repl

      # Hosted under a custom group leader (no tty, plain line mode,
      # errors routed to stdio for the embedder to capture).
      mix cure.repl --no-raw --error-device=stdio --no-history
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink
  alias Cure.REPL.Options

  @shortdoc "Starts the interactive Cure REPL"

  @impl Mix.Task
  def run(args) do
    # `mix app.start` only makes sense when the task is invoked from
    # inside a Mix project. Guarding on `Mix.Project.get/0` keeps the
    # task usable from contexts where Mix is loaded but no project is
    # (e.g. a release that opted `:mix` into `extra_applications`).
    if Mix.Project.get(), do: Mix.Task.run("app.start", [])

    {parsed, rest, invalid} = OptionParser.parse(args, strict: Options.switches())

    if rest != [] or invalid != [] do
      usage_error("Invalid arguments for mix cure.repl: #{inspect(rest ++ invalid)}")
    end

    parsed
    |> build_opts()
    |> start_repl()
  end

  @doc """
  Translates a parsed keyword list of switches into the options keyword
  accepted by `Cure.REPL.start/1`.

  Any invalid switch values (for example `--theme=neon`) are reported
  via `Mix.shell().error/1` and dropped from the result. The actual
  parsing is delegated to `Cure.REPL.Options.build_opts/1`, which is
  Mix-free and therefore reusable from release-time entry points
  (such as the Yeesh browser terminal).
  """
  @spec build_opts(keyword()) :: keyword()
  def build_opts(parsed) do
    {opts, warnings} = Options.build_opts(parsed)

    Enum.each(warnings, fn message ->
      Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.configuration_warning(message)))
    end)

    opts
  end

  # Dispatch kept private so the task is mockable in tests: overriding
  # `start_repl/1` via an application env lets us exercise the full
  # arg-parsing path without blocking on `Cure.REPL.start/1`.
  defp start_repl(opts) do
    case Application.get_env(:cure, :repl_start_mfa) do
      {mod, fun, extra} when is_atom(mod) and is_atom(fun) and is_list(extra) ->
        apply(mod, fun, extra ++ [opts])

      _ ->
        Cure.REPL.start(opts)
    end
  end

  defp usage_error(message) do
    Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.usage(message)))
    exit({:shutdown, 1})
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
