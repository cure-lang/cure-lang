defmodule Mix.Tasks.Cure.Replay do
  @shortdoc "Replay a recorded FSM trace from a .journal file"

  @moduledoc """
  Replay a recorded FSM/actor trace produced by a `@record`-annotated container.

  Journal files are written to `.cure-trace/` by `Cure.Observe.Journal.flush/1`
  when the decorated process terminates, or by calling `flush/1` manually.

  ## Usage

      mix cure.replay .cure-trace/abc123.journal [--module MyFsm] [--step]

  If `--module` is omitted, the replay only prints the trace without
  live replay (useful for inspection).

  ## Options

    * `--module` / `-m` -- the FSM module to replay against
    * `--step`   / `-s` -- pause after each event (single-step mode)
    * `--print`         -- print the trace before replaying (default: true)

  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [module: :string, step: :boolean, print: :boolean],
        aliases: [m: :module, s: :step]
      )

    if invalid != [] or length(rest) > 1 do
      usage_error("Usage: mix cure.replay <path.journal> [--module ModuleName] [--step]")
    end

    path = List.first(rest)

    if is_nil(path) do
      usage_error("Usage: mix cure.replay <path.journal> [--module ModuleName] [--step]")
    end

    case Cure.Observe.Journal.load(path) do
      {:error, reason} ->
        Mix.Shell.IO.error(render_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason)))
        exit({:shutdown, 1})

      {:ok, entries} ->
        Mix.Shell.IO.info("Loaded #{length(entries)} journal entries from #{path}")

        if Keyword.get(opts, :print, true) do
          Mix.Shell.IO.info("\nTrace:")
          Cure.Observe.Replay.print_trace(entries)
        end

        case Keyword.get(opts, :module) do
          nil ->
            Mix.Shell.IO.info("\n(pass --module ModuleName to replay against a live FSM)")

          mod_str ->
            mod = Module.concat([mod_str])

            if verified_project_module?(mod) do
              step? = Keyword.get(opts, :step, false)
              Mix.Shell.IO.info("\nReplaying against #{mod_str}#{if step?, do: " (step mode)", else: ""}...")

              case Cure.Observe.Replay.replay(mod, entries, step: step?) do
                {:ok, :quit} ->
                  Mix.Shell.IO.info("Replay quit early.")

                {:ok, results} ->
                  ok = Enum.count(results, fn {_, _, _, outcome} -> outcome == :ok end)
                  warn = length(results) - ok
                  Mix.Shell.IO.info("Replay complete: #{ok} ok, #{warn} warnings.")

                {:error, reason} ->
                  Mix.Shell.IO.error(render_diagnostic(Cure.Diagnostic.Operational.command_failure("Replay", reason)))

                  exit({:shutdown, 1})
              end
            else
              Mix.Shell.IO.error(
                render_diagnostic(
                  Cure.Diagnostic.Operational.artifact_error(
                    "Module #{mod_str} is not loaded. Compile the project first."
                  )
                )
              )

              exit({:shutdown, 1})
            end
        end
    end
  end

  defp verified_project_module?(module) do
    case Cure.Compiler.Artifacts.load_verified_modules(
           "_build/cure/project/ebin",
           [module]
         ) do
      :ok -> true
      {:error, _reason} -> false
    end
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    Mix.Shell.IO.error(render_diagnostic(Cure.Diagnostic.Operational.usage(message)))
    exit({:shutdown, 1})
  end
end
