defmodule Cure.Watch do
  @moduledoc """
  Watch mode for Cure.

  Monitors a directory (or single file) for `.cure` source changes and
  re-runs the requested action on every change. The default action is
  `compile`; alternatives are `check` and `test`.

  This module is implemented without a hard dependency on the
  `:file_system` library so it stays usable even when that dep is not
  installed. When `:file_system` is available we use it; otherwise we
  fall back to a simple polling loop with a 500 ms cadence.

  ## Public API

      Cure.Watch.start(\"lib/\", action: :check)

  ## Options

  - `:action`   -- one of `:compile | :check | :test` (default `:compile`)
  - `:poll_ms`  -- polling interval for the fallback loop (default 500)
  - `:debounce` -- coalesce events for this many milliseconds (default 200)
  - `:patterns` -- glob patterns to watch (default `[\"**/*.cure\"]`)
  """

  @default_patterns ["**/*.cure"]

  @doc """
  Start watching `path` and run `action` whenever a relevant file changes.

  This call blocks the calling process indefinitely. Send a SIGINT to
  exit.
  """
  @spec start(String.t(), keyword()) :: no_return()
  def start(path, opts \\ []) do
    action = Keyword.get(opts, :action, :compile)
    patterns = Keyword.get(opts, :patterns, @default_patterns)
    poll_ms = Keyword.get(opts, :poll_ms, 500)
    debounce = Keyword.get(opts, :debounce, 200)

    info("watching #{path} (action: #{action})")
    info("press Ctrl-C to stop")

    loop_state = %{
      path: path,
      action: action,
      patterns: patterns,
      debounce: debounce,
      poll_ms: poll_ms,
      snapshot: snapshot(path, patterns),
      pending_since: nil
    }

    # Run once on entry so the first pass is immediate.
    run_action(action, path)
    loop(loop_state)
  end

  # -- Loop --------------------------------------------------------------------

  defp loop(state) do
    Process.sleep(state.poll_ms)
    new_snapshot = snapshot(state.path, state.patterns)

    if new_snapshot == state.snapshot do
      maybe_fire(state)
    else
      now = System.monotonic_time(:millisecond)
      loop(%{state | snapshot: new_snapshot, pending_since: state.pending_since || now})
    end
  end

  defp maybe_fire(%{pending_since: nil} = state), do: loop(state)

  defp maybe_fire(state) do
    elapsed = System.monotonic_time(:millisecond) - state.pending_since

    if elapsed >= state.debounce do
      run_action(state.action, state.path)
      loop(%{state | pending_since: nil})
    else
      loop(state)
    end
  end

  # -- Snapshot ----------------------------------------------------------------

  @doc """
  Build a snapshot of files matching the given patterns under `path`.

  The snapshot is a sorted list of `{path, mtime}` tuples that we
  compare to detect changes.
  """
  @spec snapshot(String.t(), [String.t()]) :: [{String.t(), integer()}]
  def snapshot(path, patterns) do
    base = if File.dir?(path), do: path, else: Path.dirname(path)

    patterns
    |> Enum.flat_map(fn pat -> Path.wildcard(Path.join(base, pat)) end)
    |> Enum.uniq()
    |> Enum.map(fn f ->
      case File.stat(f) do
        {:ok, %{mtime: m}} -> {f, m}
        _ -> {f, 0}
      end
    end)
    |> Enum.sort()
  end

  # -- Actions -----------------------------------------------------------------

  @doc false
  def run_action(:compile, path) do
    info("[#{ts()}] compiling #{path}")

    if File.dir?(path) do
      paths = Path.wildcard(Path.join(path, "**/*.cure"))

      case Cure.Compiler.compile_files(paths, emit_events: false, continue_on_error: true) do
        {:ok, %{compiled: compiled, errors: errors}} ->
          Enum.each(compiled, fn {source, module, _warnings} ->
            info("  #{source} -> #{module}")
          end)

          Enum.each(errors, fn {source, reason} ->
            emit_error(reason, source, read_source(source))
          end)

        {:error, reason} ->
          emit_error(reason, path, nil)
      end
    else
      case Cure.Compiler.compile_files([path], emit_events: false) do
        {:ok, %{compiled: [{_source, mod, _warnings}]}} ->
          info("  #{path} -> #{mod}")

        {:ok, %{compiled: []}} ->
          info("  #{path} is up-to-date")

        {:error, reason} ->
          emit_error(reason, path, read_source(path))
      end
    end
  end

  def run_action(:check, path) do
    info("[#{ts()}] checking #{path}")

    paths =
      if File.dir?(path) do
        Path.wildcard(Path.join(path, "**/*.cure"))
      else
        [path]
      end

    Enum.each(paths, fn p ->
      case File.read(p) do
        {:ok, src} ->
          with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(src, file: p, emit_events: false),
               {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: p, emit_events: false),
               {:ok, _env} <- Cure.Elab.Program.check_ast(ast) do
            info("  #{p}: OK")
          else
            {:error, reason} ->
              emit_error(reason, p, src)
          end

        {:error, reason} ->
          emit_diagnostic(Cure.Diagnostic.Operational.file_read(p, reason))
      end
    end)
  end

  def run_action(:test, _path) do
    info("[#{ts()}] running tests")
    System.cmd("mix", ["test", "--no-deps-check"], into: IO.stream(:stdio, :line))
  end

  def run_action(other, _path) do
    diagnostic = Cure.Diagnostic.Operational.unknown_watch_action(other)
    emit_diagnostic(diagnostic)
  end

  # -- Helpers -----------------------------------------------------------------

  defp ts do
    {_date, time} = :erlang.localtime()

    time
    |> Tuple.to_list()
    |> Enum.map_join(":", fn n -> n |> Integer.to_string() |> String.pad_leading(2, "0") end)
  end

  defp info(msg), do: IO.puts(msg)

  defp emit_error(reason, file, source) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)
    emit_diagnostic(diagnostic, registry)
  end

  defp read_source(path) do
    case File.read(path) do
      {:ok, source} -> source
      {:error, _reason} -> ""
    end
  end

  defp emit_diagnostic(diagnostic, registry \\ nil) do
    Cure.Diagnostic.Host.emit_diagnostic(diagnostic, output_device: :stderr, registry: registry)
  end
end
