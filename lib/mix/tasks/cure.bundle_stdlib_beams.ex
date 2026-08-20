defmodule Mix.Tasks.Cure.BundleStdlibBeams do
  @moduledoc """
  Compile the foundational stdlib and embedded Regex package into
  `priv/ebin/Cure.Std.*.beam`.

  Companion to `Mix.Tasks.Cure.BundleStdlib`, which stages stdlib
  *sources* into `priv/std/`. Host applications that embed Cure (most
  notably the browser REPL inside `:cure_site`) need not just the
  sources but also the compiled stdlib BEAMs reachable at runtime --
  `Std.List.map` lowers to `:'Cure.Std.List':map/...` in codegen, and
  that BEAM has to be loadable or every call raises `:undef`.

  Historically `mix cure.compile_stdlib` wrote the BEAMs to
  `_build/cure/ebin`, a build-time artefact that is not part of an OTP
  release. Staging the BEAMs under `priv/ebin/` instead gives us the
  same guarantees as `priv/std/`:

    * Mix propagates `priv/` into every dep build (`_build/<env>/lib/cure/priv/`).
    * `mix release` bundles `priv/` into the release tarball.
    * `:code.priv_dir(:cure)` resolves to the staged location at runtime.

  ## Integrity

  Bundling uses the same content-addressed artifact sweep as development
  compilation. The destination includes its manifest and is accepted only as a
  complete verified generation; mtimes and filename presence are never
  freshness evidence.

  ## No-op paths

  Leaves the tree untouched when `lib/std/` is missing (hex-packaged
  consumers whose `:files` strips the sources, tests that stub the
  project layout, etc.) and when `Cure.Compiler` is not yet available
  at the moment the task runs (very first dep compile). The caller
  that wired this into a `compile` alias is responsible for ordering
  it **after** the regular `compile` step so `Cure.Compiler` has been
  built.

  Wired into Cure's own `compile` alias in `mix.exs`, so end users do
  not need to invoke it explicitly.
  """

  use Mix.Task

  @shortdoc "Compile Cure stdlib sources into priv/ebin/"

  @source_dir Path.join(["lib", "std"])

  @impl Mix.Task
  def run(_args) do
    # `Cure.Compiler` emits pipeline events unconditionally (see
    # `Cure.Compiler.Lexer.maybe_emit_event/2`), so the
    # `Cure.Pipeline.Events.Registry` has to be running for any
    # compilation to succeed. Starting `:cure` as an OTP application
    # brings the registry up via `Cure.Application`. We call it even
    # when `compiler_available?/0` is false below; Mix handles the
    # "app not loaded yet" case gracefully.
    _ = ensure_cure_application_started()

    result =
      case Cure.Compiler.Artifacts.copy_verified_set(
             "_build/cure/ebin",
             default_destination()
           ) do
        {:ok, _generation_root} -> {:ok, %{compiled: 0, skipped: 0, errors: 0}}
        {:error, _reason} -> bundle(@source_dir, default_destination())
      end

    case result do
      {:ok, %{errors: 0}} -> :ok
      {:ok, %{errors: count}} -> Mix.raise("stdlib bundle failed with #{count} artifact errors")
      {:error, reason} -> Mix.raise("stdlib bundle failed: #{inspect(reason)}")
    end
  end

  defp ensure_cure_application_started do
    if Code.ensure_loaded?(Mix.Task) and function_exported?(Mix.Task, :run, 2) do
      try do
        Mix.Task.run("app.start", [])
      rescue
        _ -> :ok
      catch
        _, _ -> :ok
      end
    else
      Application.ensure_all_started(:cure)
    end
  end

  @doc """
  Default output directory for compiled stdlib BEAMs.

  Resolves to `<priv>/ebin` relative to Cure's mix project root. Exposed
  as a function so tests can stub the path without pulling in Mix.
  """
  @spec default_destination() :: String.t()
  def default_destination, do: Path.join(["priv", "ebin"])

  @doc false
  @spec bundle(String.t(), String.t()) ::
          {:ok, %{compiled: non_neg_integer(), skipped: non_neg_integer(), errors: non_neg_integer()}}
  def bundle(source_dir, dest_dir) do
    cond do
      not File.dir?(source_dir) ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      not compiler_available?() ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      true ->
        File.mkdir_p!(dest_dir)

        case Cure.Stdlib.Packages.compile(source_dir |> Path.join("*.cure") |> Path.wildcard(), dest_dir,
               compile_opts: [emit_events: false]
             ) do
          {:ok, result} ->
            {:ok,
             %{
               compiled: map_size(result.rebuilt),
               skipped: length(result.reused),
               errors: length(result.errors)
             }}

          {:error, {:artifact_sweep_failed, errors}} ->
            Enum.each(errors, fn {target, reason} ->
              if Code.ensure_loaded?(Mix) and function_exported?(Mix, :shell, 0) do
                Mix.shell().error(render_host_diagnostic(reason, source_path_for(target, source_dir)))
              end
            end)

            {:error, {:artifact_sweep_failed, errors}}

          {:error, reason} ->
            if Code.ensure_loaded?(Mix) and function_exported?(Mix, :shell, 0) do
              Mix.shell().error(render_host_diagnostic(reason, source_dir))
            end

            {:error, reason}
        end
    end
  end

  @doc false
  @spec compiler_available?() :: boolean()
  # The task is wired into a `compile` alias that runs *after* the
  # primary `compile` step, so by the time we get here the Cure
  # compiler should already be loaded. On the very first dep compile
  # however the task module can still be stale; guarding with a
  # function-exported check lets us degrade to a silent no-op instead
  # of crashing the entire compile.
  def compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)

    Cure.Diagnostic.Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  defp source_path_for(target, source_dir) do
    if is_binary(target) and File.regular?(target) do
      target
    else
      stem =
        target
        |> to_string()
        |> String.split(".")
        |> List.last()
        |> Macro.underscore()

      Enum.find(
        Path.wildcard(Path.join(source_dir, "*.cure")),
        source_dir,
        &(Path.basename(&1, ".cure") == stem)
      )
    end
  end
end
