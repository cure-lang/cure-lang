defmodule Cure.Stdlib.Packages do
  @moduledoc false

  alias Cure.Compiler.Artifacts
  alias Cure.Compiler.Artifacts.Result
  alias Cure.Compiler.Artifacts.Writer

  @regex_source_dir Path.expand("../../std_deps/regex", __DIR__)

  # Persistent (not random-per-call) staging root for the two intermediate
  # sweeps the embedded-package path in `compile/3` needs: the foundational
  # `Std.*` sources and the embedded Regex package. Both are swept through
  # `Cure.Compiler.Artifacts.Sweep`, which decides what to rebuild by
  # diffing the incoming sources against whatever verified generation is
  # already published at its `:output_dir` (see
  # `Cure.Compiler.Artifacts.Sweep.canonical_prior_generation/3`). A
  # directory that is recreated under a fresh, randomly-named path on every
  # call is always empty, so that diff always finds nothing to reuse and
  # every stdlib module looks changed on every single compile, whether or
  # not any source actually was. Rooting these two sweeps at a stable path
  # instead means unrelated compiles (`mix compile`, `mix test`, the
  # runtime `Cure.Stdlib.Preload` repair path, ...) land on -- and can
  # reuse -- the same generation. `Cure.Compiler.Artifacts.Lock` protects
  # each sweep's `:output_dir` with a real OS-level (flock/lockf) lock, so
  # sharing this path across concurrent OS processes (e.g. parallel `mix
  # test` runs) is safe. It lives beside, not inside, whichever real
  # `output_dir` the caller passed in, so a plain listing of a published
  # ebin directory (or a Hex-packaged `priv/ebin`) never sees it.
  @embedded_stage_root Path.join(["_build", "cure", ".cure_stdlib_stage"])

  @doc "Return the embedded Regex package source directory."
  @spec regex_source_dir() :: Path.t()
  def regex_source_dir, do: @regex_source_dir

  @doc "Return the embedded Regex package sources in deterministic order."
  @spec regex_sources() :: [Path.t()]
  def regex_sources do
    @regex_source_dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.sort()
  end

  @doc """
  Compile foundational stdlib sources, then the embedded Regex package.

  `:embedded_packages` (default `true`) selects whether the embedded package
  stage runs at all. It is a real stage, not a detail: it sweeps every module
  under `lib/std_deps/regex` (proof-heavy dependent code) and merges the result
  with the foundation, which costs about two minutes cold. The
  `@embedded_stage_root` cache both sweeps publish into means a later call
  whose sources have not changed re-verifies the existing generation instead
  of recompiling it -- see `@embedded_stage_root` for why that distinction
  depends on where these two sweeps publish, not just on this stage existing.
  A caller sweeping a source set that is NOT the standard library — a fixture
  directory, a single module under test — gets no value from that stage while
  paying its full cold cost, and its reused/rebuilt counts then describe the
  embedded package instead of the caller's own sources. Such callers pass
  `embedded_packages: false` and get the plain foundation sweep.
  """
  @spec compile([Path.t()], Path.t(), keyword()) ::
          {:ok, Result.t()} | {:error, term()}
  def compile(foundational_sources, output_dir, opts \\ []) do
    {embedded_packages?, opts} = Keyword.pop(opts, :embedded_packages, true)
    regex_sources = if embedded_packages?, do: regex_sources(), else: []
    all_sources = foundational_sources ++ regex_sources

    case short_circuit_up_to_date(output_dir, all_sources, opts) do
      {:ok, %Result{} = result} ->
        {:ok, result}

      :miss ->
        if regex_sources == [] do
          Artifacts.sweep(
            Keyword.merge(
              [
                module_pipeline: :canonical,
                package: "stdlib",
                source_paths: foundational_sources,
                source_roots: [Path.dirname(List.first(foundational_sources) || "lib/std")],
                output_dir: output_dir,
                kind: :stdlib,
                repair: true
              ],
              opts
            )
          )
        else
          foundation_root = Path.join(@embedded_stage_root, "foundation")
          regex_root = Path.join(@embedded_stage_root, "package")

          # Unlike the two sweeps above, the merge step only copies
          # already-compiled, already-verified beams (see
          # `Artifacts.merge_verified_flat/3`) -- it performs no compilation --
          # so it has nothing to gain from persistent caching. Keeping it in a
          # fresh temp directory per call avoids adding a new concurrency
          # hazard: `merge_verified_flat/3` writes to `merged_root` directly,
          # without the OS-level lock that protects `foundation_root` and
          # `regex_root` (via `Artifacts.Sweep`) and `output_dir` (via
          # `Writer.copy_verified/2`).
          tmp_dir = Path.join(System.tmp_dir!(), "cure_stdlib_merge_#{System.unique_integer([:positive])}")
          merged_root = Path.join(tmp_dir, "merged")
          foundation_source_root = Path.dirname(List.first(foundational_sources) || "lib/std")

          foundation_opts =
            Keyword.merge(
              [
                module_pipeline: :canonical,
                package: "stdlib",
                source_paths: foundational_sources,
                source_roots: [foundation_source_root],
                output_dir: foundation_root,
                kind: :stdlib,
                repair: true
              ],
              opts
            )

          try do
            with {:ok, foundation} <- Artifacts.sweep(foundation_opts),
                 {:ok, package} <-
                   Artifacts.sweep(
                     Keyword.merge(
                       [
                         module_pipeline: :canonical,
                         package: "cure_regex",
                         package_exports: %{"cure_regex" => ["Std.Regex"]},
                         source_paths: regex_sources,
                         source_roots: [@regex_source_dir],
                         interface_roots: [foundation.artifact_root],
                         stdlib_roots: [],
                         output_dir: regex_root,
                         kind: :dependency,
                         repair: true
                       ],
                       opts
                     )
                   ),
                 _removed <- File.rm_rf!(merged_root),
                 {:ok, _merged} <-
                   Artifacts.merge_verified_flat([foundation.artifact_root, package.artifact_root], merged_root,
                     kind: :stdlib,
                     package_artifact_digests: %{"cure_regex" => package.artifact_digest},
                     package_exports: %{"cure_regex" => ["Std.Regex"]}
                   ),
                 {:ok, final_root} <- Writer.copy_verified(merged_root, output_dir),
                 {:ok, final_set} <- Artifacts.open_verified_set(final_root, verification: :full) do
              {:ok,
               %Result{
                 pipeline: :canonical,
                 workspace_key: final_set.workspace_key,
                 input_snapshot: final_set.input_snapshot,
                 artifact_digest: final_set.artifact_digest,
                 artifact_root: final_set.artifact_root,
                 reused: Enum.uniq(foundation.reused ++ package.reused) |> Enum.sort(),
                 rebuilt: Map.merge(foundation.rebuilt, package.rebuilt),
                 removed: Map.merge(foundation.removed, package.removed),
                 cycles: foundation.cycles ++ package.cycles,
                 verification: :full,
                 manifest_path: Path.join(final_set.artifact_root, Cure.Compiler.BuildManifest.filename())
               }}
            end
          after
            File.rm_rf!(tmp_dir)
          end
        end
    end
  end

  defp short_circuit_up_to_date(output_dir, all_sources, opts) do
    if Keyword.get(opts, :force, false) or not File.dir?(output_dir) do
      :miss
    else
      expected_kind = Keyword.get(opts, :kind, :stdlib)
      verification = Keyword.get(opts, :verification, :full)

      with {:ok, manifest} <- Artifacts.open_verified_set(output_dir, verification: verification),
           true <- manifest.kind == expected_kind,
           recorded_compiler <- get_in(manifest, [:context, :compiler_hash]),
           true <- recorded_compiler == Cure.Compiler.BuildManifest.toolchain_fingerprint(),
           sources <- all_sources |> Enum.map(&Path.expand/1) |> Enum.uniq(),
           true <- length(sources) == map_size(manifest.modules),
           {:ok, current_hashes} <- read_source_hashes(sources),
           manifest_hashes <- manifest.modules |> Map.values() |> Enum.map(&get_in(&1, [:source, :sha256])) |> Enum.sort(),
           true <- Enum.sort(current_hashes) == manifest_hashes do
        {:ok,
         %Result{
           pipeline: :canonical,
           workspace_key: manifest.workspace_key,
           input_snapshot: manifest.input_snapshot,
           artifact_digest: manifest.artifact_digest,
           artifact_root: manifest.artifact_root,
           reused: manifest.modules |> Map.keys() |> Enum.sort(),
           rebuilt: %{},
           removed: %{},
           cycles: [],
           verification: verification,
           manifest_path: Path.join(manifest.artifact_root, Cure.Compiler.BuildManifest.filename())
         }}
      else
        _ -> :miss
      end
    end
  end

  defp read_source_hashes(paths) do
    Enum.reduce_while(paths, {:ok, []}, fn path, {:ok, acc} ->
      case File.read(path) do
        {:ok, bytes} -> {:cont, {:ok, [:crypto.hash(:sha256, bytes) | acc]}}
        {:error, _reason} -> {:halt, :error}
      end
    end)
  end
end
