defmodule Cure.Stdlib.Packages do
  @moduledoc false

  alias Cure.Compiler.Artifacts
  alias Cure.Compiler.Artifacts.Result
  alias Cure.Compiler.Artifacts.Writer

  @regex_source_dir Path.expand("../../std_deps/regex", __DIR__)

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

  @doc "Compile foundational stdlib sources, then the embedded Regex package."
  @spec compile([Path.t()], Path.t(), keyword()) ::
          {:ok, Result.t()} | {:error, term()}
  def compile(foundational_sources, output_dir, opts \\ []) do
    regex_sources = regex_sources()

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
      stage_root = Path.join(output_dir <> ".packages", "regex")
      foundation_root = Path.join(stage_root, "foundation")
      regex_root = Path.join(stage_root, "package")
      merged_root = Path.join(stage_root, "merged")
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
    end
  end
end
