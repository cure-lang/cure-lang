defmodule Cure.Compiler.Artifacts.Result do
  @moduledoc "Structured result returned by the unified artifact sweep."

  @enforce_keys [:workspace_key, :input_snapshot, :artifact_digest, :artifact_root, :manifest_path]
  defstruct workspace_key: nil,
            pipeline: :default,
            input_snapshot: nil,
            artifact_digest: nil,
            artifact_root: nil,
            reused: [],
            rebuilt: %{},
            removed: %{},
            manifest_path: nil,
            verification: :cached,
            hashes_computed: 0,
            hashes_reused: 0,
            errors: [],
            warnings: %{},
            cycles: []

  @type t :: %__MODULE__{
          workspace_key: binary(),
          pipeline: :default | :canonical,
          input_snapshot: binary(),
          artifact_digest: binary(),
          artifact_root: Path.t(),
          reused: [String.t()],
          rebuilt: map(),
          removed: map(),
          manifest_path: Path.t(),
          verification: :cached | :full,
          hashes_computed: non_neg_integer(),
          hashes_reused: non_neg_integer(),
          errors: list(),
          warnings: map(),
          cycles: list()
        }
end
