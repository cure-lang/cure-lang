defmodule Cure.Compiler.Artifacts.Manifest do
  @moduledoc "Manifest-v2 API for the artifact subsystem."

  defdelegate empty(workspace_key), to: Cure.Compiler.BuildManifest
  defdelegate read(root), to: Cure.Compiler.BuildManifest
  defdelegate load(root), to: Cure.Compiler.BuildManifest
  defdelegate save(manifest, root), to: Cure.Compiler.BuildManifest
  defdelegate seal(manifest), to: Cure.Compiler.BuildManifest
  defdelegate artifact_digest(manifest), to: Cure.Compiler.BuildManifest
  defdelegate valid_digest?(manifest), to: Cure.Compiler.BuildManifest
  defdelegate filename(), to: Cure.Compiler.BuildManifest
end
