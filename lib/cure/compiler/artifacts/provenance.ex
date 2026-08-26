defmodule Cure.Compiler.Artifacts.Provenance do
  @moduledoc "Reads the provenance embedded in a Cure-generated BEAM."

  @spec read(Path.t()) :: {:ok, map()} | {:error, term()}
  def read(path) do
    with {:ok, artifact} <-
           Cure.Compiler.Artifacts.record(Path.basename(path), Path.dirname(path)),
         provenance when is_map(provenance) <- artifact.provenance do
      {:ok, provenance}
    else
      nil -> {:error, :provenance_missing}
      {:error, _} = error -> error
    end
  end
end
