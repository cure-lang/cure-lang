defmodule Cure.Compiler.ModulePipeline.Selection do
  @moduledoc false

  @type t :: :canonical

  @spec normalize(keyword()) :: {:ok, t()} | {:error, {:invalid_module_pipeline, term()}}
  def normalize(opts) when is_list(opts) do
    case Keyword.get(opts, :module_pipeline) do
      nil -> {:ok, :canonical}
      :canonical -> {:ok, :canonical}
      invalid -> {:error, {:invalid_module_pipeline, invalid}}
    end
  end
end
