defmodule Cure.Diagnostic.Registry.Catalog do
  @moduledoc "Compatibility delegates for the registry-owned diagnostic catalog."

  @spec entries() :: [{String.t(), String.t(), String.t()}]
  def entries, do: Cure.Diagnostic.Registry.catalog_entries()

  @spec explanation!(String.t()) :: String.t()
  def explanation!(code), do: Cure.Diagnostic.Registry.catalog_explanation!(code)
end
