defmodule Cure.Compiler.ModuleFragments do
  @moduledoc """
  Shared policy for source files that contribute to one canonical Cure module.

  A fragment is deliberately opt-in.  Ordinary duplicate module declarations
  remain an error; only a source carrying the exact `# cure:fragment` marker may
  participate in a same-module compilation unit.  The marker is a comment so
  fragment files remain valid Cure sources when inspected or compiled by tools
  that do not know about the grouping pass.
  """

  @marker "# cure:fragment"

  @spec marked?(String.t()) :: boolean()
  def marked?(source) when is_binary(source) do
    source
    |> String.split(["\n", "\r\n"], trim: false)
    |> Enum.any?(fn line -> String.trim(line) == @marker end)
  end

  def marked?(_source), do: false

  @doc "Return the deterministic ordered source paths represented by an entry."
  @spec source_paths(struct()) :: [Path.t()]
  def source_paths(%{source_path: source_path, source_paths: source_paths})
      when is_binary(source_path) and is_list(source_paths) do
    [source_path | source_paths]
    |> Enum.uniq()
    |> Enum.sort()
  end

  def source_paths(%{source_path: source_path}) when is_binary(source_path), do: [source_path]

  @doc "Build a stable source hash from the already-read fragment hashes."
  @spec aggregate_hash([struct()]) :: binary()
  def aggregate_hash(entries) when is_list(entries) do
    bytes =
      entries
      |> Enum.sort_by(& &1.source_path)
      |> Enum.map(fn entry -> entry.source_hash end)
      |> IO.iodata_to_binary()

    :crypto.hash(:sha256, bytes)
  end

  @spec marker() :: String.t()
  def marker, do: @marker
end
