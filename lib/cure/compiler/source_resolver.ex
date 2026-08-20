defmodule Cure.Compiler.SourceResolver do
  @moduledoc """
  Resolve a Cure module NAME to a source PATH, on demand, by name only —
  the same resolution `Cure.Elab.Program.import_source_path/1` performs for
  `use` imports, reduced to the path (no elaboration-layer return tags).
  Used by the fixity resolver to walk the `use`-closure at parse time
  without a precomputed dependency graph. User-module matching uses the
  tolerant harvest (never a full parse), so it cannot recurse into fixity
  resolution.
  """

  alias Cure.Stdlib.Paths
  alias Cure.Compiler.Parser.FixityScan
  alias Cure.Compiler.Parser.FixityTable

  @spec module_path(String.t()) :: {:ok, Path.t()} | :not_found
  def module_path(name) when is_binary(name) do
    case indexed_path(name) do
      {:ok, _} = indexed ->
        indexed

      :not_found ->
        case stdlib_path(name) do
          {:ok, _} = ok -> ok
          :not_found -> user_path(name)
        end
    end
  end

  defp indexed_path(name) do
    case Process.get(:cure_module_index) do
      %Cure.Compiler.ModuleIndex{} = index ->
        case Cure.Compiler.ModuleIndex.fetch(index, name) do
          {:ok, entry} -> {:ok, entry.source_path}
          {:error, _} -> :not_found
        end

      _ ->
        :not_found
    end
  end

  defp stdlib_path("Std." <> _ = name) do
    dirs = Paths.all_source_dirs()

    case dirs do
      [] ->
        :not_found

      dirs ->
        segments = name |> String.split(".") |> tl()
        stems = [Enum.map_join(segments, "_", &Macro.underscore/1), String.downcase(Enum.join(segments, "_"))]

        dirs
        |> Enum.flat_map(fn dir -> Enum.map(stems, &Path.join(dir, &1 <> ".cure")) end)
        |> Enum.uniq()
        |> Enum.find(&File.exists?/1)
        |> case do
          nil -> :not_found
          path -> {:ok, path}
        end
    end
  end

  defp stdlib_path(_), do: :not_found

  defp user_path(name) do
    Process.get(:cure_source_roots, [])
    |> Enum.flat_map(fn root -> Path.wildcard(Path.join(root, "**/*.cure")) end)
    |> Enum.uniq()
    |> Enum.filter(fn path -> declared_module(path) == name end)
    |> case do
      [path] -> {:ok, path}
      _ -> :not_found
    end
  end

  defp declared_module(path) do
    case File.read(path) do
      {:ok, source} -> FixityScan.harvest_source(source, path, FixityTable.new()).module
      _ -> nil
    end
  end
end
