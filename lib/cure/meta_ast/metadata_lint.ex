defmodule Cure.MetaAST.MetadataLint do
  @moduledoc """
  Finds exact MetaAST metadata-list patterns in quoted Elixir source.

  Parser construction is deliberately not reported: only terms reached while
  walking a function/case clause pattern are considered semantic patterns.
  """

  @type site :: %{file: String.t(), line: pos_integer(), node: atom(), pattern: Macro.t()}

  @legacy_source_keys [
    :construct_span,
    :span,
    :name_span,
    :callee_span,
    :operator_span,
    :operand_spans,
    :argument_spans,
    :arg_label_spans,
    :annotation_span,
    :body_span,
    :condition_span,
    :then_span,
    :else_span,
    :pattern_span,
    :guard_span,
    :branch_spans,
    :field_spans,
    :opener_span,
    :closer_span
  ]

  @spec scan([Path.t()]) :: [site()]
  def scan(paths) when is_list(paths), do: Enum.flat_map(paths, &scan_file/1)

  @spec scan_source(String.t(), String.t()) :: [site()]
  def scan_source(source, file \\ "nofile") when is_binary(source) and is_binary(file) do
    case Code.string_to_quoted(source, file: file) do
      {:ok, quoted} -> walk(quoted, false, file)
      {:error, _} -> []
    end
  end

  @spec validate([Path.t()]) :: :ok | {:error, {:exact_metadata_patterns, [site()]}}
  def validate(paths) when is_list(paths) do
    case scan(paths) do
      [] -> :ok
      sites -> {:error, {:exact_metadata_patterns, sites}}
    end
  end

  defp scan_file(file) do
    case File.read(file) do
      {:ok, source} -> scan_source(source, file)
      {:error, _} -> []
    end
  end

  defp walk({kind, _meta, [{name, name_meta, args}, body]}, _pattern?, file)
       when kind in [:def, :defp, :defmacro, :defmacrop] and is_list(args) do
    walk(args, true, file) ++ walk({name, name_meta, args}, false, file) ++ walk(body, false, file)
  end

  defp walk({:fn, _meta, clauses}, _pattern?, file), do: walk_clauses(clauses, file)

  defp walk({:->, _meta, [patterns, body]}, _pattern?, file),
    do: walk(patterns, true, file) ++ walk(body, false, file)

  defp walk({:{}, meta, [node, metadata, _children]} = quoted, true, file)
       when is_atom(node) and is_list(meta) do
    if keyword_metadata_literal?(metadata) do
      site = %{file: file, line: Keyword.get(meta, :line, 0), node: node, pattern: quoted}

      if legacy_metadata_literal?(metadata) do
        [Map.put(site, :legacy_source_keys, legacy_metadata_keys(metadata))]
      else
        [site]
      end
    else
      walk(metadata, true, file)
    end
  end

  defp walk({kind, meta, args}, pattern?, file) when is_tuple({kind, meta, args}) and is_list(args) do
    walk(meta, pattern?, file) ++ Enum.flat_map(args, &walk(&1, pattern?, file))
  end

  defp walk(list, pattern?, file) when is_list(list),
    do: Enum.flat_map(list, &walk(&1, pattern?, file))

  defp walk(tuple, pattern?, file) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&walk(&1, pattern?, file))

  defp walk(_other, _pattern?, _file), do: []

  defp walk_clauses(clauses, file), do: Enum.flat_map(clauses, &walk(&1, false, file))

  defp keyword_metadata_literal?(metadata) when is_list(metadata) do
    Enum.all?(metadata, &match?({key, _} when is_atom(key), &1))
  end

  defp keyword_metadata_literal?(_), do: false

  defp legacy_metadata_literal?(metadata),
    do: Enum.any?(metadata, fn {key, _value} -> key in @legacy_source_keys end)

  defp legacy_metadata_keys(metadata),
    do: metadata |> Keyword.keys() |> Enum.filter(&(&1 in @legacy_source_keys))
end
