defmodule Cure.MetaAST.SourceDecorator do
  @moduledoc false

  alias Cure.Diagnostic.Span
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @doc "Decorate every canonical surface node, including nodes nested in metadata values."
  def decorate(ast), do: walk(ast, 0) |> elem(0)

  defp walk({tag, meta, children}, index) when is_atom(tag) and is_list(meta) do
    {meta, index} =
      meta
      |> Enum.map_reduce(index, fn {key, value}, index ->
        {value, index} = walk(value, index)
        {{key, value}, index}
      end)

    {children, index} = walk(children, index)
    info = %SourceInfo{whole: sentinel(index), name: sentinel(index + 1)}
    {Metadata.put_source_info(meta, info) |> then(&{tag, &1, children}), index + 2}
  end

  defp walk(list, index) when is_list(list) do
    Enum.map_reduce(list, index, &walk/2)
  end

  defp walk(tuple, index) when is_tuple(tuple) and not is_struct(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.map_reduce(index, &walk/2)
    |> then(fn {items, index} -> {List.to_tuple(items), index} end)
  end

  defp walk(map, index) when is_map(map) and not is_struct(map) do
    {map, index} =
      Enum.reduce(map, {%{}, index}, fn {key, value}, {map, index} ->
        {key, index} = walk(key, index)
        {value, index} = walk(value, index)
        {Map.put(map, key, value), index}
      end)

    {map, index}
  end

  defp walk(value, index), do: {value, index}

  defp sentinel(index) do
    %Span{
      source_id: {:sentinel, index},
      path: "sentinel-#{index}.cure",
      start_byte: index,
      end_byte: index + 1,
      start_line: index + 1,
      start_column: 1,
      end_line: index + 1,
      end_column: 2
    }
  end
end
