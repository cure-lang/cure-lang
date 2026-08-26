defmodule Cure.LSP.Symbols do
  @moduledoc "Symbol extraction from Cure AST for LSP features."

  alias Cure.LSP.Positions
  alias Cure.MetaAST.Metadata

  @spec extract(tuple(), String.t() | nil, Positions.encoding()) :: [map()]
  def extract(ast, source \\ nil, encoding \\ :utf16) do
    case ast do
      {:container, meta, body} -> extract_generic_container(meta, body, source, encoding)
      {:lift_module, meta, _body} -> extract_lift_module(meta, source, encoding)
      {:block, _, children} -> Enum.flat_map(children, &extract(&1, source, encoding))
      _ -> []
    end
  end

  defp extract_lift_module(meta, source, encoding) when is_list(meta) do
    name = Keyword.get(meta, :module, "unnamed")
    behavior = Keyword.get(meta, :behaviour, :unknown)
    line = Keyword.get(meta, :line, 1)
    declarations = Keyword.get(meta, :declarations, [])
    callbacks = Keyword.get(meta, :callbacks, [])
    callback_symbols = Enum.map(callbacks, &callback_symbol(&1, line, source, encoding))

    [
      %{
        "name" => to_string(name),
        "kind" => 2,
        "range" => node_range(meta, line, source, encoding),
        "selectionRange" => node_selection(meta, line, source, encoding),
        "detail" => "lifted #{behavior}",
        "children" => callback_symbols ++ Enum.flat_map(declarations, &extract_body_item(&1, source, encoding))
      }
    ]
  end

  defp callback_symbol(%{name: name, arity: arity, line: line}, _default, source, encoding) do
    range = Positions.line_range(line, source, encoding)

    %{
      "name" => "callback #{name}/#{arity}",
      "kind" => 12,
      "detail" => "callback #{name}/#{arity}",
      "range" => range,
      "selectionRange" => range
    }
  end

  defp callback_symbol(%{name: name}, default, source, encoding),
    do: callback_symbol(%{name: name, arity: 0, line: default}, default, source, encoding)

  defp extract_generic_container(meta, body, source, encoding) do
    type = Keyword.get(meta, :container_type, :unknown)
    name = Keyword.get(meta, :name, "unnamed")
    line = Keyword.get(meta, :line, 1)
    kind = %{module: 2, protocol: 11, trait: 12, struct: 23}[type] || 2
    children = Enum.flat_map(body, &extract_body_item(&1, source, encoding))

    [
      %{
        "name" => name,
        "kind" => kind,
        "range" => node_range(meta, line, source, encoding),
        "selectionRange" => node_selection(meta, line, source, encoding),
        "detail" => to_string(type),
        "children" => children
      }
    ]
  end

  defp extract_body_item({:function_def, meta, _body}, source, encoding) do
    name = Keyword.get(meta, :name, "unknown")
    arity = Keyword.get(meta, :arity, 0)
    line = Keyword.get(meta, :line, 1)
    visibility = Keyword.get(meta, :visibility, :public)
    detail = if visibility == :private, do: "local fn #{name}/#{arity}", else: "fn #{name}/#{arity}"

    [
      %{
        "name" => "#{name}/#{arity}",
        "kind" => 12,
        "detail" => detail,
        "range" => node_range(meta, line, source, encoding),
        "selectionRange" => node_selection(meta, line, source, encoding)
      }
    ]
  end

  defp extract_body_item({:container, meta, body}, source, encoding),
    do: extract_generic_container(meta, body, source, encoding)

  defp extract_body_item({:type_annotation, meta, _children}, source, encoding) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)

    [
      %{
        "name" => name,
        "kind" => 26,
        "range" => node_range(meta, line, source, encoding),
        "selectionRange" => node_selection(meta, line, source, encoding)
      }
    ]
  end

  defp extract_body_item(_, _source, _encoding), do: []

  defp node_range(meta, line, source, encoding) do
    info = Metadata.source_info(meta)
    if info, do: Positions.range(info.whole, source, encoding), else: Positions.line_range(line, source, encoding)
  end

  defp node_selection(meta, line, source, encoding) do
    info = Metadata.source_info(meta)

    if info,
      do: Positions.range(info.name || info.whole, source, encoding),
      else: Positions.line_range(line, source, encoding)
  end
end
