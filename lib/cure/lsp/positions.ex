defmodule Cure.LSP.Positions do
  @moduledoc "Source-derived LSP ranges for AST and diagnostic spans."

  alias Cure.Diagnostic.{SourceRegistry, Span}

  @type encoding :: :utf8 | :utf16 | :utf32

  def range(%Span{} = span, source, encoding) when is_binary(source) do
    registry = SourceRegistry.new() |> SourceRegistry.register(span.source_id, source)

    with {:ok, start} <- SourceRegistry.lsp_position(registry, span, :start, encoding),
         {:ok, finish} <- SourceRegistry.lsp_position(registry, span, :end, encoding) do
      %{"start" => start, "end" => finish}
    else
      _ -> fallback_range(span)
    end
  end

  def range(%Span{} = span, _source, _encoding), do: fallback_range(span)
  def range(nil, source, encoding), do: line_range(1, source, encoding)

  def line_range(line, source, encoding) do
    line = max(line - 1, 0)
    text = if is_binary(source), do: Enum.at(String.split(source, "\n"), line), else: nil
    length = if is_binary(text), do: encoded_length(String.trim_trailing(text, "\r"), encoding), else: 0
    %{"start" => %{"line" => line, "character" => 0}, "end" => %{"line" => line, "character" => length}}
  end

  defp fallback_range(span) do
    %{
      "start" => %{"line" => max(span.start_line - 1, 0), "character" => max(span.start_column - 1, 0)},
      "end" => %{"line" => max(span.end_line - 1, 0), "character" => max(span.end_column - 1, 0)}
    }
  end

  defp encoded_length(text, :utf8), do: byte_size(text)

  defp encoded_length(text, :utf16),
    do: text |> :unicode.characters_to_binary(:utf8, {:utf16, :little}) |> byte_size() |> div(2)

  defp encoded_length(text, :utf32), do: String.length(text)
end
