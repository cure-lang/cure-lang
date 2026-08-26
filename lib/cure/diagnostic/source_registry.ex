defmodule Cure.Diagnostic.SourceRegistry do
  @moduledoc "Immutable source-buffer registry used to resolve diagnostic spans."

  alias Cure.Diagnostic.Span

  defstruct sources: %{}, paths: %{}
  @type t :: %__MODULE__{sources: %{term() => String.t()}, paths: %{term() => String.t() | nil}}

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @spec register(t(), term(), String.t(), String.t() | nil) :: t()
  def register(%__MODULE__{} = registry, source_id, source, path \\ nil) when is_binary(source) do
    %__MODULE__{
      registry
      | sources: Map.put(registry.sources, source_id, source),
        paths: Map.put(registry.paths, source_id, path)
    }
  end

  @spec fetch(t(), term()) :: {:ok, String.t()} | :error
  def fetch(%__MODULE__{sources: sources}, source_id), do: Map.fetch(sources, source_id)

  @spec span(t(), term(), non_neg_integer(), non_neg_integer()) :: {:ok, Span.t()} | {:error, term()}
  def span(%__MODULE__{} = registry, source_id, start_byte, end_byte)
      when is_integer(start_byte) and is_integer(end_byte) and start_byte >= 0 and end_byte >= start_byte do
    with {:ok, source} <- fetch(registry, source_id),
         true <- end_byte <= byte_size(source) do
      {start_line, start_column} = coordinates(source, start_byte)
      {end_line, end_column} = coordinates(source, end_byte)

      {:ok,
       Span.new(
         source_id: source_id,
         path: Map.get(registry.paths, source_id),
         start_byte: start_byte,
         end_byte: end_byte,
         start_line: start_line,
         start_column: start_column,
         end_line: end_line,
         end_column: end_column
       )}
    else
      :error -> {:error, :unknown_source}
      false -> {:error, :span_out_of_bounds}
    end
  end

  @doc "Build a span from Elixir-style one-based line and Unicode scalar columns."
  @spec span_at(t(), term(), pos_integer(), pos_integer(), non_neg_integer()) ::
          {:ok, Span.t()} | {:error, term()}
  def span_at(%__MODULE__{} = registry, source_id, line, column, length \\ 1)
      when line > 0 and column > 0 and length >= 0 do
    with {:ok, source} <- fetch(registry, source_id),
         {:ok, start_byte} <- byte_at(source, line, column),
         {:ok, end_byte} <- byte_at(source, line, column + length) do
      span(registry, source_id, start_byte, end_byte)
    end
  end

  @spec line(t(), Span.t(), pos_integer()) :: {:ok, String.t()} | :error
  def line(%__MODULE__{} = registry, %Span{source_id: source_id}, line_number) do
    with {:ok, source} <- fetch(registry, source_id),
         line when is_binary(line) <- Enum.at(String.split(source, "\n"), line_number - 1) do
      {:ok, String.trim_trailing(line, "\r")}
    else
      _ -> :error
    end
  end

  @doc "Convert a span endpoint to a zero-based position in the negotiated LSP encoding."
  @spec lsp_position(t(), Span.t(), :start | :end, :utf8 | :utf16 | :utf32) ::
          {:ok, map()} | {:error, term()}
  def lsp_position(%__MODULE__{} = registry, %Span{} = span, endpoint, encoding \\ :utf16)
      when endpoint in [:start, :end] and encoding in [:utf8, :utf16, :utf32] do
    byte = if endpoint == :start, do: span.start_byte, else: span.end_byte
    line = if endpoint == :start, do: span.start_line, else: span.end_line

    with {:ok, source} <- fetch(registry, span.source_id),
         true <- byte <= byte_size(source) do
      prefix = binary_part(source, 0, byte)
      line_prefix = prefix |> String.split("\n") |> List.last() |> lsp_line_text()
      {:ok, %{"line" => line - 1, "character" => encoded_length(line_prefix, encoding)}}
    else
      :error -> {:error, :unknown_source}
      false -> {:error, :span_out_of_bounds}
    end
  end

  defp encoded_length(text, :utf8), do: byte_size(text)

  defp encoded_length(text, :utf16) do
    text |> :unicode.characters_to_binary(:utf8, {:utf16, :little}) |> byte_size() |> div(2)
  end

  defp encoded_length(text, :utf32), do: String.length(text)

  # LSP positions are measured within the logical line. In a CRLF buffer the
  # carriage return belongs to the line terminator, not to the line's text.
  defp lsp_line_text(text), do: String.trim_trailing(text, "\r")

  # Columns are Unicode scalar columns. LSP's UTF-16 conversion belongs in its adapter.
  defp coordinates(source, byte) do
    prefix = binary_part(source, 0, byte)
    lines = String.split(prefix, "\n")
    {length(lines), String.length(List.last(lines) || "") + 1}
  end

  defp byte_at(source, wanted_line, wanted_column) do
    lines = String.split(source, "\n")

    case Enum.at(lines, wanted_line - 1) do
      nil ->
        {:error, :line_out_of_bounds}

      line ->
        prefix = line |> String.codepoints() |> Enum.take(wanted_column - 1) |> Enum.join()

        if String.length(prefix) == wanted_column - 1 do
          preceding = lines |> Enum.take(wanted_line - 1) |> Enum.map_join("", &(&1 <> "\n"))
          {:ok, byte_size(preceding) + byte_size(prefix)}
        else
          {:error, :column_out_of_bounds}
        end
    end
  end
end
