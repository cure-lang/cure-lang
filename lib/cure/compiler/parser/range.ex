defmodule Cure.Compiler.Parser.Range do
  @moduledoc "Token-owned half-open source range primitives for parser productions."

  alias Cure.Compiler.Token
  alias Cure.Diagnostic.Span

  @spec mark(Token.t() | Span.t()) :: {:ok, Span.t()} | {:error, :missing_span}
  def mark(%Token{span: %Span{} = span}), do: {:ok, span}
  def mark(%Span{} = span), do: {:ok, span}
  def mark(_), do: {:error, :missing_span}

  @spec through(Token.t() | Span.t(), Token.t() | Span.t()) ::
          {:ok, Span.t()} | {:error, :missing_span | :different_source}
  def through(first, last), do: combine(first, last)

  @spec between(Token.t() | Span.t(), Token.t() | Span.t()) ::
          {:ok, Span.t()} | {:error, :missing_span | :different_source}
  def between(first, last), do: combine(first, last)

  @spec zero_at(Token.t() | Span.t()) :: {:ok, Span.t()} | {:error, :missing_span}
  def zero_at(value) do
    with {:ok, %Span{} = span} <- mark(value) do
      {:ok,
       %Span{
         span
         | end_byte: span.start_byte,
           end_line: span.start_line,
           end_column: span.start_column
       }}
    end
  end

  defp combine(first, last) do
    with {:ok, %Span{} = left} <- mark(first),
         {:ok, %Span{} = right} <- mark(last),
         :ok <- same_source(left, right) do
      start = if left.start_byte <= right.start_byte, do: left, else: right
      ending = if left.end_byte >= right.end_byte, do: left, else: right

      {:ok,
       %Span{
         start
         | end_byte: ending.end_byte,
           end_line: ending.end_line,
           end_column: ending.end_column
       }}
    end
  end

  defp same_source(%Span{source_id: source}, %Span{source_id: source}), do: :ok
  defp same_source(_left, _right), do: {:error, :different_source}
end
