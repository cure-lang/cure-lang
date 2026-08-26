defmodule Cure.Compiler.Token do
  @moduledoc """
  Token representation for the Cure lexer.

  Every authored token carries an exact half-open UTF-8 span. `line` and `col`
  remain as migration projections for parser consumers.
  """

  @type t :: %__MODULE__{
          type: atom(),
          value: term(),
          line: pos_integer(),
          col: pos_integer(),
          lexeme: binary() | nil,
          span: Cure.Diagnostic.Span.t() | nil
        }

  @enforce_keys [:type, :value, :line, :col]
  defstruct [:type, :value, :line, :col, :lexeme, :span]

  @doc "Create a new token."
  @spec new(atom(), term(), pos_integer(), pos_integer()) :: t()
  def new(type, value, line, col) do
    %__MODULE__{type: type, value: value, line: line, col: col}
  end

  @doc "Attach an authoritative source span and derive legacy coordinates from it."
  @spec with_span(t(), Cure.Diagnostic.Span.t()) :: t()
  def with_span(%__MODULE__{} = token, %Cure.Diagnostic.Span{} = span) do
    %{token | span: span, line: span.start_line, col: span.start_column}
  end
end
