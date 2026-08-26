defmodule Cure.Compiler.Parser.RangeTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Parser.Range
  alias Cure.Compiler.{Lexer, Token}
  alias Cure.Diagnostic.Span

  test "marks, spans through delimiters, and preserves multiline unicode coordinates" do
    first = token("α", 1, 1, 0, 2, 1, 3)
    last = token("]", 2, 3, 5, 6, 2, 4)

    assert {:ok, marked} = Range.mark(first)
    assert marked.start_byte == 0
    assert marked.end_byte == 2

    assert {:ok, range} = Range.through(first, last)
    assert range.start_byte == 0
    assert range.end_byte == 6
    assert range.end_line == 2
    assert range.end_column == 4
  end

  test "between is half-open and zero_at creates an honest insertion range" do
    first = token("(", 3, 4, 10, 11, 3, 5)
    last = token(")", 3, 7, 14, 15, 3, 8)

    assert {:ok, range} = Range.between(first, last)
    assert range.start_byte == 10 and range.end_byte == 15

    assert {:ok, insertion} = Range.zero_at(last)
    assert insertion.start_byte == 14
    assert insertion.end_byte == 14
    assert insertion.start_line == 3
    assert insertion.end_line == 3
    assert insertion.start_column == 7
    assert insertion.end_column == 7
  end

  test "never merges source identities and rejects missing token spans" do
    left = token("(", 1, 1, 0, 1, 1, 2)
    right = %{token(")", 1, 2, 1, 2, 1, 3) | span: span("other", 1, 2, 1, 2, 1, 3)}

    assert {:error, :different_source} = Range.through(left, right)
    assert {:error, :missing_span} = Range.mark(Token.new(:eof, nil, 1, 1))
  end

  test "real layout and EOF tokens provide honest insertion positions" do
    source = "mod Omega\n  fn identity() -> String = \"Ω\"\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "unicode_layout.cure", emit_events: false)

    newline = Enum.find(tokens, &(&1.type == :newline))
    indent = Enum.find(tokens, &(&1.type == :indent))
    dedent = Enum.find(tokens, &(&1.type == :dedent))
    eof = List.last(tokens)

    assert newline.span.end_byte > newline.span.start_byte

    for token <- [indent, dedent, eof] do
      assert {:ok, marked} = Range.mark(token)
      assert marked.start_byte == marked.end_byte
      assert {:ok, insertion} = Range.zero_at(token)
      assert insertion.start_byte == insertion.end_byte
      assert insertion.start_line == insertion.end_line
      assert insertion.start_column == insertion.end_column
    end

    assert eof.type == :eof
    assert eof.span.start_byte == byte_size(source)
    assert {eof.span.start_line, eof.span.start_column} == {3, 1}
  end

  test "unicode token columns and bytes remain distinct and composable" do
    source = "\"α\" + \"β\""
    assert {:ok, tokens} = Lexer.tokenize(source, file: "unicode.cure", emit_events: false)
    [alpha, plus, beta | _layout] = tokens

    assert {alpha.span.start_byte, alpha.span.end_byte, alpha.span.start_column, alpha.span.end_column} ==
             {0, 4, 1, 4}

    assert {beta.span.start_byte, beta.span.end_byte, beta.span.start_column, beta.span.end_column} ==
             {7, 11, 7, 10}

    assert {:ok, whole} = Range.through(alpha, beta)
    assert {whole.start_byte, whole.end_byte, whole.start_column, whole.end_column} == {0, 11, 1, 10}
    assert plus.span.start_byte == 5
  end

  defp token(value, line, column, start_byte, end_byte, end_line, end_column) do
    %Token{
      type: :test,
      value: value,
      line: line,
      col: column,
      span: span("demo.cure", line, column, start_byte, end_byte, end_line, end_column)
    }
  end

  defp span(source, line, column, start_byte, end_byte, end_line, end_column) do
    %Span{
      source_id: source,
      path: source,
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: line,
      start_column: column,
      end_line: end_line,
      end_column: end_column
    }
  end
end
