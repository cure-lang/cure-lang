defmodule Cure.Compiler.TokenSpanTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Lexer

  test "authored token spans round-trip exact lexemes while layout tokens are zero-width" do
    source = "fn `run-now`(x) -> Int = \"hi \#{x}\" # note\nnext <-| ✉ done\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "spans.cure", preserve_comments: true, emit_events: false)

    authored =
      tokens
      |> Enum.reject(&(&1.type in [:indent, :dedent, :eof]))
      |> Enum.map(fn token ->
        {token.type, binary_part(source, token.span.start_byte, token.span.end_byte - token.span.start_byte)}
      end)

    assert authored == [
             {:keyword, "fn"},
             {:identifier, "`run-now`"},
             {:lparen, "("},
             {:identifier, "x"},
             {:rparen, ")"},
             {:arrow, "->"},
             {:identifier, "Int"},
             {:assign, "="},
             {:string_interpolation, "\"hi \#{x}\""},
             {:line_comment, "# note"},
             {:newline, "\n"},
             {:identifier, "next"},
             {:melquiades, "<-|"},
             {:melquiades, "✉"},
             {:identifier, "done"},
             {:newline, "\n"}
           ]

    assert Enum.all?(tokens, &match?(%Cure.Diagnostic.Span{}, &1.span))

    assert Enum.all?(
             Enum.filter(tokens, &(&1.type in [:indent, :dedent, :eof])),
             &(&1.span.start_byte == &1.span.end_byte)
           )

    done = Enum.find(tokens, &(&1.value == "done"))
    assert {done.line, done.col} == {2, 12}

    interpolation = Enum.find(tokens, &(&1.type == :string_interpolation))
    [{:expr, [nested_x]}] = Enum.filter(interpolation.value, &match?({:expr, _}, &1))
    assert slice(source, nested_x) == "x"
  end

  test "multiline strings and fenced comments retain consumed ranges" do
    source = "###\n docs\n###\n\"first\nsecond\"\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "multi.cure", emit_events: false)

    comment = Enum.find(tokens, &(&1.type == :doc_comment))
    string = Enum.find(tokens, &(&1.type == :string))

    assert slice(source, comment) == "###\n docs\n###"
    assert slice(source, string) == "\"first\nsecond\""
    assert {string.span.start_line, string.span.end_line} == {4, 5}
  end

  test "literal and delimiter families retain their authored spelling" do
    source = "0xCA_FE 0b10_01 12.5e-2 'x' '\\n' :ready? = /a+/iu <<x::8>> %[1] %{key: true} \"\#{\"quoted\"}\""
    assert {:ok, tokens} = Lexer.tokenize(source, file: "literals.cure", emit_events: false)

    slices =
      tokens
      |> Enum.reject(&(&1.type in [:indent, :dedent, :eof]))
      |> Enum.map(&slice(source, &1))

    assert slices == [
             "0xCA_FE",
             "0b10_01",
             "12.5e-2",
             "'x'",
             "'\\n'",
             ":ready?",
             "=",
             "/a+/iu",
             "<<",
             "x",
             "::",
             "8",
             ">>",
             "%[",
             "1",
             "]",
             "%{",
             "key",
             ":",
             "true",
             "}",
             "\"\#{\"quoted\"}\""
           ]
  end

  test "invalid UTF-8 remains a clean lexer rejection" do
    assert {:error, {:unexpected_character, 0xFF, 1, 1}} =
             Lexer.tokenize(<<0xFF>>, file: "bad.cure", emit_events: false)
  end

  defp slice(source, token),
    do: binary_part(source, token.span.start_byte, token.span.end_byte - token.span.start_byte)
end
