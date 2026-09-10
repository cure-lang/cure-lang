defmodule Cure.Compiler.LexerSpanHotpathTest do
  use ExUnit.Case, async: true

  test "scalar column conversion does not materialize a codepoint list" do
    source = File.read!("lib/cure/compiler/lexer.ex")

    assert source =~ "defp scalar_length(binary), do: String.length(binary)"
    assert source =~ "defp advance_coordinates"
    refute source =~ ":unicode.characters_to_list(binary, :utf8)"
  end

  test "Unicode token spans still use scalar columns" do
    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize("mod M\n  fn f() = \"é\"\n", emit_events: false)

    token = Enum.find(tokens, &(&1.type == :string))
    assert token.span.start_line == 2
    assert token.span.start_column == 12
    assert token.span.end_column == 15
  end
end
