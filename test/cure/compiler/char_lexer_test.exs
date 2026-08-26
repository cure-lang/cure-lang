defmodule Cure.Compiler.CharLexerTest do
  # `lex_char` must decode a full UTF-8 codepoint, not a single raw byte, so a
  # multi-byte character literal like '😀' becomes its Unicode codepoint (128512),
  # not a lex error. ASCII behavior is unchanged.
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Token}

  defp char_tokens(src) do
    {:ok, toks} = Lexer.tokenize(src)
    for %Token{type: :char} = t <- toks, do: t.value
  end

  test "an ASCII char literal still lexes to its byte/codepoint" do
    assert [97] = char_tokens("fn f() = 'a'")
  end

  test "a multi-byte emoji char literal lexes to its Unicode codepoint" do
    assert [128_512] = char_tokens("fn f() = '😀'")
  end

  test "a 2-byte char (é, U+00E9) lexes to its codepoint, not a raw byte" do
    assert [233] = char_tokens("fn f() = 'é'")
  end

  test "a recognized escape is unaffected" do
    assert [?\n] = char_tokens(~S"fn f() = '\n'")
  end

  test "an unrecognized escape is a hard error, not a silently dropped backslash" do
    # Before the fix, an unknown escape fell through to `decode_char_at`, which read the byte
    # AFTER the backslash literally — silently yielding the codepoint for `r` (114)
    # instead of reporting an error. That corruption then round-tripped stably
    # as an ordinary character. Cure recognizes `\b \f \n \r \t \\ \' \0`; any
    # other escape must error rather than miscompile.
    assert {:error, {:invalid_char_escape, _, _}} = Lexer.tokenize(~S"fn f() = '\z'", emit_events: false)
  end

  test "backspace and form-feed escapes decode to their control code points" do
    assert [?\b, ?\f] = char_tokens(~S"fn backspace() = '\b'
fn form_feed() = '\f'")
  end

  test "a truncated multi-byte tail at EOF is an unterminated-char error, not a crash" do
    # Opening quote then a lone UTF-8 lead byte, no closing quote.
    assert {:error, {:unterminated_char, _, _}} = Lexer.tokenize(<<"fn f() = '", 0xF0>>)
  end

  test "a backslash immediately at end-of-source is an unterminated-char error, not a crash" do
    # Regression guard, not a newly-red case: today, `peek(state)` returning nil
    # right after the backslash falls through to the escape-fallback catch-all
    # harmlessly (it binds the loop variable to nil and just advances). The
    # multi-byte-decode fix below must preserve that — `decode_char_at` must not
    # call `:binary.at` past the end of source. This test already passes on the
    # unfixed lexer (same status as the ASCII/escape cases above); it exists to
    # catch a regression if the fix is implemented without the EOF guard.
    assert {:error, {:unterminated_char, _, _}} = Lexer.tokenize("fn f() = '\\", emit_events: false)
  end
end
