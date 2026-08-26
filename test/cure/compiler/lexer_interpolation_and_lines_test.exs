defmodule Cure.Compiler.LexerInterpolationAndLinesTest do
  @moduledoc ~S"""
  Three lexer defects, all about state that crossed a boundary and shouldn't have —
  or didn't and should have.

    * `paren_depth` was forced to 0 before each single-token step inside a `#{…}` and
      overwritten with the pre-step snapshot afterwards, so a `(` opened inside an
      interpolation never reached the counter `handle_newline/1` consults. Newline
      suppression inside parens — an invariant the lexer's own tests assert at top
      level — silently stopped holding inside interpolated strings.

    * the brace counter that finds a `#{…}`'s closing `}` only ever saw a bare `{`
      byte. `%{` is consumed whole by `lex_percent/1` as one `:map_open` token, so a map
      literal's opening brace never bumped the counter while its closing brace was still
      seen raw. `"#{ %{a: 1} }"` ended the interpolation one brace early and swallowed
      the rest of the string as literal text. A record literal's `Type{` uses a bare `{`,
      so only the map sigil was affected.

    * `advance/2` moves `pos` and `col`, never `line`. A string literal may span
      physical lines, and the catch-all that copies a raw byte into the literal used
      `advance/2` — so every token after a multi-line string reported a line number short
      by however many newlines the string held. Every other multi-line construct in the
      lexer bumps `line` and resets `col` when it crosses a newline.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Token}

  defp lex!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    tokens
  end

  describe "string interpolation" do
    test "a newline inside parens is suppressed, same as at top level" do
      # Cure source: "#{f(a,\nb)}" with a real newline between `a,` and `b)`.
      tokens = lex!("\"#" <> "{f(a,\nb)}\"")

      assert [%Token{type: :string_interpolation, value: [{:expr, expr}]}, _eof] = tokens

      assert Enum.map(expr, & &1.type) ==
               [:identifier, :lparen, :identifier, :comma, :identifier, :rparen]
    end

    test "a %{...} map literal is not truncated at its own closing brace" do
      tokens = lex!(~s("\#{ %{a: 1} }"))

      assert [%Token{type: :string_interpolation, value: [{:expr, expr}]}, _eof] = tokens
      assert Enum.map(expr, & &1.type) == [:map_open, :identifier, :colon, :integer, :rbrace]
    end

    test "a bare-brace record literal still closes correctly" do
      tokens = lex!(~s("\#{ Point{x: 1} }"))

      assert [%Token{type: :string_interpolation, value: [{:expr, expr}]}, _eof] = tokens
      assert Enum.map(expr, & &1.type) == [:identifier, :lbrace, :identifier, :colon, :integer, :rbrace]
    end

    test "an interpolation inside an open paren restores the enclosing paren depth" do
      # The `(` is open across the whole expression, so the trailing newline is suppressed.
      tokens = lex!("f(\"#" <> "{x}\",\ny)")

      refute Enum.any?(tokens, &(&1.type == :newline))
    end
  end

  describe "line tracking" do
    test "a newline embedded in a string literal advances the line counter" do
      # `"a<newline>b"` spans lines 1-2; `next` is on line 3.
      tokens = lex!("\"a\nb\"\nnext")

      assert %Token{value: "a\nb"} = Enum.find(tokens, &(&1.type == :string))
      assert %Token{line: 3} = Enum.find(tokens, &(&1.value == "next"))
    end

    test "an escaped \\n in a string literal does not advance the line counter" do
      # Two source bytes `\` `n`, not a newline — the string stays on line 1.
      tokens = lex!(~S("a\nb") <> "\nnext")

      assert %Token{value: "a\nb"} = Enum.find(tokens, &(&1.type == :string))
      assert %Token{line: 2} = Enum.find(tokens, &(&1.value == "next"))
    end
  end
end
