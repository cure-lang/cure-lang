defmodule Cure.Compiler.LexerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Lexer
  alias Cure.Compiler.Token

  # Helper to extract token types (excluding :eof)
  defp types(tokens), do: tokens |> Enum.reject(&(&1.type == :eof)) |> Enum.map(& &1.type)

  # Helper to extract token values (excluding :eof)
  defp values(tokens), do: tokens |> Enum.reject(&(&1.type == :eof)) |> Enum.map(& &1.value)

  defp lex!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    tokens
  end

  # ── Keywords ──────────────────────────────────────────────────────────

  describe "keywords" do
    test "all Cure keywords are recognized" do
      keywords = ~w(mod fn let type rec proto impl local use as
                    match if elif else then for do
                    in try catch finally throw return yield
                    spawn send receive after when where extern unsafe)

      for kw <- keywords do
        tokens = lex!(kw)
        assert [%Token{type: :keyword, value: val}, _eof] = tokens
        assert val == String.to_atom(kw)
      end
    end

    test "boolean literals are separate token types" do
      assert [%Token{type: :bool, value: true}, _] = lex!("true")
      assert [%Token{type: :bool, value: false}, _] = lex!("false")
    end

    test "nil literal" do
      assert [%Token{type: nil, value: nil}, _] = lex!("nil")
    end

    test "and, or, not are operator tokens" do
      assert [%Token{type: :and_op, value: :and}, _] = lex!("and")
      assert [%Token{type: :or_op, value: :or}, _] = lex!("or")
      assert [%Token{type: :not_op, value: :not}, _] = lex!("not")
    end

    test "identifiers that start like keywords but continue" do
      assert [%Token{type: :identifier, value: "function"}, _] = lex!("function")
      assert [%Token{type: :identifier, value: "letter"}, _] = lex!("letter")
      assert [%Token{type: :identifier, value: "modular"}, _] = lex!("modular")
    end
  end

  # ── Identifiers ──────────────────────────────────────────────────────

  describe "identifiers" do
    test "snake_case identifiers" do
      assert [%Token{type: :identifier, value: "my_var"}, _] = lex!("my_var")
    end

    test "PascalCase identifiers" do
      assert [%Token{type: :identifier, value: "MyModule"}, _] = lex!("MyModule")
    end

    test "underscore-prefixed identifiers" do
      assert [%Token{type: :identifier, value: "_unused"}, _] = lex!("_unused")
    end

    test "plain underscore (wildcard)" do
      assert [%Token{type: :identifier, value: "_"}, _] = lex!("_")
    end

    test "identifiers with digits" do
      assert [%Token{type: :identifier, value: "x1"}, _] = lex!("x1")
      assert [%Token{type: :identifier, value: "vec3d"}, _] = lex!("vec3d")
    end

    test "backticked identifiers can be keywords, spaced, unicode, or escaped" do
      assert [%Token{type: :identifier, value: "not"}, _] = lex!("`not`")
      assert [%Token{type: :identifier, value: "has spaces"}, _] = lex!("`has spaces`")
      assert [%Token{type: :identifier, value: "λ snow ☃"}, _] = lex!("`λ snow ☃`")
      assert [%Token{type: :identifier, value: "tick`name"}, _] = lex!("`tick\\`name`")
    end
  end

  # ── Number Literals ──────────────────────────────────────────────────

  describe "integers" do
    test "decimal integers" do
      assert [%Token{type: :integer, value: 42}, _] = lex!("42")
      assert [%Token{type: :integer, value: 0}, _] = lex!("0")
      assert [%Token{type: :integer, value: 1_000_000}, _] = lex!("1_000_000")
    end

    test "hex integers" do
      assert [%Token{type: :integer, value: 0xFF}, _] = lex!("0xFF")
      assert [%Token{type: :integer, value: 0xDEAD}, _] = lex!("0xDEAD")
    end

    test "binary integers" do
      assert [%Token{type: :integer, value: 0b1010}, _] = lex!("0b1010")
      assert [%Token{type: :integer, value: 0b1111_0000}, _] = lex!("0b1111_0000")
    end
  end

  describe "floats" do
    test "simple floats" do
      assert [%Token{type: :float, value: 3.14}, _] = lex!("3.14")
      assert [%Token{type: :float, value: 0.5}, _] = lex!("0.5")
    end

    test "scientific notation" do
      assert [%Token{type: :float, value: 1.0e-3}, _] = lex!("1.0e-3")
      assert [%Token{type: :float, value: 2.5e10}, _] = lex!("2.5e10")
    end

    test "integer with exponent becomes float" do
      tokens = lex!("1e3")
      assert [%Token{type: :float, value: v}, _] = tokens
      assert v == 1.0e3
    end
  end

  # A malformed numeric literal must return a clean {:error, reason} — never
  # crash the lexer with a raised ArgumentError from String.to_integer/2 or
  # String.to_float/1. These are reachable from any source the compiler reads.
  describe "malformed numeric literals return errors, not crashes" do
    test "an all-underscore radix literal (0x_/0b_) errors instead of raising" do
      assert {:error, {:invalid_hex_literal, _, _}} = Lexer.tokenize("0x_", emit_events: false)

      assert {:error, {:invalid_binary_literal, _, _}} =
               Lexer.tokenize("0b_", emit_events: false)
    end

    test "an out-of-range exponent (float overflow) errors instead of raising" do
      assert {:error, {:invalid_float_literal, _, _}} = Lexer.tokenize("1e400", emit_events: false)

      assert {:error, {:invalid_float_literal, _, _}} =
               Lexer.tokenize("1.5e400", emit_events: false)
    end

    test "a truncated exponent (no digits after e/e+/e-) errors instead of raising" do
      assert {:error, {:invalid_float_literal, _, _}} = Lexer.tokenize("1e", emit_events: false)
      assert {:error, {:invalid_float_literal, _, _}} = Lexer.tokenize("1e+", emit_events: false)
      assert {:error, {:invalid_float_literal, _, _}} = Lexer.tokenize("1e-", emit_events: false)
    end

    test "an over-long atom literal (>255 chars) errors instead of raising SystemLimitError" do
      # The BEAM caps atoms at 255 characters; String.to_atom/1 raises
      # SystemLimitError past that. A 255-char atom is fine; 256 must be a clean
      # error, not an uncaught crash escaping tokenize/2.
      assert {:ok, _} = Lexer.tokenize(":" <> String.duplicate("a", 255), emit_events: false)

      assert {:error, {:atom_too_long, _, _}} =
               Lexer.tokenize(":" <> String.duplicate("a", 256), emit_events: false)
    end
  end

  # ── String Literals ──────────────────────────────────────────────────

  describe "strings" do
    test "simple string" do
      assert [%Token{type: :string, value: "hello"}, _] = lex!(~s("hello"))
    end

    test "string with escape sequences" do
      tokens = lex!(~s("line1\\nline2"))
      assert [%Token{type: :string, value: "line1\nline2"}, _] = tokens
    end

    test "string with escaped quote" do
      tokens = lex!(~s("say \\"hi\\""))
      assert [%Token{type: :string, value: ~s(say "hi")}, _] = tokens
    end

    test "empty string" do
      assert [%Token{type: :string, value: ""}, _] = lex!(~s(""))
    end

    test "non-ASCII characters keep their UTF-8 bytes (regression: were double-encoded)" do
      # U+2019 RIGHT SINGLE QUOTATION MARK, UTF-8 <<0xE2, 0x80, 0x99>>.
      # The lexer read the source byte-by-byte and re-encoded each byte with
      # <<c::utf8>>, turning E2 80 99 into C3 A2 C2 80 C2 99 (mojibake).
      [%Token{type: :string, value: v1}, _] = lex!(~s("Dusty’s Place"))
      assert v1 == "Dusty’s Place"
      assert byte_size(v1) == byte_size("Dusty’s Place")

      # A two-byte char as well: U+00E9 é, UTF-8 <<0xC3, 0xA9>>.
      [%Token{type: :string, value: v2}, _] = lex!(~s("café"))
      assert v2 == "café"
      assert byte_size(v2) == 5
    end

    test "doc comments keep their UTF-8 bytes (same consume_while path)" do
      # The same byte-vs-utf8 bug also affected comment/doc-comment text,
      # which feeds `cure doc`.
      [%Token{type: :doc_comment, value: text} | _] = lex!("## café’s\n")
      assert text == "café’s"
    end

    test "unterminated string returns error" do
      assert {:error, {:unterminated_string, 1, 1}} = Lexer.tokenize(~s("hello), emit_events: false)
    end
  end

  describe "string interpolation" do
    test "simple interpolation" do
      tokens = lex!(~s("hello \#{name}"))
      assert [%Token{type: :string_interpolation, value: parts}, _] = tokens
      assert [{:string_part, "hello "}, {:expr, expr_tokens}] = parts
      assert [%Token{type: :identifier, value: "name"}] = expr_tokens
    end

    test "interpolation with expression" do
      tokens = lex!(~s("result: \#{x + 1}"))
      assert [%Token{type: :string_interpolation, value: parts}, _] = tokens
      assert [{:string_part, "result: "}, {:expr, expr_tokens}] = parts
      expr_types = Enum.map(expr_tokens, & &1.type)
      assert expr_types == [:identifier, :plus, :integer]
    end

    test "string with no interpolation despite hash" do
      tokens = lex!(~s("hello # world"))
      assert [%Token{type: :string, value: "hello # world"}, _] = tokens
    end
  end

  # ── Atom / Symbol Literals ──────────────────────────────────────────

  describe "atoms" do
    test "simple atoms" do
      assert [%Token{type: :atom, value: :ok}, _] = lex!(":ok")
      assert [%Token{type: :atom, value: :error}, _] = lex!(":error")
    end

    test "atom with underscore" do
      assert [%Token{type: :atom, value: :my_atom}, _] = lex!(":my_atom")
    end

    test "colon not followed by identifier is a colon token" do
      tokens = lex!("x: Int")
      assert [:identifier, :colon, :identifier] = types(tokens)
    end
  end

  # ── Char Literals ────────────────────────────────────────────────────

  describe "char literals" do
    test "simple char" do
      assert [%Token{type: :char, value: ?c}, _] = lex!("'c'")
    end

    test "escaped char" do
      assert [%Token{type: :char, value: ?\n}, _] = lex!("'\\n'")
      assert [%Token{type: :char, value: ?\r}, _] = lex!("'\\r'")
      assert [%Token{type: :char, value: ?\b}, _] = lex!("'\\b'")
      assert [%Token{type: :char, value: ?\f}, _] = lex!("'\\f'")
      assert [%Token{type: :char, value: ?\\}, _] = lex!("'\\\\'")
    end

    test "three quotes denote a literal single quote" do
      assert [%Token{type: :char, value: ?'}, _] = lex!(<<39, 39, 39>>)
    end

    test "both quote escape spellings remain valid" do
      assert [%Token{type: :char, value: ?'}, _] = lex!(<<39, 92, 39, 39>>)
      assert [%Token{type: :char, value: ?\\}, _] = lex!(<<39, 92, 92, 39>>)
    end
  end

  # ── Regex Literals ───────────────────────────────────────────────────

  describe "regex literals" do
    test "simple regex" do
      assert [%Token{type: :regex, value: {"[a-z]+", "i"}}, _] = lex!("/[a-z]+/i")
    end

    test "regex without flags" do
      assert [%Token{type: :regex, value: {"\\d+", ""}}, _] = lex!("/\\d+/")
    end

    test "accepts the complete Elixir modifier alphabet" do
      assert [%Token{type: :regex, value: {"foo", "imsxurfUE"}}, _] =
               lex!("/foo/imsxurfUE")
    end

    test "rejects an unknown modifier instead of lexing it as an identifier" do
      assert {:error, {:invalid_regex_modifier, ?z, 1, _col}} =
               Lexer.tokenize("/foo/z", emit_events: false)
    end

    test "bare slash regex is recognized where an expression starts" do
      assert [_assign, %Token{type: :regex, value: {"[A-z]*", ""}} | _] =
               lex!("= /[A-z]*/")
    end

    test "slash remains division after an expression" do
      assert [:identifier, :slash, :identifier] = types(lex!("left / right"))
    end
  end

  # ── Operators ────────────────────────────────────────────────────────

  describe "operators" do
    test "arithmetic operators" do
      assert [:plus, :minus, :star, :slash, :percent] =
               types(lex!("+ - * / %"))
    end

    test "comparison operators" do
      assert [:eq, :neq, :lt, :gt, :lte, :gte] =
               types(lex!("== != < > <= >="))
    end

    test "assignment operator" do
      assert [:assign] = types(lex!("="))
    end

    test "arrow and fat arrow" do
      assert [:arrow, :fat_arrow] = types(lex!("-> =>"))
    end

    test "pipe operator" do
      assert [:pipe] = types(lex!("|>"))
    end

    test "bar (cons / sum separator)" do
      assert [:bar] = types(lex!("|"))
    end

    test "dot and range operators" do
      assert [:dot] = types(lex!("."))
      assert [:range] = types(lex!(".."))
      assert [:range_inclusive] = types(lex!("..="))
    end

    test "string concatenation" do
      assert [:string_concat] = types(lex!("<>"))
    end

    test "binary open/close" do
      assert [:binary_open, :binary_close] = types(lex!("<< >>"))
    end
  end

  # ── Collection Sigils ────────────────────────────────────────────────

  describe "collection sigils" do
    test "tuple sigil %[" do
      tokens = lex!("%[1, 2]")
      assert [:tuple_open, :integer, :comma, :integer, :rbracket] = types(tokens)
    end

    test "map sigil %{" do
      tokens = lex!("%{a: 1}")
      assert [:map_open, :identifier, :colon, :integer, :rbrace] = types(tokens)
    end
  end

  # ── Brackets and Punctuation ────────────────────────────────────────

  describe "brackets and punctuation" do
    test "all bracket types" do
      tokens = lex!("( ) [ ] { }")
      assert [:lparen, :rparen, :lbracket, :rbracket, :lbrace, :rbrace] = types(tokens)
    end

    test "comma and semicolon" do
      assert [:comma, :semicolon] = types(lex!(", ;"))
    end

    test "at sign (decorator)" do
      assert [:at] = types(lex!("@"))
    end

    test "caret" do
      assert [:caret] = types(lex!("^"))
    end
  end

  # ── Comments ─────────────────────────────────────────────────────────

  describe "comments" do
    test "comments are skipped" do
      tokens = lex!("x # this is a comment\ny")
      assert ["x", "\n", "y"] = values(tokens)
    end

    test "comment-only line produces no tokens" do
      tokens = lex!("# just a comment")
      assert [:eof] = Enum.map(tokens, & &1.type)
    end
  end

  # ── Indentation ──────────────────────────────────────────────────────

  describe "indentation" do
    test "indent and dedent tokens are emitted" do
      source = "x\n  y\nz"
      tokens = lex!(source)
      token_types = types(tokens)
      assert :indent in token_types
      assert :dedent in token_types
    end

    test "multiple indent levels" do
      source = "a\n  b\n    c\nd"
      tokens = lex!(source)
      indents = tokens |> Enum.filter(&(&1.type == :indent)) |> length()
      dedents = tokens |> Enum.filter(&(&1.type == :dedent)) |> length()
      assert indents == 2
      assert dedents == 2
    end

    test "remaining indentation closed at EOF" do
      source = "a\n  b\n    c"
      tokens = lex!(source)
      dedents = tokens |> Enum.filter(&(&1.type == :dedent)) |> length()
      assert dedents == 2
    end

    test "tabs are rejected" do
      assert {:error, {:tab_not_allowed, _, _}} = Lexer.tokenize("\tx", emit_events: false)
    end
  end

  # ── Newline Suppression in Parens ───────────────────────────────────

  describe "newline suppression" do
    test "newlines inside parentheses are suppressed" do
      source = "f(\n  x,\n  y\n)"
      tokens = lex!(source)
      refute :newline in types(tokens)
    end
  end

  # ── Ordinary minus punctuation ────────────────────────────────────────

  describe "ordinary minus punctuation" do
    test "double minus is not a compiler-owned transition token" do
      tokens = lex!("--timer-->")
      token_types = types(tokens)
      assert Enum.count(token_types, &(&1 == :minus)) == 3
      assert :identifier in token_types
    end

    test "transition-shaped text uses ordinary expression tokens" do
      tokens = lex!("--increment when value < 100-->")
      token_types = types(tokens)
      assert Enum.count(token_types, &(&1 == :minus)) == 3
      assert :keyword in token_types
    end
  end

  # ── Position Tracking ───────────────────────────────────────────────

  describe "position tracking" do
    test "first token starts at line 1, col 1" do
      [token | _] = lex!("hello")
      assert token.line == 1
      assert token.col == 1
    end

    test "tokens on second line have correct line number" do
      tokens = lex!("a\nb")
      b = Enum.find(tokens, &(&1.value == "b"))
      assert b.line == 2
    end
  end

  # ── Complete Expression ──────────────────────────────────────────────

  describe "complete expressions" do
    test "function definition signature" do
      source = "fn add(x: Int, y: Int) -> Int = x + y"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      token_types = types(tokens)

      # fn
      assert :keyword in token_types
      # add, x, y, Int
      assert :identifier in token_types
      assert :lparen in token_types
      assert :rparen in token_types
      assert :colon in token_types
      # ->
      assert :arrow in token_types
      # =
      assert :assign in token_types
      assert :plus in token_types
    end

    test "list with cons" do
      tokens = lex!("[head | tail]")
      assert [:lbracket, :identifier, :bar, :identifier, :rbracket] = types(tokens)
    end

    test "pipe chain" do
      tokens = lex!("x |> f |> g")
      assert [:identifier, :pipe, :identifier, :pipe, :identifier] = types(tokens)
    end
  end

  describe "hole spans" do
    test "?_ is the anonymous hole and does not disturb predicate identifiers" do
      assert [%Token{type: :hole, value: "_"}, _eof] = lex!("?_")

      assert [%Token{type: :identifier, value: "is_empty?"}, %Token{type: :identifier, value: "foo"}, _eof] =
               lex!("is_empty? foo")
    end

    test "the obsolete ?? anonymous spelling is a targeted lexer error" do
      assert {:error, {:obsolete_anonymous_hole, 1, 1}} = Lexer.tokenize("??", emit_events: false)
    end

    test "a generated triple-question hole owns one token before a following declaration" do
      source = "mod M\n  fn bad() -> Int = ???\nend\n"
      tokens = lex!(source)

      assert [%Token{type: :hole, value: "?", span: span}] =
               Enum.filter(tokens, &(&1.type == :hole))

      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == "???"
      assert {span.start_line, span.start_column, span.end_line, span.end_column} == {2, 21, 2, 24}

      assert %Token{type: :keyword, value: :end, span: end_span} =
               Enum.find(tokens, &(&1.type == :keyword and &1.value == :end))

      assert {end_span.start_line, end_span.start_column} == {3, 1}
    end

    test "a generated triple-question hole at EOF retains the whole spelling" do
      source = "fn bad() -> Int = ???"
      tokens = lex!(source)

      assert %Token{type: :hole, span: span} = Enum.find(tokens, &(&1.type == :hole))
      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == "???"
      assert span.end_byte == byte_size(source)
    end
  end

  # ── Pipeline Events ──────────────────────────────────────────────────

  describe "pipeline events" do
    test "lex_complete event is emitted on success" do
      Cure.Pipeline.Events.subscribe(:lexer, :lex_complete)
      Lexer.tokenize("42", emit_events: true)

      assert_receive {Cure.Pipeline.Events, :lexer, :lex_complete, tokens, _meta}
      assert is_list(tokens)
    end

    test "token events carry the same exact spans as the completed token stream" do
      Cure.Pipeline.Events.subscribe(:lexer, :token_produced)
      Cure.Pipeline.Events.subscribe(:lexer, :lex_complete)

      assert {:ok, returned} = Lexer.tokenize("fn value() = 1", file: "events.cure")

      produced =
        Enum.map(returned, fn expected ->
          assert_receive {Cure.Pipeline.Events, :lexer, :token_produced, token, %{file: "events.cure"}}
          assert token == expected
          assert %Cure.Diagnostic.Span{} = token.span
          token
        end)

      assert_receive {Cure.Pipeline.Events, :lexer, :lex_complete, completed, %{file: "events.cure"}}
      assert produced == completed
    end

    test "error event is emitted on failure" do
      Cure.Pipeline.Events.subscribe(:lexer, :error)
      Lexer.tokenize("\t", emit_events: true)

      assert_receive {Cure.Pipeline.Events, :lexer, :error, {:tab_not_allowed, _, _}, _meta}
    end
  end
end
