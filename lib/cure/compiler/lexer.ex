defmodule Cure.Compiler.Lexer do
  @moduledoc """
  Lexer for the Cure programming language.

  Converts Cure source code into a flat list of tokens suitable for parsing.
  The lexer handles:

  - All Cure keywords (Section 3.3 of the syntax spec)
  - All operators (Section 3.4)
  - All literal forms (integers, floats, hex, binary, strings, atoms, booleans,
    nil, regex, char, binary/bytes literals)
  - Indentation tracking: emits `:indent` and `:dedent` tokens based on
    whitespace changes (spaces only; tabs are a lexer error)
  - String interpolation (`"hello \#{expr}"`)
  - Single-line comments (`#`)
  - Position tracking (line, column) on every token

  ## Pipeline Events

  The lexer emits the following events via `Cure.Pipeline.Events`:

  - `{:lexer, :token_produced, token, meta}` -- for each token produced
  - `{:lexer, :lex_complete, tokens, meta}` -- when lexing finishes successfully
  - `{:lexer, :error, error, meta}` -- on lexer errors

  ## Usage

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize("fn add(x: Int, y: Int) -> Int = x + y")
      {:error, reason} = Cure.Compiler.Lexer.tokenize("\\t invalid")
  """

  alias Cure.Compiler.Token
  alias Cure.Pipeline.Events

  # -- Keywords (Section 3.3) ------------------------------------------------

  # Macro vocabularies are not lexer keywords. Standard-library and user
  # macros are dispatched from the ordinary identifier path, so adding a
  # language-level macro never requires changing this list.
  @keywords ~w(
    mod fn let type typealias opaque primitive indexed indices rec proto impl local use as
    interface implementation deriving
    match pickup if elif else then for do end
    in try catch finally throw return yield
    spawn send receive after
    when where and or not
    band bor bxor bsl bsr bnot
    true false nil
    extern proof
    quote unsafe
  )a

  # Contextual words are identifiers lexically. The parser promotes them only
  # where the surrounding grammar proves the construct. Keeping this list at
  # the lexer boundary prevents declaration vocabulary from stealing ordinary
  # binder/value names everywhere else. Add words here one at a time with both
  # construct and identifier regressions.
  # `precedencegroup`/`infix`/`prefix`/`postfix` head the declaration-driven
  # fixity grammar (Phase 3). They are common English words, so reserving them
  # unconditionally would steal ordinary identifier names; they are kept
  # contextual and the parser promotes them only at a declaration-shaped head.
  @contextual_keywords ~w(proof have requires precedencegroup infix prefix postfix)a

  @keyword_strings Enum.map(@keywords, &Atom.to_string/1)

  @keyword_string_set @keyword_strings
                      |> MapSet.new()
                      |> MapSet.difference(MapSet.new(Enum.map(@contextual_keywords, &Atom.to_string/1)))

  @doc "Words lexed as identifiers and promoted contextually by the parser."
  def contextual_keywords, do: @contextual_keywords

  @doc "True when a bare word is tokenized as a keyword/operator rather than an identifier."
  @spec reserved_word?(String.t()) :: boolean()
  def reserved_word?(word) when is_binary(word), do: MapSet.member?(@keyword_string_set, word)
  def reserved_word?(_word), do: false

  # -- Lexer state -----------------------------------------------------------

  defstruct [
    :source,
    :file,
    pos: 0,
    line: 1,
    col: 1,
    tokens: [],
    indent_stack: [0],
    at_line_start: true,
    paren_depth: 0,
    preserve_comments: false,
    collect_trivia: false,
    trivia: [],
    emit_events: true,
    keyword_set: @keyword_string_set
  ]

  @type t :: %__MODULE__{}

  # -- Public API ------------------------------------------------------------

  @doc """
  Tokenize a Cure source string.

  Returns `{:ok, tokens}` on success or `{:error, reason}` on failure.
  The returned token list is in source order and ends with an `:eof` token.
  Appropriate `:dedent` tokens are emitted at the end to close all open
  indentation levels.

  ## Options

  - `:file` -- filename for error messages and event metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:preserve_comments` -- when `true`, emit `:line_comment` tokens for plain
    `#` comments (v0.20.0+). Default `false` so existing pipelines see no
    change. Doc comments (`##`, `###`) are always preserved as `:doc_comment`
    tokens regardless of this flag.
  - `:trivia` -- when `true`, additionally collect *every* comment and blank-line
    run as positioned trivia and return `{:ok, tokens, trivia}` (a 3-tuple).
    `trivia` is an ordered (source-order) list of
    `{:comment, text, line, col} | {:doc_comment, text, line, col} | {:blank, count, line}`.
    Default `false`, in which case the return shape is the usual `{:ok, tokens}`.
    Independent of `:preserve_comments` (which governs the main token stream).
  - `:edition` -- the Cure edition the source is read against (default
    `Cure.Edition.current/0`). Keywords retired at/before this edition (per the
    migration registry) are lexed as plain identifiers instead.
  - `:migrate_rules` -- the migration rule list used to derive the retired-keyword
    set (default `Cure.Migrate.rules/0`); overridable for testing.
  """
  @spec tokenize(String.t(), keyword()) ::
          {:ok, [Token.t()]} | {:ok, [Token.t()], [tuple()]} | {:error, term()}
  def tokenize(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)
    preserve? = Keyword.get(opts, :preserve_comments, false)
    trivia? = Keyword.get(opts, :trivia, false)

    edition = Keyword.get(opts, :edition, Cure.Edition.current())
    migrate_rules = Keyword.get(opts, :migrate_rules, Cure.Migrate.rules())
    retired = MapSet.new(Cure.Edition.retired_keywords(edition, migrate_rules))
    keyword_set = MapSet.difference(@keyword_string_set, retired)

    state = %__MODULE__{
      source: source,
      file: file,
      preserve_comments: preserve?,
      collect_trivia: trivia?,
      emit_events: emit?,
      keyword_set: keyword_set
    }

    case do_tokenize(state) do
      {:ok, state} ->
        # Close remaining indentation levels
        state = close_indents(state)

        tokens =
          [Token.new(:eof, nil, state.line, state.col) | state.tokens]
          |> Enum.reverse()
          |> attach_token_spans(source, file)

        if emit? do
          Enum.each(tokens, fn token ->
            Events.emit(:lexer, :token_produced, token, Events.meta(file, token.line))
          end)

          Events.emit(:lexer, :lex_complete, tokens, Events.meta(file, state.line))
        end

        if trivia? do
          {:ok, tokens, Enum.reverse(state.trivia)}
        else
          {:ok, tokens}
        end

      {:error, reason, state} ->
        if emit? do
          Events.emit(:lexer, :error, reason, Events.meta(file, state.line))
        end

        {:error, reason}
    end
  end

  # -- Core loop -------------------------------------------------------------

  defp do_tokenize(%{source: source, pos: pos} = state) when pos >= byte_size(source) do
    {:ok, state}
  end

  defp do_tokenize(state) do
    case lex_next(state) do
      {:ok, state} -> do_tokenize(state)
      {:error, _reason, _state} = err -> err
    end
  catch
    {:error, _reason, _state} = err -> err
  end

  defp lex_next(%{at_line_start: true} = state) do
    lex_indentation(state)
  end

  defp lex_next(state) do
    case peek(state) do
      # Newline
      ?\n ->
        {:ok, handle_newline(state)}

      # Carriage return
      ?\r ->
        {:ok, advance(state, 1)}

      # Spaces (not at line start -> skip)
      ?\s ->
        {:ok, skip_spaces(state)}

      # Tab (error)
      ?\t ->
        {:error, {:tab_not_allowed, state.line, state.col}, state}

      # Comment
      ?# ->
        lex_comment_or_operator(state)

      # String
      ?" ->
        lex_string(state)

      # Quoted identifier
      ?` ->
        lex_quoted_identifier(state)

      # Char literal
      ?' ->
        lex_char(state)

      # Atom (symbol)
      ?: ->
        lex_atom_or_colon(state)

      # Binary literal << >>
      ?< ->
        lex_angle_or_op(state)

      # Melquiades operator (unicode `✉`, U+2709 ENVELOPE): 0xE2 0x9C 0x89.
      # Detection can't live in a guard (peek_at/2 is a plain function,
      # not a macro), so we dispatch on the first byte and inspect the
      # next two inside lex_melquiades_envelope/1. Any other 0xE2-led
      # sequence falls through to the unexpected-character error.
      0xE2 ->
        lex_melquiades_envelope(state)

      # Percent sigils: %[ %{
      ?% ->
        lex_percent(state)

      # Brackets
      ?( ->
        {:ok, emit_single(state, :lparen, "(", inc_paren: true)}

      ?) ->
        {:ok, emit_single(state, :rparen, ")", dec_paren: true)}

      # Quasiquote splice open `$(` (SP5.1). `$` is otherwise only an
      # identifier *continuation* (gensyms `base$N`), never a token start, so
      # `$(` is unambiguous. The matching `)` is an ordinary `:rparen`; the
      # inner expression lexes normally under the bumped paren depth.
      ?$ ->
        if peek_at(state, 1) == ?( do
          {:ok, emit_single(state, :splice_open, "$(", inc_paren: true)}
        else
          {:error, {:unexpected_character, ?$, state.line, state.col}, state}
        end

      ?[ ->
        {:ok, emit_single(state, :lbracket, "[")}

      ?] ->
        {:ok, emit_single(state, :rbracket, "]")}

      ?{ ->
        {:ok, emit_single(state, :lbrace, "{")}

      ?} ->
        {:ok, emit_single(state, :rbrace, "}")}

      ?, ->
        {:ok, emit_single(state, :comma, ",")}

      ?; ->
        {:ok, emit_single(state, :semicolon, ";")}

      # Operators and punctuation
      ?@ ->
        {:ok, emit_single(state, :at, "@")}

      ?_ ->
        lex_identifier(state)

      c when c in ?a..?z ->
        lex_identifier(state)

      c when c in ?A..?Z ->
        lex_identifier(state)

      c when c in ?0..?9 ->
        lex_number(state)

      ?+ ->
        lex_plus(state)

      ?- ->
        lex_minus(state)

      ?* ->
        lex_star(state)

      ?/ ->
        lex_slash(state)

      ?= ->
        lex_equal(state)

      ?! ->
        lex_bang(state)

      ?> ->
        lex_greater(state)

      ?| ->
        lex_pipe_or_bar(state)

      ?. ->
        lex_dot(state)

      ?^ ->
        {:ok, emit_single(state, :caret, "^")}

      ?? ->
        lex_hole(state)

      _ ->
        {:error, {:unexpected_character, peek(state), state.line, state.col}, state}
    end
  end

  # -- Indentation -----------------------------------------------------------

  defp lex_indentation(state) do
    {indent, state} = measure_indent(state)

    # Skip blank lines and comment-only lines: they must not affect indentation.
    # If the next char after leading whitespace is a newline (or EOF), treat
    # the line as blank and keep `at_line_start: true` for the next line.
    case peek(state) do
      c when c in [?\n, ?\r, nil] ->
        # Blank line -- advance past the newline without emitting indent/dedent.
        # Record it as trivia on the `\n`/EOF end-of-line (not the bare `\r`,
        # which for `\r\n` would double-count the same line).
        state = if c == ?\r, do: state, else: record_blank(state, state.line)

        state =
          case c do
            ?\n ->
              %{state | pos: state.pos + 1, line: state.line + 1, col: 1}

            ?\r ->
              %{state | pos: state.pos + 1}

            nil ->
              state
          end

        {:ok, %{state | at_line_start: true}}

      ?# ->
        # Comment-only line -- consume comment or doc comment, then treat as blank.
        #
        # Emit any `:dedent` tokens *first* so a doc comment that sits at
        # a lower indent level than the previous block's contents binds to
        # the outer block. Without this, the token stream would put
        # `doc_comment` *before* `dedent`, which makes the parser treat
        # the comment as belonging to the inner (ending) block.
        state = maybe_emit_dedents_to(state, indent)

        cond do
          # `###` fenced multi-line doc comment
          peek_at(state, 1) == ?# and peek_at(state, 2) == ?# ->
            {:ok, state} = lex_fenced_doc(state)
            {:ok, %{state | at_line_start: true}}

          # `##` single-line doc comment
          peek_at(state, 1) == ?# ->
            start_col = state.col
            state = advance(state, 2)
            state = if peek(state) == ?\s, do: advance(state, 1), else: state
            {text, state} = consume_while(state, fn ch -> ch != ?\n end)
            token = Token.new(:doc_comment, text, state.line, start_col)
            maybe_emit_event(state, token)
            state = record_trivia(state, {:doc_comment, text, state.line, start_col})
            {:ok, %{state | tokens: [token | state.tokens], at_line_start: true}}

          # plain `#` comment
          true ->
            start_col = state.col
            state = advance(state, 1)
            state = if peek(state) == ?\s, do: advance(state, 1), else: state
            {text, state} = consume_while(state, fn ch -> ch != ?\n end)
            state = emit_line_comment_if_enabled(state, text, start_col)
            {:ok, %{state | at_line_start: true}}
        end

      _ ->
        [current | _] = state.indent_stack

        cond do
          indent > current ->
            state = push_indent(state, indent)
            {:ok, %{state | at_line_start: false}}

          indent < current ->
            state = pop_indents(state, indent)
            {:ok, %{state | at_line_start: false}}

          true ->
            {:ok, %{state | at_line_start: false}}
        end
    end
  end

  defp measure_indent(state) do
    measure_indent(state, 0)
  end

  defp measure_indent(state, acc) do
    case peek(state) do
      ?\s -> measure_indent(advance(state, 1), acc + 1)
      ?\t -> throw({:error, {:tab_not_allowed, state.line, state.col}, state})
      _ -> {acc, state}
    end
  end

  defp push_indent(state, indent) do
    token = Token.new(:indent, indent, state.line, 1)
    maybe_emit_event(state, token)
    %{state | indent_stack: [indent | state.indent_stack], tokens: [token | state.tokens]}
  end

  defp pop_indents(%{indent_stack: [current | rest]} = state, target) when current > target do
    token = Token.new(:dedent, current, state.line, 1)
    maybe_emit_event(state, token)
    state = %{state | indent_stack: rest, tokens: [token | state.tokens]}
    pop_indents(state, target)
  end

  defp pop_indents(state, _target), do: state

  # Emit any needed `:dedent` tokens so the current indent stack top is
  # `<= target`. Used when a comment-only line reduces the effective
  # indentation before we produce any content for that line.
  defp maybe_emit_dedents_to(%{indent_stack: [current | _]} = state, target)
       when current > target do
    pop_indents(state, target)
  end

  defp maybe_emit_dedents_to(state, _target), do: state

  defp close_indents(%{indent_stack: [0]} = state), do: state

  defp close_indents(%{indent_stack: [level | rest]} = state) when level > 0 do
    token = Token.new(:dedent, level, state.line, state.col)
    state = %{state | indent_stack: rest, tokens: [token | state.tokens]}
    close_indents(state)
  end

  defp close_indents(state), do: state

  # -- Newlines --------------------------------------------------------------

  defp handle_newline(state) do
    # Don't emit newline tokens when inside parens/brackets/braces
    if state.paren_depth > 0 do
      state |> advance(1) |> Map.put(:line, state.line + 1) |> Map.put(:col, 1)
    else
      token = Token.new(:newline, "\n", state.line, state.col)
      maybe_emit_event(state, token)

      %{state | tokens: [token | state.tokens]}
      |> advance(1)
      |> Map.put(:line, state.line + 1)
      |> Map.put(:col, 1)
      |> Map.put(:at_line_start, true)
    end
  end

  # -- Comments --------------------------------------------------------------

  defp lex_comment_or_operator(state) do
    # `#` introduces a comment. There are three flavours:
    #
    #   #         plain line comment
    #   ##        single-line doc comment (back-compat, one per line)
    #   ###...### fenced multi-line doc comment (v0.17.0+)
    #
    # The fenced form is preferred because it sidesteps a long-standing
    # parser ambiguity between `##` lines and multi-clause function
    # definitions, and because multi-line prose reads better without
    # having to prefix every line.
    cond do
      # ### ... ### -- fenced doc comment
      peek_at(state, 1) == ?# and peek_at(state, 2) == ?# ->
        lex_fenced_doc(state)

      # ## single-line doc comment
      peek_at(state, 1) == ?# ->
        start_col = state.col
        state = advance(state, 2)
        state = if peek(state) == ?\s, do: advance(state, 1), else: state
        {text, state} = consume_while(state, fn c -> c != ?\n end)
        token = Token.new(:doc_comment, text, state.line, start_col)
        maybe_emit_event(state, token)
        state = record_trivia(state, {:doc_comment, text, state.line, start_col})
        {:ok, %{state | tokens: [token | state.tokens]}}

      # plain `#` comment
      true ->
        start_col = state.col
        state = advance(state, 1)
        state = if peek(state) == ?\s, do: advance(state, 1), else: state
        {text, state} = consume_while(state, fn c -> c != ?\n end)
        state = emit_line_comment_if_enabled(state, text, start_col)
        {:ok, state}
    end
  end

  # Emit a `:line_comment` token for a plain `#` comment when preservation
  # is enabled. The token carries the trimmed comment body (without the
  # leading `# `), so consumers can re-render comments without having to
  # recover the prefix heuristically.
  defp emit_line_comment_if_enabled(state, text, start_col) do
    # Trivia collection is independent of `preserve_comments`: record the
    # comment for a lossless reprint regardless of whether the main token
    # stream carries a `:line_comment` token.
    state = record_trivia(state, {:comment, text, state.line, start_col})
    emit_line_comment_token(state, text, start_col)
  end

  defp emit_line_comment_token(%{preserve_comments: true} = state, text, start_col) do
    token = Token.new(:line_comment, text, state.line, start_col)
    maybe_emit_event(state, token)
    %{state | tokens: [token | state.tokens]}
  end

  defp emit_line_comment_token(state, _text, _start_col), do: state

  # -- Trivia collection (trivia: true) --------------------------------------
  #
  # Independent of `preserve_comments`: records every comment and blank-line
  # run as a positioned item so a lossless reprint (migration facility) can
  # place it back. Items are prepended (state.trivia is reversed on return).

  defp record_trivia(%{collect_trivia: false} = state, _item), do: state

  defp record_trivia(%{collect_trivia: true} = state, item) do
    %{state | trivia: [item | state.trivia]}
  end

  # A blank line merges into an immediately-preceding blank run so a run of N
  # consecutive blank lines becomes a single `{:blank, N, first_line}` item.
  # Contiguity: the prior run spans `sl .. sl + count - 1`, so the next blank
  # at `sl + count` extends it; anything else (a comment on an intervening
  # line, a gap) starts a fresh run.
  defp record_blank(%{collect_trivia: false} = state, _line), do: state

  # The `\n` that terminates a comment-only line is NOT a blank line: the
  # line-start comment branch (lex_indentation) leaves its trailing newline
  # for the next lex_indentation call, which then sees an otherwise-empty
  # line and would spuriously count it. A comment we just recorded on this
  # exact line number means this end-of-line belongs to that comment -- skip.
  defp record_blank(%{collect_trivia: true, trivia: [{k, _t, cl, _c} | _]} = state, line)
       when k in [:comment, :doc_comment] and cl == line do
    state
  end

  defp record_blank(%{collect_trivia: true, trivia: [{:blank, count, sl} | rest]} = state, line)
       when sl + count == line do
    %{state | trivia: [{:blank, count + 1, sl} | rest]}
  end

  defp record_blank(%{collect_trivia: true} = state, line) do
    %{state | trivia: [{:blank, 1, line} | state.trivia]}
  end

  # Consume a `###\n...\n###` block and emit a single `:doc_comment` token.
  #
  # The opening `###` must be followed by either a newline or optional
  # whitespace and then a newline. Everything up to the next line that
  # consists of (whitespace + `###` + optional trailing content) is
  # collected as the doc body. Leading whitespace common to every body
  # line is stripped.
  defp lex_fenced_doc(state) do
    start_line = state.line
    start_col = state.col

    # Consume the opening ###.
    state = advance(state, 3)

    # Consume any `### some trailing text` on the opening line.
    {opening_tail, state} = consume_while(state, fn c -> c != ?\n end)

    # Step over the newline that ends the opening line.
    state =
      case peek(state) do
        ?\n ->
          state
          |> advance(1)
          |> Map.put(:line, state.line + 1)
          |> Map.put(:col, 1)

        _ ->
          state
      end

    {body_lines, state} = collect_fenced_lines(state, [])

    text =
      body_lines
      |> strip_common_indent()
      |> Enum.join("\n")
      |> prepend_opening_tail(opening_tail)

    token = Token.new(:doc_comment, text, start_line, start_col)
    maybe_emit_event(state, token)
    state = record_trivia(state, {:doc_comment, text, start_line, start_col})
    {:ok, %{state | tokens: [token | state.tokens]}}
  end

  defp collect_fenced_lines(state, acc) do
    cond do
      peek(state) == nil ->
        {Enum.reverse(acc), state}

      fence_close_line?(state) ->
        state = consume_fence_close(state)
        {Enum.reverse(acc), state}

      true ->
        {line, state} = consume_while(state, fn c -> c != ?\n end)

        state =
          case peek(state) do
            ?\n ->
              state
              |> advance(1)
              |> Map.put(:line, state.line + 1)
              |> Map.put(:col, 1)

            _ ->
              state
          end

        collect_fenced_lines(state, [line | acc])
    end
  end

  # True when the current position starts a line of the shape
  # `<whitespace>* ### <anything>*<newline or eof>`.
  defp fence_close_line?(state) do
    {_spaces, offset} = count_leading_spaces(state, 0)
    a = peek_at(state, offset)
    b = peek_at(state, offset + 1)
    c = peek_at(state, offset + 2)
    a == ?# and b == ?# and c == ?#
  end

  defp count_leading_spaces(state, offset) do
    case peek_at(state, offset) do
      ?\s -> count_leading_spaces(state, offset + 1)
      _ -> {offset, offset}
    end
  end

  defp consume_fence_close(state) do
    {_spaces, state} = consume_while(state, fn c -> c == ?\s end)
    # Advance past the three #s.
    state = advance(state, 3)
    # Consume any trailing content up to newline.
    {_trailing, state} = consume_while(state, fn c -> c != ?\n end)

    case peek(state) do
      ?\n ->
        state
        |> advance(1)
        |> Map.put(:line, state.line + 1)
        |> Map.put(:col, 1)

      _ ->
        state
    end
  end

  defp strip_common_indent([]), do: []

  defp strip_common_indent(lines) do
    non_blank = Enum.reject(lines, fn l -> String.trim(l) == "" end)

    indent =
      case non_blank do
        [] -> 0
        _ -> Enum.map(non_blank, &leading_space_count/1) |> Enum.min()
      end

    Enum.map(lines, fn l ->
      if String.length(l) >= indent, do: String.slice(l, indent..-1//1), else: l
    end)
  end

  defp leading_space_count(line) do
    line
    |> String.graphemes()
    |> Enum.take_while(fn g -> g == " " end)
    |> length()
  end

  defp prepend_opening_tail(body, tail) do
    trimmed = String.trim(tail)
    if trimmed == "", do: body, else: trimmed <> "\n" <> body
  end

  # -- Holes -----------------------------------------------------------------

  # `?name` (named hole) or `?_` (anonymous hole) — a deferred term that reports
  # its goal type and blocks codegen (design spec §6 / M8.5).
  defp lex_hole(state) do
    start_col = state.col
    state = advance(state, 1)

    {name, state} =
      consume_while(state, fn c ->
        c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_
      end)

    {name, state} =
      if name == "" do
        {questions, state} = consume_while(state, &(&1 == ??))
        {if(questions == "", do: "", else: "?"), state}
      else
        {name, state}
      end

    # `??` was the pre-0.34 anonymous spelling. Reserve it as a targeted syntax
    # error instead of silently accepting a breaking spelling; three or more
    # question marks remain the compiler-generated placeholder form used by
    # proof suggestions and diagnostics.
    if name == "?" and state.col == start_col + 2 do
      {:error, {:obsolete_anonymous_hole, state.line, start_col}, state}
    else
      token = Token.new(:hole, name, state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  # -- Identifiers & keywords -----------------------------------------------

  defp lex_quoted_identifier(state) do
    start_col = state.col
    state = advance(state, 1)

    case consume_quoted_identifier(state, []) do
      {:ok, name, state} ->
        token = Token.new(:identifier, name, state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}

      {:error, state} ->
        {:error, {:unterminated_quoted_identifier, state.line, start_col}, state}
    end
  end

  defp consume_quoted_identifier(state, acc) do
    case peek(state) do
      nil ->
        {:error, state}

      ?` ->
        state = advance(state, 1)
        {:ok, acc |> Enum.reverse() |> IO.iodata_to_binary(), state}

      ?\\ ->
        case peek_at(state, 1) do
          nil ->
            {:error, state}

          c ->
            consume_quoted_identifier(advance(state, 2), [<<c>> | acc])
        end

      c ->
        consume_quoted_identifier(advance(state, 1), [<<c>> | acc])
    end
  end

  defp lex_identifier(state) do
    start_col = state.col

    {word, state} =
      consume_while(state, fn c ->
        # `$` is permitted only as an identifier *continuation* char (the
        # dispatch that enters this function never starts on `$`), so a name
        # can never *begin* with it. This is exactly the shape macro hygiene
        # gensyms take (`base$<counter>`): freshened binders such as
        # `initial$0` must lex back as a single identifier so that
        # parse->print->parse round-trips the expanded corpus (the Printer
        # totality gate). `$` has no other lexical role in Cure.
        c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?$
      end)

    # Allow a trailing `?` for predicate-style names (Elixir convention,
    # e.g. `is_empty?`, `even?`).
    {word, state} =
      cond do
        not MapSet.member?(state.keyword_set, word) and peek(state) == ?? ->
          # `?` immediately followed by an identifier-starter is a *hole*
          # prefix (`?name`), so only consume the `?` when it is a
          # proper suffix (followed by something that can't begin a
          # new identifier on its own on this side).
          next = peek_at(state, 1)

          if next in ?a..?z or next in ?A..?Z or next == ?_ do
            {word, state}
          else
            {word <> "?", advance(state, 1)}
          end

        true ->
          {word, state}
      end

    {type, value} =
      if MapSet.member?(state.keyword_set, word) do
        kw = String.to_atom(word)

        case kw do
          true -> {:bool, true}
          false -> {:bool, false}
          nil -> {nil, nil}
          :and -> {:and_op, :and}
          :or -> {:or_op, :or}
          :not -> {:not_op, :not}
          :band -> {:band_op, :band}
          :bor -> {:bor_op, :bor}
          :bxor -> {:bxor_op, :bxor}
          :bsl -> {:bsl_op, :bsl}
          :bsr -> {:bsr_op, :bsr}
          :bnot -> {:bnot_op, :bnot}
          other -> {:keyword, other}
        end
      else
        {:identifier, word}
      end

    token = Token.new(type, value, state.line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]}}
  end

  # -- Numbers ---------------------------------------------------------------

  defp lex_number(state) do
    start_col = state.col

    case peek(state, 2) do
      "0x" -> lex_hex(state, start_col)
      "0b" -> lex_binary_int(state, start_col)
      _ -> lex_decimal(state, start_col)
    end
  end

  defp lex_hex(state, start_col) do
    state = advance(state, 2)

    {digits, state} =
      consume_while(state, fn c ->
        c in ?0..?9 or c in ?a..?f or c in ?A..?F or c == ?_
      end)

    clean = String.replace(digits, "_", "")

    # Reject both an empty digit run (`0x`) and an all-underscore run (`0x_`):
    # the latter passes `digits != ""` but strips to "", and String.to_integer
    # would then raise ArgumentError. Guard on `clean` so both surface cleanly.
    if clean == "" do
      {:error, {:invalid_hex_literal, state.line, start_col}, state}
    else
      value = String.to_integer(clean, 16)
      token = %{Token.new(:integer, value, state.line, start_col) | lexeme: "0x" <> clean}
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  defp lex_binary_int(state, start_col) do
    state = advance(state, 2)

    {digits, state} =
      consume_while(state, fn c ->
        c in [?0, ?1, ?_]
      end)

    clean = String.replace(digits, "_", "")

    # Reject `0b` (empty) and `0b_` (all-underscore, strips to ""); the latter
    # would otherwise reach String.to_integer/2 and raise. See lex_hex.
    if clean == "" do
      {:error, {:invalid_binary_literal, state.line, start_col}, state}
    else
      value = String.to_integer(clean, 2)
      token = %{Token.new(:integer, value, state.line, start_col) | lexeme: "0b" <> clean}
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  defp lex_decimal(state, start_col) do
    {int_part, state} = consume_while(state, fn c -> c in ?0..?9 or c == ?_ end)

    cond do
      # Float: digits.digits or digits.digitseN
      peek(state) == ?. and peek_at(state, 1) in ?0..?9 ->
        state = advance(state, 1)
        {frac_part, state} = consume_while(state, fn c -> c in ?0..?9 or c == ?_ end)
        {exp_part, state} = lex_exponent(state)
        raw = "#{int_part}.#{frac_part}#{exp_part}" |> String.replace("_", "")
        finish_float(raw, raw, state, start_col)

      # Scientific notation without dot: 1e3
      peek(state) in [?e, ?E] ->
        {exp_part, state} = lex_exponent(state)
        exact = "#{int_part}#{exp_part}" |> String.replace("_", "")
        host = "#{int_part}.0#{exp_part}" |> String.replace("_", "")
        finish_float(exact, host, state, start_col)

      true ->
        clean = String.replace(int_part, "_", "")
        value = String.to_integer(clean)
        token = %{Token.new(:integer, value, state.line, start_col) | lexeme: clean}
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  # Build a float token from an assembled numeric string, converting a raw that
  # String.to_float/1 rejects — a truncated exponent (`1.0e`, from `1e`/`1e+`)
  # or an out-of-range magnitude (`1.0e400`, which overflows the IEEE double) —
  # into a clean lexer error instead of a raised ArgumentError that would crash
  # the whole tokenize.
  defp finish_float(exact, host, state, start_col) do
    token = %{Token.new(:float, String.to_float(host), state.line, start_col) | lexeme: exact}
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]}}
  rescue
    ArgumentError -> {:error, {:invalid_float_literal, state.line, start_col}, state}
  end

  defp lex_exponent(state) do
    case peek(state) do
      c when c in [?e, ?E] ->
        state = advance(state, 1)

        {sign, state} =
          case peek(state) do
            ?+ -> {"+", advance(state, 1)}
            ?- -> {"-", advance(state, 1)}
            _ -> {"", state}
          end

        {digits, state} = consume_while(state, fn c -> c in ?0..?9 end)
        {"e#{sign}#{digits}", state}

      _ ->
        {"", state}
    end
  end

  # -- Strings ---------------------------------------------------------------

  defp lex_string(state) do
    start_col = state.col
    state = advance(state, 1)
    lex_string_body(state, start_col, [])
  end

  defp lex_string_body(state, start_col, acc) do
    case peek(state) do
      nil ->
        {:error, {:unterminated_string, state.line, start_col}, state}

      ?" ->
        state = advance(state, 1)
        parts = Enum.reverse(acc)

        if Enum.all?(parts, &is_binary/1) do
          # Plain string, no interpolation
          value = IO.iodata_to_binary(parts)
          token = Token.new(:string, value, state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
        else
          # String with interpolation parts
          normalized = normalize_string_parts(parts)
          token = Token.new(:string_interpolation, normalized, state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
        end

      ?\\ ->
        state = advance(state, 1)

        case peek(state) do
          ?n -> lex_string_body(advance(state, 1), start_col, ["\n" | acc])
          ?t -> lex_string_body(advance(state, 1), start_col, ["\t" | acc])
          ?\\ -> lex_string_body(advance(state, 1), start_col, ["\\" | acc])
          ?" -> lex_string_body(advance(state, 1), start_col, ["\"" | acc])
          ?# -> lex_string_body(advance(state, 1), start_col, ["#" | acc])
          _ -> lex_string_body(state, start_col, ["\\" | acc])
        end

      ?# ->
        if peek_at(state, 1) == ?{ do
          # String interpolation. The interpolated expression is its own paren scope:
          # enter at depth 0, and restore the enclosing depth on the way out.
          outer_paren_depth = state.paren_depth
          state = advance(state, 2)
          {expr_tokens, state} = lex_interpolation_expr(%{state | paren_depth: 0}, 0)
          state = %{state | paren_depth: outer_paren_depth}
          lex_string_body(state, start_col, [{:expr, expr_tokens} | acc])
        else
          state2 = advance(state, 1)
          lex_string_body(state2, start_col, ["#" | acc])
        end

      # A string literal may span physical lines — there is no lexer error for a raw
      # newline in one. `advance/2` only moves `pos` and `col`, so swallowing the byte
      # through the catch-all below left `line` stale, and every token after a multi-line
      # string reported a line number short by however many newlines the string held.
      # Every other multi-line construct here (`handle_newline/1`, `collect_fenced_lines/2`,
      # `lex_indentation/1`'s blank-line branch) bumps `line` and resets `col`.
      ?\n ->
        state = %{state | pos: state.pos + 1, line: state.line + 1, col: 1}
        lex_string_body(state, start_col, ["\n" | acc])

      c ->
        state = advance(state, 1)
        # `c` is a raw source byte (peek/1 is :binary.at/2). The source is
        # UTF-8, so appending the byte verbatim preserves multi-byte
        # characters. Re-encoding here with <<c::utf8>> would double-encode
        # every non-ASCII byte (e.g. E2 80 99 -> C3 A2 C2 80 C2 99).
        lex_string_body(state, start_col, [<<c>> | acc])
    end
  end

  defp lex_interpolation_expr(state, depth) do
    case peek(state) do
      nil ->
        {[], state}

      ?} when depth == 0 ->
        {[], advance(state, 1)}

      ?{ ->
        token = Token.new(:lbrace, "{", state.line, state.col)
        {rest, state} = lex_interpolation_expr(advance(state, 1), depth + 1)
        {[token | rest], state}

      ?} ->
        token = Token.new(:rbrace, "}", state.line, state.col)
        {rest, state} = lex_interpolation_expr(advance(state, 1), depth - 1)
        {[token | rest], state}

      _ ->
        # Tokenize one token inside interpolation, then continue. `paren_depth` must
        # survive the step: it used to be forced to 0 on the way in and overwritten with
        # the pre-step snapshot on the way out, so a `(` opened inside an interpolation
        # never reached the counter `handle_newline/1` consults, and a newline inside a
        # parenthesised call in `"#{f(a,\nb)}"` emitted a spurious `:newline`.
        inner_state = %{state | tokens: []}

        case lex_next(inner_state) do
          {:ok, inner_state} ->
            produced = Enum.reverse(inner_state.tokens)

            next_state = %{inner_state | tokens: state.tokens}
            {rest, final_state} = lex_interpolation_expr(next_state, depth + brace_delta(produced))
            {produced ++ rest, final_state}

          {:error, _reason, err_state} ->
            {[], err_state}
        end
    end
  end

  # `depth` counts the braces still open inside a `#{…}`, and the clauses above only see a
  # BARE `{` — the raw byte. `%{` is consumed whole by `lex_percent/1` as one `:map_open`
  # token, so its brace never bumped the counter, while its closing `}` was still seen raw.
  # `"#{ %{a: 1} }"` therefore ended the interpolation at the map's `}`, one brace early,
  # and swallowed the rest of the string as literal text. A record literal's `Type{` uses a
  # bare `{`, which is why only the map sigil was affected.
  defp brace_delta(produced), do: Enum.count(produced, &(&1.type == :map_open))

  defp normalize_string_parts(parts) do
    # Merge consecutive binary parts, keep {:expr, tokens} as-is
    parts
    |> Enum.reduce([], fn
      part, [{:string_part, prev} | rest] when is_binary(part) ->
        [{:string_part, prev <> part} | rest]

      part, acc when is_binary(part) ->
        [{:string_part, part} | acc]

      {:expr, tokens}, acc ->
        [{:expr, tokens} | acc]
    end)
    |> Enum.reverse()
  end

  # -- Char literal ----------------------------------------------------------

  defp lex_char(state) do
    start_col = state.col
    # Advance past opening '
    state = advance(state, 1)

    if peek(state) == ?' and peek_at(state, 1) == ?' do
      # Three quotes are an unescaped single-quote character: the first quote
      # opened the literal, the second is its value, and the third closes it.
      state = advance(state, 2)
      token = Token.new(:char, ?', state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    else
      case peek(state) do
        ?\\ ->
          state = advance(state, 1)

          {value, state} =
            case peek(state) do
              ?n ->
                {?\n, advance(state, 1)}

              ?t ->
                {?\t, advance(state, 1)}

              ?r ->
                {?\r, advance(state, 1)}

              ?b ->
                {?\b, advance(state, 1)}

              ?f ->
                {?\f, advance(state, 1)}

              # Bell, escape, vertical tab. `Char` is a nominal builtin whose only
              # introduction form is a literal, so a control character with no
              # escape here has no spelling at all — `char == 11` cannot stand in
              # for it, because the natural-literal instance for `Char` bottoms out
              # in the extern `from_code_point` and so never reduces at compile
              # time. These three complete the set a regex engine has to name
              # (`\a \b \e \f \n \r \t \v`), and match Elixir's own codes.
              ?a ->
                {?\a, advance(state, 1)}

              ?e ->
                {?\e, advance(state, 1)}

              ?v ->
                {?\v, advance(state, 1)}

              ?\\ ->
                {?\\, advance(state, 1)}

              ?' ->
                {?', advance(state, 1)}

              ?0 ->
                {0, advance(state, 1)}

              # An unrecognized escape must NOT fall through to `decode_char_at`,
              # which would read the byte *after* the backslash literally and
              # silently drop the `\` and turn it into an unrelated character.
              # Cure recognizes only the small escape set above; anything else
              # is a hard error rather than a silent miscompile.
              nil ->
                {:invalid, state}

              _ ->
                {:bad_escape, state}
            end

          cond do
            value == :invalid ->
              {:error, {:unterminated_char, state.line, start_col}, state}

            value == :bad_escape ->
              {:error, {:invalid_char_escape, state.line, start_col}, state}

            true ->
              # Expect closing '
              case peek(state) do
                ?' ->
                  state = advance(state, 1)
                  token = Token.new(:char, value, state.line, start_col)
                  maybe_emit_event(state, token)
                  {:ok, %{state | tokens: [token | state.tokens]}}

                _ ->
                  {:error, {:unterminated_char, state.line, start_col}, state}
              end
          end

        nil ->
          {:error, {:unterminated_char, state.line, start_col}, state}

        _ ->
          case decode_char_at(state) do
            {cp, state} ->
              # Expect closing '
              case peek(state) do
                ?' ->
                  state = advance(state, 1)
                  token = Token.new(:char, cp, state.line, start_col)
                  maybe_emit_event(state, token)
                  {:ok, %{state | tokens: [token | state.tokens]}}

                _ ->
                  {:error, {:unterminated_char, state.line, start_col}, state}
              end

            :invalid ->
              {:error, {:unterminated_char, state.line, start_col}, state}
          end
      end
    end
  end

  # Read one character at the current position as a full Unicode codepoint,
  # advancing past all its UTF-8 bytes. ASCII (byte < 0x80) keeps the fast
  # single-byte path. A multi-byte sequence is decoded via String.next_codepoint/1
  # on the remaining source; a truncated/invalid tail yields :invalid so the caller
  # can surface the existing unterminated-char error rather than crash.
  #
  # The `pos >= byte_size(source)` clause is required, not defensive boilerplate:
  # the escape-fallback call site reaches this function even when there is no byte
  # left to read (a backslash at end-of-source) — `peek/1` returns nil there today
  # and that nil falls through harmlessly to its catch-all. Without this guard,
  # `:binary.at(source, pos)` raises `ArgumentError` on an out-of-range position,
  # and `do_tokenize/1`'s `catch` clause does not rescue raised errors (only
  # `throw`), so the lexer would crash instead of returning `{:unterminated_char,
  # _, _}`. Mirrors the existing two-clause guard idiom used by `peek/1` below.
  defp decode_char_at(%{source: source, pos: pos}) when pos >= byte_size(source), do: :invalid

  defp decode_char_at(%{source: source, pos: pos} = state) do
    case :binary.at(source, pos) do
      byte when byte < 0x80 ->
        {byte, advance(state, 1)}

      _ ->
        rest = binary_part(source, pos, byte_size(source) - pos)

        case String.next_codepoint(rest) do
          {<<cp::utf8>>, _tail} -> {cp, advance(state, byte_size(<<cp::utf8>>))}
          _ -> :invalid
        end
    end
  end

  # -- Atom / colon ----------------------------------------------------------

  defp lex_atom_or_colon(state) do
    start_col = state.col
    next = peek_at(state, 1)

    cond do
      next in ?a..?z or next in ?A..?Z or next == ?_ ->
        state = advance(state, 1)

        {name, state} =
          consume_while(state, fn c ->
            c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_
          end)

        # Allow trailing ? or ! for atoms
        {name, state} =
          if peek(state) in [??, ?!] do
            {name <> <<peek(state)::utf8>>, advance(state, 1)}
          else
            {name, state}
          end

        # The BEAM caps atoms at 255 characters; String.to_atom/1 raises an
        # UNCAUGHT SystemLimitError past that (not the ArgumentError the numeric
        # paths rescue, and do_tokenize's catch only catches throws), so a
        # 256-char `:atom` literal would crash tokenize. Guard the length and
        # return a clean error instead. `name` is ASCII (consume_while accepts
        # only [A-Za-z0-9_] plus a trailing ?/!), so byte_size == char count.
        if byte_size(name) > 255 do
          {:error, {:atom_too_long, state.line, start_col}, state}
        else
          token = Token.new(:atom, String.to_atom(name), state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
        end

      # `::` is the binary-segment specifier operator introduced in
      # v0.20.0. It is distinct from `:` (type annotations) and from
      # `:atom` (symbol literals). Inside `<<...>>` it separates a
      # segment value from its specifier chain.
      next == ?: ->
        token = Token.new(:colon_colon, "::", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      true ->
        token = Token.new(:colon, ":", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Generic (user-declared) symbolic operators ----------------------------

  # Symbol bytes a generic operator lexeme may contain. `-`, `.`, `:` are
  # deliberately EXCLUDED so existing multi-byte forms built on them (`<-|`,
  # `->`, `..`, `..=`, and the `<-` binary-comprehension generator) keep lexing
  # exactly as before — their runs shrink to a single byte here and fall through
  # to the dedicated lexers untouched.
  @generic_op_bytes ~c"<>=!?@|&^%*/+"

  # Multi-byte symbol runs already recognised as FIXED tokens. A run in this set
  # defers to its dedicated lexer so tokenisation stays byte-identical; only a
  # run that is NOT here (and is >= 2 bytes) becomes a generic `:operator` token.
  @fixed_op_runs MapSet.new(~w(<< <> <= >= >> == => != |>))

  # `<<` / `>>` are binary-pattern DELIMITERS, not operators. Maximal munch would
  # otherwise swallow the empty binary pattern `<<>>` (delimiter `<<` immediately
  # followed by delimiter `>>`) into one bogus operator run. When a run begins
  # with a delimiter, defer to the dedicated lexer so it peels just the `<<`/`>>`
  # and the remainder is retokenised from the next byte.
  @op_delimiters ["<<", ">>"]

  # Consulted at the head of every hooked operator lexer: if the maximal run of
  # `@generic_op_bytes` from the cursor is >= 2 bytes and not a fixed form, emit
  # it as one generic `:operator` token carrying the lexeme string; otherwise
  # signal `:fixed` so the dedicated lexer runs unchanged.
  defp generic_operator(state) do
    run = collect_op_run(state, 0, [])

    cond do
      byte_size(run) < 2 -> :fixed
      String.starts_with?(run, @op_delimiters) -> :fixed
      MapSet.member?(@fixed_op_runs, run) -> :fixed
      true -> {:operator, run}
    end
  end

  defp collect_op_run(state, offset, acc) do
    case peek_at(state, offset) do
      c when c in @generic_op_bytes -> collect_op_run(state, offset + 1, [c | acc])
      _ -> acc |> Enum.reverse() |> IO.iodata_to_binary()
    end
  end

  defp emit_operator(state, run) do
    token = Token.new(:operator, run, state.line, state.col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]} |> advance(byte_size(run))}
  end

  # -- Binary literal << >> --------------------------------------------------

  defp lex_angle_or_op(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_angle_or_op_fixed(state)
    end
  end

  defp lex_angle_or_op_fixed(state) do
    start_col = state.col

    case {peek(state), peek_at(state, 1), peek_at(state, 2)} do
      {?<, ?<, _} ->
        token = Token.new(:binary_open, "<<", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      {?<, ?>, _} ->
        # String concat operator
        token = Token.new(:string_concat, "<>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      {?<, ?=, _} ->
        token = Token.new(:lte, "<=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      # Melquiades operator (ASCII form): `<-|` sends a message to the
      # mailbox on the left. Three bytes: `<`, `-`, `|`.
      {?<, ?-, ?|} ->
        token = Token.new(:melquiades, "<-|", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(3)}

      _ ->
        token = Token.new(:lt, "<", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # Unicode `✉` (U+2709 ENVELOPE) is the alternate form of the Melquiades
  # operator. Encoded as three bytes `0xE2 0x9C 0x89` in UTF-8; the lexer
  # records the original lexeme on the token so the printer can round-trip
  # the author's choice between the ASCII and unicode forms. Any other
  # 0xE2-led sequence is unrecognised at the top level; we surface it as
  # the same `:unexpected_character` error the plain path would emit.
  defp lex_melquiades_envelope(state) do
    case {peek_at(state, 1), peek_at(state, 2)} do
      {0x9C, 0x89} ->
        start_col = state.col
        token = Token.new(:melquiades, "✉", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(3)}

      _ ->
        {:error, {:unexpected_character, 0xE2, state.line, state.col}, state}
    end
  end

  # -- Percent sigils: %[ and %{ ---------------------------------------------

  defp lex_percent(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?[ ->
        token = Token.new(:tuple_open, "%[", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?{ ->
        token = Token.new(:map_open, "%{", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:percent, "%", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Operators -------------------------------------------------------------

  defp lex_plus(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_plus_fixed(state)
    end
  end

  defp lex_plus_fixed(state) do
    start_col = state.col
    token = Token.new(:plus, "+", state.line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
  end

  defp lex_minus(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?> ->
        token = Token.new(:arrow, "->", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?- ->
        token = Token.new(:minus, "-", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}

      _ ->
        token = Token.new(:minus, "-", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_star(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_star_fixed(state)
    end
  end

  defp lex_star_fixed(state) do
    start_col = state.col
    token = Token.new(:star, "*", state.line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
  end

  defp lex_slash(state) do
    if regex_literal_start?(state) do
      lex_bare_regex(state)
    else
      case generic_operator(state) do
        {:operator, run} -> emit_operator(state, run)
        :fixed -> lex_slash_fixed(state)
      end
    end
  end

  # A slash is a regex delimiter only where an expression can begin.  Keeping
  # division and regex literals in one lexer is intentional: `/` remains the
  # ordinary arithmetic operator after a completed expression.
  defp regex_literal_start?(%{tokens: []}), do: true

  defp regex_literal_start?(%{tokens: [%Token{type: type} | _]}) do
    type in [
      :assign,
      :arrow,
      :fat_arrow,
      :lparen,
      :lbracket,
      :lbrace,
      :comma,
      :colon,
      :bar,
      :pipe,
      :semicolon,
      :at,
      :return
    ]
  end

  defp regex_literal_start?(_), do: false

  defp lex_bare_regex(state) do
    start_col = state.col
    state = advance(state, 1)
    {body, state} = consume_regex_body(state)

    if peek(state) == ?/ do
      state = advance(state, 1)
      {flags, state} = consume_while(state, &regex_flag?/1)

      case peek(state) do
        c when is_integer(c) and c in ?a..?z ->
          {:error, {:invalid_regex_modifier, c, state.line, state.col}, state}

        c when is_integer(c) and c in ?A..?Z ->
          {:error, {:invalid_regex_modifier, c, state.line, state.col}, state}

        _ ->
          token = Token.new(:regex, {body, flags}, state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
      end
    else
      {:error, {:unterminated_regex, state.line, start_col}, state}
    end
  end

  # Consume a regex body while treating an escaped delimiter as pattern data.
  # The body is kept verbatim because the pure Cure parser owns escape
  # semantics; the lexer only has to find the closing delimiter safely.
  defp consume_regex_body(state, acc \\ []) do
    case peek(state) do
      nil ->
        {IO.iodata_to_binary(Enum.reverse(acc)), state}

      ?/ ->
        {IO.iodata_to_binary(Enum.reverse(acc)), state}

      ?\\ ->
        case peek_at(state, 1) do
          nil -> {IO.iodata_to_binary(Enum.reverse([?\\ | acc])), advance(state, 1)}
          escaped -> consume_regex_body(advance(state, 2), [escaped, ?\\ | acc])
        end

      c ->
        consume_regex_body(advance(state, 1), [c | acc])
    end
  end

  # Elixir/PCRE's sigil modifiers. `r` is retained as the deprecated alias for
  # `U`; `E` is the OTP 28 exported-pattern option and is intentionally accepted
  # by the syntax even though a pure Cure value has no remote export handle.
  defp regex_flag?(c), do: c in [?i, ?m, ?s, ?x, ?u, ?f, ?r, ?U, ?E]

  defp lex_slash_fixed(state) do
    start_col = state.col
    token = Token.new(:slash, "/", state.line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
  end

  defp lex_equal(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_equal_fixed(state)
    end
  end

  defp lex_equal_fixed(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?= ->
        token = Token.new(:eq, "==", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?> ->
        token = Token.new(:fat_arrow, "=>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:assign, "=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_bang(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_bang_fixed(state)
    end
  end

  defp lex_bang_fixed(state) do
    start_col = state.col

    if peek_at(state, 1) == ?= do
      token = Token.new(:neq, "!=", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:bang, "!", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_greater(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_greater_fixed(state)
    end
  end

  defp lex_greater_fixed(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?= ->
        token = Token.new(:gte, ">=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?> ->
        token = Token.new(:binary_close, ">>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:gt, ">", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_pipe_or_bar(state) do
    case generic_operator(state) do
      {:operator, run} -> emit_operator(state, run)
      :fixed -> lex_pipe_or_bar_fixed(state)
    end
  end

  defp lex_pipe_or_bar_fixed(state) do
    start_col = state.col

    if peek_at(state, 1) == ?> do
      token = Token.new(:pipe, "|>", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:bar, "|", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_dot(state) do
    start_col = state.col

    case {peek_at(state, 1), peek_at(state, 2)} do
      {?., ?.} ->
        token = Token.new(:ellipsis, "...", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(3)}

      {?., ?=} ->
        token = Token.new(:range_inclusive, "..=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(3)}

      {?., _} ->
        token = Token.new(:range, "..", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:dot, ".", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Helpers ---------------------------------------------------------------

  defp peek(%{source: source, pos: pos}) when pos >= byte_size(source), do: nil
  defp peek(%{source: source, pos: pos}), do: :binary.at(source, pos)

  defp peek_at(%{source: source, pos: pos}, offset) do
    at = pos + offset

    if at >= byte_size(source) do
      nil
    else
      :binary.at(source, at)
    end
  end

  defp peek(%{source: source, pos: pos}, len) do
    if pos + len > byte_size(source) do
      nil
    else
      binary_part(source, pos, len)
    end
  end

  defp advance(state, n) do
    %{state | pos: state.pos + n, col: state.col + n}
  end

  defp skip_spaces(state) do
    case peek(state) do
      ?\s -> skip_spaces(advance(state, 1))
      _ -> state
    end
  end

  defp consume_while(state, pred) do
    consume_while(state, pred, [])
  end

  defp consume_while(state, pred, acc) do
    case peek(state) do
      nil ->
        {IO.iodata_to_binary(Enum.reverse(acc)), state}

      c ->
        if pred.(c) do
          # `c` is a raw source byte; append it verbatim to preserve UTF-8.
          # Re-encoding with <<c::utf8>> would double-encode non-ASCII bytes
          # in comments and doc comments (whose predicate accepts any byte).
          consume_while(advance(state, 1), pred, [<<c>> | acc])
        else
          {IO.iodata_to_binary(Enum.reverse(acc)), state}
        end
    end
  end

  defp emit_single(state, type, value, opts \\ []) do
    token = Token.new(type, value, state.line, state.col)
    maybe_emit_event(state, token)

    state = %{state | tokens: [token | state.tokens]}
    state = advance(state, String.length(value))

    state =
      if Keyword.get(opts, :inc_paren, false),
        do: %{state | paren_depth: state.paren_depth + 1},
        else: state

    state =
      if Keyword.get(opts, :dec_paren, false),
        do: %{state | paren_depth: max(state.paren_depth - 1, 0)},
        else: state

    state
  end

  # Token events are emitted after the source-order span pass, immediately
  # before `:lex_complete`, so event consumers receive the same complete token
  # values returned by `tokenize/2`.
  defp maybe_emit_event(_state, _token), do: :ok

  # Attach spans in one source-order pass. The scanner cursor is authoritative:
  # it avoids inheriting the legacy lexer's byte-counted columns after Unicode
  # and gives omitted trivia honest ownership between authored tokens.
  defp attach_token_spans(tokens, source, file) do
    line_starts = source_line_starts(source)
    {tokens, _cursor} = attach_token_spans(tokens, source, file, line_starts, 0)
    tokens
  end

  defp attach_token_spans(tokens, source, file, line_starts, initial_cursor) do
    Enum.map_reduce(tokens, initial_cursor, fn token, cursor ->
      {start_byte, end_byte, next_cursor} = token_bytes(token, source, cursor)
      span = token_span(source, file, line_starts, start_byte, end_byte)
      token = %Token{token | span: span, line: span.start_line, col: span.start_column}
      {attach_interpolation_spans(token, source, file, line_starts), next_cursor}
    end)
  end

  defp attach_interpolation_spans(
         %Token{type: :string_interpolation, value: parts, span: span} = token,
         source,
         file,
         line_starts
       ) do
    {parts, _cursor} =
      Enum.map_reduce(parts, span.start_byte, fn
        {:expr, tokens}, cursor ->
          expr_start = find_sequence_end(source, cursor, "\#{")
          {tokens, token_end} = attach_token_spans(tokens, source, file, line_starts, expr_start)
          {{:expr, tokens}, token_end}

        text, cursor when is_binary(text) ->
          {text, cursor}

        part, cursor ->
          {part, cursor}
      end)

    %{token | value: parts}
  end

  defp attach_interpolation_spans(token, _source, _file, _line_starts), do: token

  defp source_line_starts(source) do
    starts =
      source
      |> :binary.matches("\n")
      |> Enum.map(fn {offset, 1} -> offset + 1 end)

    List.to_tuple([0 | starts])
  end

  defp token_span(source, file, line_starts, start_byte, end_byte) do
    {start_line, start_column} = source_coordinates(source, line_starts, start_byte)
    {end_line, end_column} = source_coordinates(source, line_starts, end_byte)

    Cure.Diagnostic.Span.new(
      source_id: file,
      path: file,
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: start_line,
      start_column: start_column,
      end_line: end_line,
      end_column: end_column
    )
  end

  defp source_coordinates(source, line_starts, byte) do
    index = line_index(line_starts, byte, 0, tuple_size(line_starts) - 1)
    line_start = elem(line_starts, index)
    column = source |> binary_part(line_start, byte - line_start) |> scalar_length() |> Kernel.+(1)
    {index + 1, column}
  end

  defp scalar_length(binary) do
    case :unicode.characters_to_list(binary, :utf8) do
      characters when is_list(characters) -> length(characters)
      {:error, valid, rest} -> length(valid) + byte_size(rest)
      {:incomplete, valid, rest} -> length(valid) + byte_size(rest)
    end
  end

  defp line_index(starts, byte, low, high) when low >= high do
    if elem(starts, high) <= byte, do: high, else: max(0, high - 1)
  end

  defp line_index(starts, byte, low, high) do
    middle = div(low + high + 1, 2)

    if elem(starts, middle) <= byte,
      do: line_index(starts, byte, middle, high),
      else: line_index(starts, byte, low, middle - 1)
  end

  defp token_bytes(%Token{type: :eof}, source, _cursor) do
    ending = byte_size(source)
    {ending, ending, ending}
  end

  defp token_bytes(%Token{type: type}, source, cursor) when type in [:indent, :dedent] do
    insertion = skip_trivia(source, cursor)
    {insertion, insertion, cursor}
  end

  defp token_bytes(%Token{type: :newline}, source, cursor) do
    start = find_byte(source, cursor, ?\n)
    {start, min(start + 1, byte_size(source)), min(start + 1, byte_size(source))}
  end

  defp token_bytes(%Token{type: type} = token, source, cursor) when type in [:doc_comment, :line_comment] do
    start = skip_space_only(source, cursor)
    ending = start + authored_length(token, binary_part(source, start, byte_size(source) - start))
    {start, ending, ending}
  end

  defp token_bytes(%Token{} = token, source, cursor) do
    start = skip_trivia(source, cursor)
    ending = start + authored_length(token, binary_part(source, start, byte_size(source) - start))
    {start, ending, ending}
  end

  defp authored_length(%Token{type: type}, rest) when type in [:string, :string_interpolation],
    do: string_length(rest)

  defp authored_length(%Token{type: :char}, rest), do: quoted_length(rest, ?')
  defp authored_length(%Token{type: :regex}, rest), do: regex_length(rest)
  defp authored_length(%Token{type: type}, rest) when type in [:doc_comment, :line_comment], do: comment_length(rest)

  defp authored_length(%Token{type: :identifier}, <<?`, _::binary>> = rest), do: quoted_length(rest, ?`)

  defp authored_length(%Token{type: :identifier}, rest), do: take_while_bytes(rest, &identifier_byte?/1)
  defp authored_length(%Token{type: :hole}, rest), do: take_while_bytes(rest, &hole_byte?/1)
  defp authored_length(%Token{type: :atom}, rest), do: take_while_bytes(rest, &atom_byte?/1)

  defp authored_length(%Token{type: type}, rest) when type in [:integer, :float] do
    case Regex.run(~r/^(?:0[xX][0-9A-Fa-f_]+|0[bB][01_]+|[0-9][0-9_]*(?:\.[0-9_]+)?(?:[eE][+-]?[0-9]+)?)/, rest) do
      [number] -> byte_size(number)
      _ -> 1
    end
  end

  defp authored_length(%Token{type: :keyword, value: value}, _rest), do: value |> Atom.to_string() |> byte_size()
  defp authored_length(%Token{type: :bool, value: value}, _rest), do: value |> Atom.to_string() |> byte_size()
  defp authored_length(%Token{type: nil}, _rest), do: 3

  defp authored_length(%Token{value: value}, _rest) when is_binary(value), do: byte_size(value)
  defp authored_length(%Token{value: value}, _rest) when is_atom(value), do: value |> Atom.to_string() |> byte_size()
  defp authored_length(_token, _rest), do: 1

  defp quoted_length(<<?', ?', ?', _::binary>>, ?'), do: 3

  defp quoted_length(<<delimiter, tail::binary>>, delimiter),
    do: 1 + scan_quoted(tail, delimiter, 0, false)

  defp quoted_length(rest, _delimiter), do: min(1, byte_size(rest))

  defp scan_quoted(<<>>, _delimiter, consumed, _escaped), do: consumed

  defp scan_quoted(<<_byte, tail::binary>>, delimiter, consumed, true),
    do: scan_quoted(tail, delimiter, consumed + 1, false)

  defp scan_quoted(<<?\\, tail::binary>>, delimiter, consumed, false),
    do: scan_quoted(tail, delimiter, consumed + 1, true)

  defp scan_quoted(<<byte, _tail::binary>>, delimiter, consumed, false) when byte == delimiter,
    do: consumed + 1

  defp scan_quoted(<<_byte, tail::binary>>, delimiter, consumed, false),
    do: scan_quoted(tail, delimiter, consumed + 1, false)

  defp string_length(<<?", tail::binary>>), do: 1 + scan_string(tail, 0, false, 0)
  defp string_length(rest), do: min(1, byte_size(rest))

  defp scan_string(<<>>, consumed, _escaped, _interpolation_depth), do: consumed
  defp scan_string(<<_byte, tail::binary>>, consumed, true, depth), do: scan_string(tail, consumed + 1, false, depth)
  defp scan_string(<<?\\, tail::binary>>, consumed, false, depth), do: scan_string(tail, consumed + 1, true, depth)
  defp scan_string(<<?", _tail::binary>>, consumed, false, 0), do: consumed + 1

  defp scan_string(<<?#, ?{, tail::binary>>, consumed, false, 0),
    do: scan_string(tail, consumed + 2, false, 1)

  defp scan_string(<<?{, tail::binary>>, consumed, false, depth) when depth > 0,
    do: scan_string(tail, consumed + 1, false, depth + 1)

  defp scan_string(<<?}, tail::binary>>, consumed, false, depth) when depth > 0,
    do: scan_string(tail, consumed + 1, false, depth - 1)

  defp scan_string(<<?", _::binary>> = rest, consumed, false, depth) when depth > 0 do
    inner_length = quoted_length(rest, ?")
    tail = binary_part(rest, inner_length, byte_size(rest) - inner_length)
    scan_string(tail, consumed + inner_length, false, depth)
  end

  defp scan_string(<<_byte, tail::binary>>, consumed, false, depth),
    do: scan_string(tail, consumed + 1, false, depth)

  defp regex_length(<<?/, tail::binary>>) do
    case scan_regex_length(tail, 1, false) do
      {length, flags} -> length + take_while_bytes(flags, &regex_flag?/1)
      :unterminated -> 1
    end
  end

  defp regex_length(_rest), do: 1

  defp scan_regex_length(<<>>, _consumed, _escaped), do: :unterminated

  defp scan_regex_length(<<_byte, tail::binary>>, consumed, true),
    do: scan_regex_length(tail, consumed + 1, false)

  defp scan_regex_length(<<?\\, tail::binary>>, consumed, false),
    do: scan_regex_length(tail, consumed + 1, true)

  defp scan_regex_length(<<?/, tail::binary>>, consumed, false),
    do: {consumed + 1, tail}

  defp scan_regex_length(<<_byte, tail::binary>>, consumed, false),
    do: scan_regex_length(tail, consumed + 1, false)

  defp comment_length(rest) do
    if String.starts_with?(rest, "###") do
      case :binary.matches(rest, "###") do
        [{0, 3}, {closing, 3} | _] -> closing + 3
        _ -> byte_size(rest)
      end
    else
      case :binary.match(rest, "\n") do
        {length, 1} -> length
        :nomatch -> byte_size(rest)
      end
    end
  end

  defp skip_trivia(source, cursor) when cursor >= byte_size(source), do: byte_size(source)

  defp skip_trivia(source, cursor) do
    case :binary.at(source, cursor) do
      byte when byte in [?\s, ?\t, ?\r, ?\n] -> skip_trivia(source, cursor + 1)
      ?# -> skip_trivia(source, skip_comment(source, cursor))
      _ -> cursor
    end
  end

  defp skip_space_only(source, cursor) when cursor >= byte_size(source), do: byte_size(source)

  defp skip_space_only(source, cursor) do
    case :binary.at(source, cursor) do
      byte when byte in [?\s, ?\t, ?\r] -> skip_space_only(source, cursor + 1)
      _ -> cursor
    end
  end

  defp skip_comment(source, cursor) do
    rest = binary_part(source, cursor, byte_size(source) - cursor)
    cursor + comment_length(rest)
  end

  defp find_byte(source, cursor, _byte) when cursor >= byte_size(source), do: byte_size(source)

  defp find_byte(source, cursor, byte),
    do: if(:binary.at(source, cursor) == byte, do: cursor, else: find_byte(source, cursor + 1, byte))

  defp find_sequence_end(source, cursor, sequence) do
    rest = binary_part(source, cursor, byte_size(source) - cursor)

    case :binary.match(rest, sequence) do
      {offset, length} -> cursor + offset + length
      :nomatch -> cursor
    end
  end

  defp take_while_bytes(binary, predicate), do: take_while_bytes(binary, predicate, 0)

  defp take_while_bytes(<<byte, tail::binary>>, predicate, count),
    do: if(predicate.(byte), do: take_while_bytes(tail, predicate, count + 1), else: count)

  defp take_while_bytes(<<>>, _predicate, count), do: count

  defp identifier_byte?(byte), do: byte in ?a..?z or byte in ?A..?Z or byte in ?0..?9 or byte in [?_, ?$, ??]
  defp hole_byte?(byte), do: identifier_byte?(byte) or byte == ??
  defp atom_byte?(byte), do: identifier_byte?(byte) or byte in [?:, ?!]
end
