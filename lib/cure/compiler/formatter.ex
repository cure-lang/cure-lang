defmodule Cure.Compiler.Formatter do
  alias Cure.MetaAST.Metadata

  @moduledoc ~S"""
  Safe, source-preserving formatter for Cure source files.

  Unlike `Cure.Compiler.Printer`, which rewrites a buffer from its AST
  (and therefore loses plain `#` comments and any non-canonical
  whitespace), this formatter operates directly on the source text.
  It applies a small, fixed set of byte-level transformations whose
  effect on the lexer/parser output is provably a no-op, and validates
  every run by re-parsing the result against the original AST before
  returning.

  ## Passes

    1. **Line endings.** `\r\n` and lone `\r` are rewritten to `\n`.
    2. **Trailing whitespace.** Horizontal whitespace at the end of a
       line is stripped, outside protected spans.
    3. **Tab-to-space.** Leading tab characters in a line's indentation
       are expanded to two spaces. Cure's lexer treats tabs as a hard
       error, so this turns an otherwise-unparseable file into a
       parseable one without changing any token's identity.
    4. **Blank-line collapsing.** Runs of two or more consecutive blank
       lines are collapsed to a single blank line, outside protected
       spans.
    5. **Operator spacing.** A fixed set of unambiguously binary
       operators is rewritten to have exactly one space on each side,
       outside protected spans.
    6. **Final newline.** The buffer is guaranteed to end with exactly
       one `\n`.

  ## Protected spans

  Protected spans are byte ranges that must not be modified by any
  pass. They are identified by a dedicated scanner (not the full
  lexer, so that even unparseable buffers can be formatted) and cover:

    * `"..."` string literals (including `#{...}` interpolation),
    * `'...'` character literals,
    * `/.../flags` regex literals,
    * `## ...` single-line doc comments,
    * `### ... ###` fenced multi-line doc comments.

  Plain `# ...` line comments are protected from operator-spacing but
  not from the whitespace passes, because every byte they contain is
  discarded by the lexer.

  ## Round-trip safety

  After applying the passes, the formatter re-tokenises and re-parses
  the result. It requires that the formatted buffer produces an AST
  structurally equal to the original (modulo position metadata). If
  the original did not parse but the formatted version does (the
  tab-fix case), the formatted buffer is accepted because it strictly
  improves the file. Otherwise the formatter returns the original
  source unchanged.
  """

  alias Cure.Compiler.{Lexer, Parser}

  # -- Public API --------------------------------------------------------------

  @doc """
  Format a Cure source string.

  Returns `{:ok, formatted}` if the result is safe to apply, or
  `{:ok, source}` if any pass would break semantics. The function
  never returns an error tuple for well-formed binary input; it
  degrades to the original source instead so that callers can treat
  the formatter as "best effort, never destructive".
  """
  @spec format(binary(), keyword()) :: {:ok, binary()}
  def format(source, _opts \\ []) when is_binary(source) do
    try do
      stage0 = normalize_line_endings(source)
      stage1 = strip_trailing_whitespace(stage0, scan_spans(stage0))
      stage2 = expand_leading_tabs(stage1, scan_spans(stage1))
      stage3 = collapse_blank_lines(stage2, scan_spans(stage2))
      stage4 = apply_operator_spacing(stage3)
      formatted = ensure_final_newline(stage4)

      if verify(source, formatted) do
        {:ok, formatted}
      else
        {:ok, source}
      end
    rescue
      _ -> {:ok, source}
    catch
      _, _ -> {:ok, source}
    end
  end

  @doc """
  Format a buffer and return an LSP `TextEdit` list.

  Returns an empty list when the formatter produces no change.
  Otherwise returns a single whole-document edit.
  """
  @spec format_to_edits(binary()) :: [map()]
  def format_to_edits(source) when is_binary(source) do
    {:ok, formatted} = format(source)

    if formatted == source do
      []
    else
      [whole_document_edit(source, formatted)]
    end
  end

  @doc """
  Algebra-based formatter (v0.20.0, opt-in behind `cure fmt --algebra`).

  Lexes the source with comment preservation enabled, parses it into a
  comment-aware AST, renders that AST through `Cure.Compiler.AlgebraFormatter`
  (which delegates per-node rendering to `Cure.Compiler.Printer`), and
  verifies round-trip safety by re-parsing the result and comparing
  ASTs modulo comment placement and position metadata.

  Returns `{:ok, formatted}` when the rewrite is safe; returns
  `{:ok, source}` unchanged when verification fails, so callers can
  treat the algebra formatter as non-destructive.
  """
  @spec format_algebra(binary(), keyword()) :: {:ok, binary()}
  def format_algebra(source, opts \\ []) when is_binary(source) do
    try do
      with {:ok, tokens} <-
             Cure.Compiler.Lexer.tokenize(source, emit_events: false, preserve_comments: true),
           {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, emit_events: false),
           formatted when is_binary(formatted) <-
             Cure.Compiler.AlgebraFormatter.format(ast, opts),
           true <- verify_algebra(source, formatted) do
        {:ok, formatted}
      else
        _ -> {:ok, source}
      end
    rescue
      _ -> {:ok, source}
    catch
      _, _ -> {:ok, source}
    end
  end

  # Comment-aware equivalence: the algebra formatter may re-flow
  # comments but must not change the AST's structural content. We
  # strip comment nodes from both sides before comparing.
  defp verify_algebra(original, formatted) do
    with {:ok, a} <- parse(original),
         {:ok, b} <- parse(formatted) do
      strip(strip_comments(a)) == strip(strip_comments(b))
    else
      _ -> false
    end
  end

  defp strip_comments({type, meta, children}) when is_list(meta) and is_list(children) do
    children =
      Enum.reject(children, fn
        {:comment, _, _} -> true
        _ -> false
      end)

    {type, meta, Enum.map(children, &strip_comments/1)}
  end

  defp strip_comments({type, meta, child}) when is_list(meta), do: {type, meta, child}
  defp strip_comments(other), do: other

  # -- Line endings ------------------------------------------------------------

  defp normalize_line_endings(source) do
    source
    |> String.replace("\r\n", "\n")
    |> String.replace("\r", "\n")
  end

  # -- Whitespace passes -------------------------------------------------------

  # Strip trailing horizontal whitespace on every line, except when the
  # trimmed bytes would overlap a protected span that forbids
  # whitespace modification (i.e. strings, chars, regex, doc comments).
  # Line comments (`# ...`) are whitespace-permissive: we may trim
  # trailing spaces that sit within their body because the lexer
  # discards them anyway.
  defp strip_trailing_whitespace(source, spans) do
    hard = Enum.filter(spans, &hard_protected?/1)

    source
    |> split_lines_with_offsets()
    |> Enum.map_join("", fn {start, line, newline} ->
      stop = start + byte_size(line)

      if overlaps_any?(hard, start, stop) do
        line <> newline
      else
        trim_trailing_horizontal(line) <> newline
      end
    end)
  end

  defp trim_trailing_horizontal(line) do
    line
    |> String.reverse()
    |> String.trim_leading(" ")
    |> String.trim_leading("\t")
    |> then(fn s ->
      # We only want to trim runs of space/tab, no other characters.
      # `String.trim_leading/2` only accepts one char at a time in the
      # single-char form we used above; do it iteratively until stable.
      trim_trailing_horizontal_reversed(s)
    end)
    |> String.reverse()
  end

  defp trim_trailing_horizontal_reversed(s) do
    trimmed = s |> String.trim_leading(" ") |> String.trim_leading("\t")
    if trimmed == s, do: s, else: trim_trailing_horizontal_reversed(trimmed)
  end

  # Expand tab characters in the indentation (leading whitespace) of
  # each line to two spaces. Tabs in trailing positions of code lines
  # are already removed by the trailing-whitespace pass; tabs inside
  # code (never emitted by the lexer, but a user might type one) are
  # left untouched because the lexer rejects them as invalid and our
  # verify step will catch any mistake.
  defp expand_leading_tabs(source, spans) do
    hard = Enum.filter(spans, &hard_protected?/1)

    source
    |> split_lines_with_offsets()
    |> Enum.map_join("", fn {start, line, newline} ->
      stop = start + byte_size(line)

      if overlaps_any?(hard, start, stop) do
        line <> newline
      else
        expand_tabs_in_indent(line) <> newline
      end
    end)
  end

  defp expand_tabs_in_indent(line) do
    {indent, rest} = split_leading_whitespace(line)
    new_indent = String.replace(indent, "\t", "  ")
    new_indent <> rest
  end

  defp split_leading_whitespace(line) do
    split_leading_whitespace(line, <<>>)
  end

  defp split_leading_whitespace(<<c, rest::binary>>, acc) when c in [?\s, ?\t] do
    split_leading_whitespace(rest, acc <> <<c>>)
  end

  defp split_leading_whitespace(rest, acc), do: {acc, rest}

  # Collapse runs of two or more consecutive blank lines to a single
  # blank line, skipping any run that starts inside (or would remove)
  # a hard-protected span.
  defp collapse_blank_lines(source, spans) do
    hard = Enum.filter(spans, &hard_protected?/1)
    lines = split_lines_with_offsets(source)

    lines
    |> Enum.reduce({[], 0}, fn {start, line, _newline} = row, {acc, blanks} ->
      blank? = blank_line?(line)
      inside_hard? = point_inside_any?(hard, start)

      cond do
        inside_hard? ->
          {[row | acc], 0}

        blank? and blanks >= 1 ->
          # Skip this extra blank line.
          {acc, blanks + 1}

        blank? ->
          {[row | acc], 1}

        true ->
          {[row | acc], 0}
      end
    end)
    |> elem(0)
    |> Enum.reverse()
    |> Enum.map_join("", fn {_, line, newline} -> line <> newline end)
  end

  defp blank_line?(line) do
    line
    |> String.replace(~r/[ \t]+/, "")
    |> Kernel.==("")
  end

  # -- Operator spacing --------------------------------------------------------

  # Whitelisted binary operators, ordered so that longer strings are
  # matched before shorter ones. Each entry is `{text, kind}` where
  # `kind` is `:always_binary` (always gets a space on both sides) or
  # `:context_binary` (space only when heuristics decide the occurrence
  # is binary rather than unary/variadic/etc).
  @operator_table [
    # Melquiades operator (always binary). `<-|` is three bytes, so it
    # must come before the two-byte `<` entries to match first. The
    # unicode `✉` (U+2709 ENVELOPE) encodes to three bytes in UTF-8.
    {"<-|", :always_binary},
    {"✉", :always_binary},
    # comparisons / other two-char operators
    {"==", :always_binary},
    {"!=", :always_binary},
    {"<=", :always_binary},
    {">=", :always_binary},
    {"<>", :always_binary},
    {"|>", :always_binary},
    {"->", :always_binary},
    {"=>", :always_binary},
    # single-char unambiguous binary operators
    {"=", :assign_binary},
    {"+", :plus_binary},
    {"-", :minus_binary},
    {"*", :star_binary},
    {"/", :slash_binary},
    {"%", :percent_binary}
  ]

  defp apply_operator_spacing(source) do
    spans = scan_spans(source)
    ops_blocked = Enum.filter(spans, &op_blocked?/1)

    ops = collect_operator_positions(source, ops_blocked)

    apply_operator_edits(source, ops)
  end

  defp collect_operator_positions(source, ops_blocked) do
    do_collect_ops(source, 0, byte_size(source), ops_blocked, [])
    |> Enum.reverse()
  end

  defp do_collect_ops(_source, pos, size, _blocked, acc) when pos >= size do
    acc
  end

  defp do_collect_ops(source, pos, size, blocked, acc) do
    # Skip over blocked spans.
    case block_containing(blocked, pos) do
      {_, stop} ->
        do_collect_ops(source, stop, size, blocked, acc)

      nil ->
        case match_operator(source, pos, size) do
          {text, kind, len} ->
            case classify_operator(source, pos, len, text, kind) do
              :skip ->
                do_collect_ops(source, pos + 1, size, blocked, acc)

              :binary ->
                do_collect_ops(source, pos + len, size, blocked, [{pos, len, text} | acc])
            end

          :none ->
            do_collect_ops(source, pos + 1, size, blocked, acc)
        end
    end
  end

  defp match_operator(source, pos, size) do
    Enum.reduce_while(@operator_table, :none, fn {text, kind}, _ ->
      len = byte_size(text)

      if pos + len <= size and binary_part(source, pos, len) == text do
        {:halt, {text, kind, len}}
      else
        {:cont, :none}
      end
    end)
  end

  # Decide whether a matched operator should be rewritten.
  #
  # For `:always_binary` operators we always act. For context-sensitive
  # ones we peek at the surrounding byte to weed out false positives:
  # `=` must not be the first `=` of `==`, `!=`, `<=`, `>=`, `=>`, or a
  # trailing byte of some other operator run, `/` must not be part of a
  # regex (protected span would have already blocked that), `%` must not
  # be the start of `%[` or `%{`.
  defp classify_operator(_source, _pos, _len, _text, :always_binary), do: :binary

  defp classify_operator(source, pos, _len, _text, :assign_binary) do
    # Reject if next byte makes this part of a longer op that we
    # didn't match (shouldn't happen because the longer ops come
    # first) or if the prev byte makes this the tail of an operator run.
    next = byte_at(source, pos + 1)

    cond do
      next == ?= -> :skip
      next == ?> -> :skip
      byte_at(source, pos - 1) in [?+, ?-, ?*, ?/, ?!, ?<, ?>, ?=] -> :skip
      true -> :binary
    end
  end

  defp classify_operator(source, pos, _len, _text, :slash_binary) do
    # `/` that starts a regex body is already inside a protected
    # span, so we should not be called. Guard anyway.
    prev = prev_nonspace_byte(source, pos)
    next = byte_at(source, pos + 1)

    cond do
      next == ?= -> :skip
      prev == nil -> :skip
      prev in [?(, ?,, ?\n, ?[, ?{, ?=, ?>, ?<, ?+, ?-, ?*, ?/] -> :skip
      true -> :binary
    end
  end

  defp classify_operator(source, pos, _len, _text, :percent_binary) do
    # Don't touch `%[` tuple or `%{` map sigils.
    next = byte_at(source, pos + 1)
    if next in [?[, ?{], do: :skip, else: :binary
  end

  defp classify_operator(source, pos, _len, _text, :plus_binary) do
    # `+` could appear inside a number's scientific exponent (1e+3). The
    # protected-span scanner does not treat numbers as protected, so we
    # have to detect the exponent case manually.
    prev = byte_at(source, pos - 1)
    next = byte_at(source, pos + 1)

    cond do
      prev in [?e, ?E] and digit?(byte_at(source, pos - 2)) -> :skip
      next == ?= -> :skip
      binary_context?(source, pos) -> :binary
      true -> :skip
    end
  end

  defp classify_operator(source, pos, _len, _text, :minus_binary) do
    prev = byte_at(source, pos - 1)
    next = byte_at(source, pos + 1)

    cond do
      # Transition-shaped punctuation `--event-->` or `-->`: the lexer eats
      # these whole, but our byte scan can land on one of them. Skip
      # if we see `--` either starting here or immediately before.
      next == ?- -> :skip
      prev == ?- -> :skip
      # Exponent sign inside a number: 1e-3.
      prev in [?e, ?E] and digit?(byte_at(source, pos - 2)) -> :skip
      # `->` already matched above, but guard anyway.
      next == ?> -> :skip
      next == ?= -> :skip
      binary_context?(source, pos) -> :binary
      true -> :skip
    end
  end

  defp classify_operator(source, pos, _len, _text, :star_binary) do
    prev = byte_at(source, pos - 1)
    next = byte_at(source, pos + 1)

    cond do
      # `**kwargs` / `*args` in a parameter list: previous non-space
      # byte is `(` or `,`.
      next == ?* -> :skip
      prev == ?* -> :skip
      next == ?= -> :skip
      variadic_context?(source, pos) -> :skip
      binary_context?(source, pos) -> :binary
      true -> :skip
    end
  end

  defp digit?(b), do: is_integer(b) and b in ?0..?9

  # An operator byte is in a binary context when the previous
  # non-whitespace byte on the same line would terminate an expression
  # (identifier, closing bracket, number, string/char close, or a
  # question/bang suffix on an identifier). If the preceding token is
  # an expression-introducing keyword (`return`, `throw`, `if`, ...),
  # it counts as unary context even though the last byte is a letter.
  defp binary_context?(source, pos) do
    case prev_nonspace_byte(source, pos) do
      nil ->
        false

      ?\n ->
        false

      b ->
        cond do
          b in [?), ?], ?}, ?", ?', ??, ?!] -> true
          digit?(b) -> true
          ident_char?(b) -> not preceding_word_is_unary_keyword?(source, pos)
          true -> false
        end
    end
  end

  # Keywords after which a following `-` or `*` would be unary
  # (expression-introducing) rather than binary.
  @unary_intro_keywords ~w(
    return throw yield spawn send
    if elif then else when where
    for in do after match
    and or not
    let use as
  )

  defp preceding_word_is_unary_keyword?(source, pos) do
    word = read_preceding_word(source, pos)
    word in @unary_intro_keywords
  end

  defp read_preceding_word(source, pos) do
    # Walk back past whitespace then collect identifier-ish bytes.
    ws_end = skip_ws_backward(source, pos - 1)
    word_end = ws_end
    word_start = collect_ident_start(source, word_end)

    if word_start > word_end do
      ""
    else
      binary_part(source, word_start, word_end - word_start + 1)
    end
  end

  defp skip_ws_backward(_source, pos) when pos < 0, do: -1

  defp skip_ws_backward(source, pos) do
    case :binary.at(source, pos) do
      c when c in [?\s, ?\t] -> skip_ws_backward(source, pos - 1)
      _ -> pos
    end
  end

  defp collect_ident_start(_source, pos) when pos < 0, do: 0

  defp collect_ident_start(source, pos) do
    case :binary.at(source, pos) do
      b when b in ?a..?z or b in ?A..?Z or b == ?_ or b in ?0..?9 ->
        if pos == 0, do: 0, else: collect_ident_start(source, pos - 1)

      _ ->
        pos + 1
    end
  end

  defp variadic_context?(source, pos) do
    case prev_nonspace_byte(source, pos) do
      ?( -> true
      ?, -> true
      _ -> false
    end
  end

  defp ident_char?(b) when is_integer(b) do
    b in ?a..?z or b in ?A..?Z or b == ?_
  end

  defp apply_operator_edits(source, ops) do
    ops
    |> Enum.sort_by(fn {pos, _, _} -> pos end, :desc)
    |> Enum.reduce(source, fn {pos, len, _text}, src ->
      rewrite_operator_at(src, pos, len)
    end)
  end

  defp rewrite_operator_at(source, pos, len) do
    size = byte_size(source)
    {left_start, left_ws} = left_ws_range(source, pos)
    {right_stop, right_ws} = right_ws_range(source, pos + len, size)

    before_ws = binary_part(source, 0, left_start)
    op = binary_part(source, pos, len)
    after_ws = binary_part(source, right_stop, size - right_stop)

    new_left = normalize_left_ws(source, left_start, pos, left_ws)
    new_right = normalize_right_ws(source, pos + len, right_stop, size, right_ws)

    before_ws <> new_left <> op <> new_right <> after_ws
  end

  defp left_ws_range(source, pos) do
    do_left_ws(source, pos, 0)
  end

  defp do_left_ws(_source, 0, count), do: {0, count}

  defp do_left_ws(source, pos, count) do
    case :binary.at(source, pos - 1) do
      c when c in [?\s, ?\t] -> do_left_ws(source, pos - 1, count + 1)
      _ -> {pos, count}
    end
  end

  defp right_ws_range(source, pos, size) do
    do_right_ws(source, pos, size, 0)
  end

  defp do_right_ws(_source, pos, size, count) when pos >= size, do: {pos, count}

  defp do_right_ws(source, pos, size, count) do
    case :binary.at(source, pos) do
      c when c in [?\s, ?\t] -> do_right_ws(source, pos + 1, size, count + 1)
      _ -> {pos, count}
    end
  end

  defp normalize_left_ws(source, left_start, _pos, _ws_count) do
    prev = if left_start == 0, do: nil, else: :binary.at(source, left_start - 1)

    cond do
      # Operator sits at the very start of the buffer.
      prev == nil -> ""
      # Operator at the very start of a line (only whitespace before).
      prev == ?\n -> ""
      # Otherwise: exactly one space.
      true -> " "
    end
  end

  defp normalize_right_ws(source, _end_pos, right_stop, size, _ws_count) do
    next = if right_stop >= size, do: nil, else: :binary.at(source, right_stop)

    cond do
      # End of buffer: no space.
      next == nil -> ""
      # End of line: keep the newline, no space before it.
      next == ?\n -> ""
      # Otherwise: exactly one space.
      true -> " "
    end
  end

  # -- Final newline -----------------------------------------------------------

  defp ensure_final_newline(""), do: ""

  defp ensure_final_newline(source) do
    trimmed = String.trim_trailing(source, "\n")
    trimmed <> "\n"
  end

  # -- Span scanner ------------------------------------------------------------

  # Returns a sorted list of `{kind, start, stop}` tuples, where
  # `start` is inclusive and `stop` is exclusive, and `kind` is one
  # of `:string`, `:char`, `:regex`, `:doc_single`, `:doc_fenced`,
  # or `:line_comment`.
  defp scan_spans(source) do
    do_scan(source, 0, byte_size(source), [])
    |> Enum.reverse()
  end

  defp do_scan(_source, pos, size, acc) when pos >= size, do: acc

  defp do_scan(source, pos, size, acc) do
    case :binary.at(source, pos) do
      ?" ->
        stop = scan_string(source, pos + 1, size)
        do_scan(source, stop, size, [{:string, pos, stop} | acc])

      ?' ->
        stop = scan_char(source, pos + 1, size)
        do_scan(source, stop, size, [{:char, pos, stop} | acc])

      ?/ ->
        if regex_start?(source, pos) do
          stop = scan_regex(source, pos + 1, size)
          do_scan(source, stop, size, [{:regex, pos, stop} | acc])
        else
          do_scan(source, pos + 1, size, acc)
        end

      ?# ->
        case {byte_at(source, pos + 1), byte_at(source, pos + 2)} do
          {?#, ?#} ->
            stop = scan_fenced_doc(source, pos + 3, size)
            do_scan(source, stop, size, [{:doc_fenced, pos, stop} | acc])

          {?#, _} ->
            stop = scan_to_newline(source, pos + 2, size)
            do_scan(source, stop, size, [{:doc_single, pos, stop} | acc])

          _ ->
            stop = scan_to_newline(source, pos + 1, size)
            do_scan(source, stop, size, [{:line_comment, pos, stop} | acc])
        end

      _ ->
        do_scan(source, pos + 1, size, acc)
    end
  end

  defp scan_string(_source, pos, size) when pos >= size, do: size

  defp scan_string(source, pos, size) do
    case :binary.at(source, pos) do
      ?" ->
        pos + 1

      ?\\ ->
        # Skip the escaped character.
        if pos + 1 < size, do: scan_string(source, pos + 2, size), else: size

      ?# ->
        if byte_at(source, pos + 1) == ?{ do
          inner = scan_balanced_braces(source, pos + 2, size, 0)
          scan_string(source, inner, size)
        else
          scan_string(source, pos + 1, size)
        end

      _ ->
        scan_string(source, pos + 1, size)
    end
  end

  # Walk bytes from `pos`, which is just past a `#{` opener inside a
  # string, until the matching `}` is consumed. Nested braces are
  # tracked by `depth`.
  defp scan_balanced_braces(_source, pos, size, _depth) when pos >= size, do: size

  defp scan_balanced_braces(source, pos, size, depth) do
    case :binary.at(source, pos) do
      ?{ -> scan_balanced_braces(source, pos + 1, size, depth + 1)
      ?} when depth == 0 -> pos + 1
      ?} -> scan_balanced_braces(source, pos + 1, size, depth - 1)
      ?" -> scan_balanced_braces(source, scan_string(source, pos + 1, size), size, depth)
      ?\\ -> scan_balanced_braces(source, min(pos + 2, size), size, depth)
      _ -> scan_balanced_braces(source, pos + 1, size, depth)
    end
  end

  defp scan_char(_source, pos, size) when pos >= size, do: size

  defp scan_char(source, pos, size) do
    case :binary.at(source, pos) do
      ?\\ ->
        if pos + 2 < size and :binary.at(source, pos + 2) == ?' do
          pos + 3
        else
          min(pos + 3, size)
        end

      _ ->
        if pos + 1 < size and :binary.at(source, pos + 1) == ?' do
          pos + 2
        else
          # Malformed char literal: swallow one byte and stop.
          pos + 1
        end
    end
  end

  defp scan_regex(_source, pos, size) when pos >= size, do: size

  defp scan_regex(source, pos, size) do
    case :binary.at(source, pos) do
      ?/ -> scan_regex_flags(source, pos + 1, size)
      ?\\ -> if pos + 1 < size, do: scan_regex(source, pos + 2, size), else: size
      _ -> scan_regex(source, pos + 1, size)
    end
  end

  defp scan_regex_flags(_source, pos, size) when pos >= size, do: size

  defp scan_regex_flags(source, pos, size) do
    case :binary.at(source, pos) do
      c when c in [?i, ?m, ?s, ?x, ?u, ?f, ?r, ?U, ?E] ->
        scan_regex_flags(source, pos + 1, size)

      _ ->
        pos
    end
  end

  defp regex_start?(_source, 0), do: true

  defp regex_start?(source, pos) do
    previous = previous_nonspace(source, pos - 1)
    previous in [?=, ?(, ?[, ?{, ?,, ?:, ?\n]
  end

  defp previous_nonspace(_source, pos) when pos < 0, do: nil

  defp previous_nonspace(source, pos) do
    case :binary.at(source, pos) do
      c when c in [?s, ?\t, ?\r] -> previous_nonspace(source, pos - 1)
      c -> c
    end
  end

  defp scan_to_newline(_source, pos, size) when pos >= size, do: size

  defp scan_to_newline(source, pos, size) do
    case :binary.at(source, pos) do
      ?\n -> pos
      _ -> scan_to_newline(source, pos + 1, size)
    end
  end

  defp scan_fenced_doc(source, pos, size) do
    # `pos` is just past the opening `###`. The close is a line of
    # the shape `<ws>* ### <anything>* <nl|eof>`.
    do_scan_fenced(source, pos, size)
  end

  defp do_scan_fenced(_source, pos, size) when pos >= size, do: size

  defp do_scan_fenced(source, pos, size) do
    line_start = pos
    {nl_pos, _} = find_newline(source, pos, size)
    line_stop = nl_pos

    if fenced_close?(source, line_start, line_stop) do
      if nl_pos < size, do: nl_pos + 1, else: size
    else
      if nl_pos < size, do: do_scan_fenced(source, nl_pos + 1, size), else: size
    end
  end

  defp find_newline(source, pos, size) do
    do_find_newline(source, pos, size)
  end

  defp do_find_newline(_source, pos, size) when pos >= size, do: {size, size}

  defp do_find_newline(source, pos, size) do
    case :binary.at(source, pos) do
      ?\n -> {pos, pos}
      _ -> do_find_newline(source, pos + 1, size)
    end
  end

  defp fenced_close?(source, line_start, line_stop) do
    {content_start, _} = drop_leading_spaces(source, line_start, line_stop)

    content_start + 2 < line_stop and
      :binary.at(source, content_start) == ?# and
      :binary.at(source, content_start + 1) == ?# and
      :binary.at(source, content_start + 2) == ?#
  end

  defp drop_leading_spaces(_source, pos, stop) when pos >= stop, do: {pos, 0}

  defp drop_leading_spaces(source, pos, stop) do
    case :binary.at(source, pos) do
      ?\s -> drop_leading_spaces(source, pos + 1, stop)
      _ -> {pos, 0}
    end
  end

  # -- Span helpers ------------------------------------------------------------

  # "Hard" protected spans are never modified by any pass. Line
  # comments are "soft" (only operator spacing is blocked there).
  defp hard_protected?({kind, _, _}),
    do: kind in [:string, :char, :regex, :doc_single, :doc_fenced]

  defp op_blocked?({kind, _, _}),
    do: kind in [:string, :char, :regex, :doc_single, :doc_fenced, :line_comment]

  defp overlaps_any?(spans, start, stop) do
    Enum.any?(spans, fn {_, s, e} -> s < stop and start < e end)
  end

  defp point_inside_any?(spans, point) do
    Enum.any?(spans, fn {_, s, e} -> s <= point and point < e end)
  end

  defp block_containing(spans, pos) do
    Enum.find_value(spans, fn {_, s, e} ->
      if s <= pos and pos < e, do: {s, e}, else: nil
    end)
  end

  # -- Low-level helpers -------------------------------------------------------

  defp byte_at(source, pos) do
    cond do
      pos < 0 -> nil
      pos >= byte_size(source) -> nil
      true -> :binary.at(source, pos)
    end
  end

  defp prev_nonspace_byte(source, pos) do
    do_prev_nonspace(source, pos - 1)
  end

  defp do_prev_nonspace(_source, pos) when pos < 0, do: nil

  defp do_prev_nonspace(source, pos) do
    case :binary.at(source, pos) do
      c when c in [?\s, ?\t] -> do_prev_nonspace(source, pos - 1)
      c -> c
    end
  end

  # Split a source buffer into a list of `{line_start_offset, line_text_without_nl, newline_suffix}`
  # tuples. The newline suffix is either "\n" or "" (for the final line
  # if it does not end with a newline).
  defp split_lines_with_offsets(source) do
    do_split_lines(source, 0, 0, byte_size(source), [])
    |> Enum.reverse()
  end

  defp do_split_lines(source, line_start, pos, size, acc) when pos >= size do
    if line_start >= size do
      acc
    else
      line = binary_part(source, line_start, size - line_start)
      [{line_start, line, ""} | acc]
    end
  end

  defp do_split_lines(source, line_start, pos, size, acc) do
    case :binary.at(source, pos) do
      ?\n ->
        line = binary_part(source, line_start, pos - line_start)
        do_split_lines(source, pos + 1, pos + 1, size, [{line_start, line, "\n"} | acc])

      _ ->
        do_split_lines(source, line_start, pos + 1, size, acc)
    end
  end

  # -- Round-trip verification -------------------------------------------------

  defp verify(original, formatted) do
    original_result = parse(original)
    formatted_result = parse(formatted)

    case {original_result, formatted_result} do
      # Both parse: require structural AST equivalence.
      {{:ok, a}, {:ok, b}} -> ast_equivalent?(a, b)
      # Tab-fix case: original was unparseable, formatted parses.
      {{:error, _}, {:ok, _}} -> true
      # A working buffer must not be turned into a broken one.
      {{:ok, _}, {:error, _}} -> false
      # Neither parses: we have no AST to compare against, so
      # refuse to modify unparseable input rather than gamble.
      {{:error, _}, {:error, _}} -> false
    end
  end

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    else
      {:error, _} = err -> err
    end
  end

  # Compare two MetaAST trees ignoring position metadata.
  defp ast_equivalent?(a, b) do
    strip(a) == strip(b)
  end

  defp strip({type, meta, children}) when is_list(meta) do
    Metadata.strip_diagnostics({type, meta, children})
  end

  defp strip(other), do: Metadata.strip_diagnostics(other)

  # -- LSP edit helper ---------------------------------------------------------

  defp whole_document_edit(source, formatted) do
    {end_line, end_char} = end_position(source)

    %{
      "range" => %{
        "start" => %{"line" => 0, "character" => 0},
        "end" => %{"line" => end_line, "character" => end_char}
      },
      "newText" => formatted
    }
  end

  defp end_position(""), do: {0, 0}

  defp end_position(source) do
    lines = String.split(source, "\n")
    last_idx = length(lines) - 1
    last_line = List.last(lines)
    {last_idx, String.length(last_line)}
  end
end
