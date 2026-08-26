defmodule Cure.Diagnostic.Doc do
  @moduledoc """
  A small semantic document algebra for compiler diagnostics.

  Documents contain no terminal escape sequences. Layout is deterministic at
  an explicit display width and styling is introduced only by `ansi/2`.
  """

  @roles [
    :name,
    :type,
    :keyword,
    :expected,
    :observed,
    :addition,
    :removal,
    :banner,
    :error_marker,
    :warning_marker,
    :secondary_marker
  ]
  @default_width 80
  @default_tab_width 4

  @type role ::
          :name
          | :type
          | :keyword
          | :expected
          | :observed
          | :addition
          | :removal
          | :banner
          | :error_marker
          | :warning_marker
          | :secondary_marker
  @opaque t ::
            :empty
            | :line
            | :blank_line
            | {:text, String.t()}
            | {:concat, [t()]}
            | {:paragraph, [t()]}
            | {:stack, [t()]}
            | {:indent, non_neg_integer(), t()}
            | {:code, String.t()}
            | {:emphasis, role(), t()}
            | {:note, t()}
            | {:hint, t()}
            | {:bullet_list, [t()]}

  @type segment :: {String.t(), role() | nil}

  @spec empty() :: t()
  def empty, do: :empty

  @spec text(String.Chars.t()) :: t()
  def text(value), do: {:text, to_string(value)}

  @spec concat([t() | String.Chars.t()]) :: t()
  def concat(documents), do: {:concat, Enum.map(documents, &document/1)}

  @spec line() :: t()
  def line, do: :line

  @spec blank_line() :: t()
  def blank_line, do: :blank_line

  @spec paragraph(t() | String.Chars.t() | [t() | String.Chars.t()]) :: t()
  def paragraph(inlines) when is_list(inlines), do: {:paragraph, Enum.map(inlines, &document/1)}
  def paragraph(inline), do: {:paragraph, [document(inline)]}

  @spec stack([t() | String.Chars.t()]) :: t()
  def stack(blocks), do: {:stack, Enum.map(blocks, &document/1)}

  @spec indent(non_neg_integer(), t() | String.Chars.t()) :: t()
  def indent(columns, document) when is_integer(columns) and columns >= 0,
    do: {:indent, columns, document(document)}

  @spec code(String.Chars.t()) :: t()
  def code(source), do: {:code, to_string(source)}

  @spec emphasis(role(), t() | String.Chars.t()) :: t()
  def emphasis(role, document) when role in @roles, do: {:emphasis, role, document(document)}

  def emphasis(role, _document) do
    raise ArgumentError, "unknown diagnostic emphasis role: #{inspect(role)}"
  end

  @spec note(t() | String.Chars.t()) :: t()
  def note(document), do: {:note, document(document)}

  @spec hint(t() | String.Chars.t()) :: t()
  def hint(document), do: {:hint, document(document)}

  @spec bullet_list([t() | String.Chars.t()]) :: t()
  def bullet_list(items), do: {:bullet_list, Enum.map(items, &document/1)}

  @doc "Render a document without terminal styling."
  @spec plain(t(), keyword()) :: String.t()
  def plain(document, opts \\ []) do
    document
    |> layout(opts)
    |> Enum.map_join(fn {value, _role} -> value end)
  end

  @doc "Render a document with ANSI styling derived from semantic roles."
  @spec ansi(t(), keyword()) :: String.t()
  def ansi(document, opts \\ []) do
    document
    |> layout(opts)
    |> Enum.map_join(fn
      {value, nil} -> value
      {value, role} -> role_ansi(role) <> value <> IO.ANSI.reset()
    end)
  end

  @doc "Encode a document as stable semantic data for machine consumers."
  @spec to_map(t()) :: map()
  def to_map(:empty), do: %{"kind" => "empty"}
  def to_map(:line), do: %{"kind" => "line"}
  def to_map(:blank_line), do: %{"kind" => "blank_line"}
  def to_map({:text, value}), do: %{"kind" => "text", "text" => value}
  def to_map({:code, value}), do: %{"kind" => "code", "text" => value}

  def to_map({kind, documents}) when kind in [:concat, :paragraph, :stack, :bullet_list] do
    %{"kind" => Atom.to_string(kind), "children" => Enum.map(documents, &to_map/1)}
  end

  def to_map({:indent, columns, document}),
    do: %{"kind" => "indent", "columns" => columns, "document" => to_map(document)}

  def to_map({:emphasis, role, document}),
    do: %{"kind" => "emphasis", "role" => Atom.to_string(role), "document" => to_map(document)}

  def to_map({kind, document}) when kind in [:note, :hint],
    do: %{"kind" => Atom.to_string(kind), "document" => to_map(document)}

  @doc "Return terminal columns occupied by a string from a one-based column."
  @spec display_width(String.t(), pos_integer(), keyword()) :: non_neg_integer()
  def display_width(string, start_column \\ 1, opts \\ [])

  def display_width(string, start_column, opts)
      when is_binary(string) and is_integer(start_column) and start_column > 0 do
    tab_width = Keyword.get(opts, :tab_width, @default_tab_width)

    final_column =
      string
      |> String.graphemes()
      |> Enum.reduce(start_column, fn
        "\t", column -> column + tab_width - rem(column - 1, tab_width)
        grapheme, column -> column + grapheme_width(grapheme)
      end)

    final_column - start_column
  end

  defp document(:empty), do: :empty
  defp document(:line), do: :line
  defp document(:blank_line), do: :blank_line

  defp document({kind, _} = document)
       when kind in [:text, :concat, :paragraph, :stack, :code, :note, :hint, :bullet_list],
       do: document

  defp document({kind, _, _} = document) when kind in [:indent, :emphasis], do: document
  defp document(value), do: text(value)

  defp layout(document, opts) do
    width = Keyword.get(opts, :width, @default_width)
    tab_width = Keyword.get(opts, :tab_width, @default_tab_width)

    if not is_integer(width) or width < 1 do
      raise ArgumentError, "document width must be a positive integer"
    end

    render(document, %{width: width, tab_width: tab_width}, nil)
  end

  defp render(:empty, _opts, _role), do: []
  defp render(:line, _opts, _role), do: [{"\n", nil}]
  defp render(:blank_line, _opts, _role), do: [{"\n\n", nil}]
  defp render({:text, value}, _opts, role), do: [{value, role}]
  defp render({:code, value}, _opts, role), do: [{value, role}]

  defp render({:concat, documents}, opts, role) do
    Enum.flat_map(documents, &render(&1, opts, role))
  end

  defp render({:stack, documents}, opts, role) do
    documents
    |> Enum.map(&render(&1, opts, role))
    |> Enum.reject(&(&1 == []))
    |> intersperse([{"\n\n", nil}])
    |> List.flatten()
  end

  defp render({:paragraph, inlines}, opts, role) do
    inlines
    |> inline_segments(opts, role)
    |> wrap_segments(opts.width, opts.tab_width)
  end

  defp render({:indent, columns, document}, opts, role) do
    document
    |> render(%{opts | width: max(1, opts.width - columns)}, role)
    |> prefix_lines(String.duplicate(" ", columns))
  end

  defp render({:emphasis, emphasized_role, document}, opts, _role),
    do: render(document, opts, emphasized_role)

  defp render({:note, document}, opts, role), do: prefixed_block("Note: ", document, opts, role)
  defp render({:hint, document}, opts, role), do: prefixed_block("Hint: ", document, opts, role)

  defp render({:bullet_list, items}, opts, role) do
    items
    |> Enum.map(fn item ->
      rendered = render(item, %{opts | width: max(1, opts.width - 2)}, role)
      rendered |> prefix_lines("- ", "  ")
    end)
    |> intersperse([{"\n", nil}])
    |> List.flatten()
  end

  defp inline_segments(inlines, opts, role) do
    inlines
    |> Enum.map(&render(&1, opts, role))
    |> Enum.reduce([], fn segments, acc ->
      segments = normalize_inline_whitespace(segments)

      cond do
        segments == [] -> acc
        acc == [] -> segments
        trailing_space?(acc) or leading_space?(segments) -> acc ++ segments
        true -> acc ++ [{" ", nil} | segments]
      end
    end)
  end

  defp normalize_inline_whitespace(segments) do
    Enum.flat_map(segments, fn {value, role} ->
      Regex.split(~r/(\s+)/u, value, include_captures: true, trim: true)
      |> Enum.map(fn part -> if Regex.match?(~r/^\s+$/u, part), do: {" ", nil}, else: {part, role} end)
    end)
  end

  defp wrap_segments(segments, width, tab_width) do
    tokens = split_words(segments)

    {lines, current, _column} =
      Enum.reduce(tokens, {[], [], 1}, fn
        {:space, _role}, {lines, [], column} ->
          {lines, [], column}

        {:space, role}, {lines, current, column} ->
          {lines, current ++ [{" ", role}], column + 1}

        {word, role}, {lines, current, column} ->
          word_width = display_width(word, column, tab_width: tab_width)

          if current != [] and column - 1 + word_width > width do
            {lines ++ [trim_trailing_space(current)], [{word, role}], 1 + display_width(word, 1, tab_width: tab_width)}
          else
            {lines, current ++ [{word, role}], column + word_width}
          end
      end)

    (lines ++ [trim_trailing_space(current)])
    |> Enum.reject(&(&1 == []))
    |> intersperse([{"\n", nil}])
    |> List.flatten()
  end

  defp split_words(segments) do
    Enum.flat_map(segments, fn
      {" ", role} -> [{:space, role}]
      {value, role} -> [{value, role}]
    end)
  end

  defp trim_trailing_space(segments) do
    case List.last(segments) do
      {" ", _role} -> Enum.drop(segments, -1)
      _ -> segments
    end
  end

  defp prefixed_block(prefix, document, opts, role) do
    body = render(document, %{opts | width: max(1, opts.width - String.length(prefix))}, role)
    prefix_lines(body, prefix, String.duplicate(" ", String.length(prefix)))
  end

  defp prefix_lines([], _first), do: []
  defp prefix_lines(segments, first), do: prefix_lines(segments, first, first)

  defp prefix_lines(segments, first, rest) do
    {result, _at_start, _line_number} =
      Enum.reduce(segments, {[], true, 0}, fn {value, role}, state ->
        Regex.split(~r/(\n)/, value, include_captures: true, trim: true)
        |> Enum.reduce(state, fn
          "\n", {acc, _at_start, line_number} ->
            {acc ++ [{"\n", nil}], true, line_number + 1}

          piece, {acc, true, line_number} ->
            prefix = if line_number == 0, do: first, else: rest
            {acc ++ [{prefix, nil}, {piece, role}], false, line_number}

          piece, {acc, false, line_number} ->
            {acc ++ [{piece, role}], false, line_number}
        end)
      end)

    result
  end

  defp leading_space?([{value, _role} | _]), do: String.starts_with?(value, " ")
  defp trailing_space?(segments), do: segments |> List.last() |> elem(0) |> String.ends_with?(" ")

  defp intersperse([], _separator), do: []
  defp intersperse([item], _separator), do: [item]
  defp intersperse([item | rest], separator), do: [item, separator | intersperse(rest, separator)]

  # Grapheme segmentation handles combining sequences and ZWJ clusters. East
  # Asian width supplies the authoritative wide/full-width classification.
  defp grapheme_width(grapheme) do
    codepoints = String.to_charlist(grapheme)
    first = hd(codepoints)

    cond do
      Regex.match?(~r/^\p{M}+$/u, grapheme) -> 0
      emoji_cluster?(codepoints) -> 2
      Unicode.EastAsianWidth.east_asian_width_category(first) in [:w, :f] -> 2
      control?(first) -> 0
      true -> 1
    end
  end

  defp emoji_cluster?(codepoints) do
    0xFE0F in codepoints or 0x200D in codepoints or
      Enum.any?(codepoints, &(&1 in 0x1F1E6..0x1FAFF))
  end

  defp control?(codepoint), do: codepoint < 0x20 or codepoint in 0x7F..0x9F

  defp role_ansi(role) when role in [:expected, :addition], do: IO.ANSI.green()
  defp role_ansi(role) when role in [:observed, :removal, :error_marker], do: IO.ANSI.red()
  defp role_ansi(:warning_marker), do: IO.ANSI.yellow()
  defp role_ansi(role) when role in [:banner, :secondary_marker], do: IO.ANSI.cyan()
  defp role_ansi(:keyword), do: IO.ANSI.magenta()
  defp role_ansi(role) when role in [:name, :type], do: IO.ANSI.cyan()
end
