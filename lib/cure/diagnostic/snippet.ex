defmodule Cure.Diagnostic.Snippet do
  @moduledoc false

  alias Cure.Diagnostic.{Doc, Label, SourceRegistry, Span}

  defmodule Plan do
    @moduledoc false
    defstruct groups: []
  end

  defmodule Group do
    @moduledoc false
    defstruct [:source_id, :path, :start_line, :start_column, lines: []]
  end

  defmodule Line do
    @moduledoc false
    defstruct [:number, :source, :leading_clip, :trailing_clip, :multiline, marker_rows: []]
  end

  defmodule Marker do
    @moduledoc false
    defstruct [:start, :width, :style, :message, :order]
  end

  @type severity :: Cure.Diagnostic.severity()

  @spec plan(Label.t() | nil, [Label.t()], SourceRegistry.t() | nil, keyword()) :: Plan.t()
  def plan(primary, secondary, registry, opts \\ [])

  def plan(_primary, _secondary, nil, _opts), do: %Plan{}

  def plan(primary, secondary, %SourceRegistry{} = registry, opts) do
    labels = Enum.reject([primary | secondary], &is_nil/1)

    groups =
      labels
      |> Enum.with_index()
      |> Enum.group_by(fn {%Label{span: span}, _index} -> span.source_id end)
      |> Enum.sort_by(fn {_source_id, indexed} -> group_order(indexed) end)
      |> Enum.map(fn {source_id, indexed} -> plan_group(source_id, indexed, registry, opts) end)

    %Plan{groups: groups}
  end

  @spec to_doc(Plan.t(), severity(), keyword()) :: Doc.t()
  def to_doc(%Plan{groups: groups}, severity, opts \\ []) do
    project_root = Keyword.get(opts, :project_root)

    groups
    |> Enum.map(fn group ->
      header =
        case normalize_path(group.path, project_root) do
          nil -> Doc.empty()
          path -> Doc.paragraph("at #{path}:#{group.start_line}:#{group.start_column}")
        end

      Doc.concat([header, if(header == Doc.empty(), do: Doc.empty(), else: Doc.line()), group_doc(group, severity)])
    end)
    |> Doc.stack()
  end

  defp plan_group(source_id, indexed, registry, opts) do
    labels = Enum.map(indexed, &elem(&1, 0))
    path = labels |> hd() |> then(& &1.span.path)
    line_numbers = visible_lines(labels, Keyword.get(opts, :max_lines, 8))
    width = Keyword.get(opts, :width, 80)

    gutter_width =
      line_numbers |> Enum.reject(&(&1 == :ellipsis)) |> Enum.max(fn -> 1 end) |> Integer.digits() |> length()

    available = max(8, width - gutter_width - 3)

    lines =
      Enum.map(line_numbers, fn
        :ellipsis ->
          :ellipsis

        line_number ->
          source = source_line!(registry, hd(labels).span, line_number)

          markers =
            indexed
            |> Enum.flat_map(fn {label, order} -> marker_for_line(label, order, source, line_number) end)

          {source, markers, leading_clip, trailing_clip} = clip(source, markers, available)

          %Line{
            number: line_number,
            source: source,
            leading_clip: leading_clip,
            trailing_clip: trailing_clip,
            multiline: Enum.any?(labels, &multiline_on?(&1.span, line_number)),
            marker_rows: pack_rows(markers)
          }
      end)

    first_label = indexed |> Enum.min_by(&elem(&1, 1)) |> elem(0)

    %Group{
      source_id: source_id,
      path: path,
      start_line: first_label.span.start_line,
      start_column: first_label.span.start_column,
      lines: lines
    }
  end

  defp visible_lines(labels, max_lines) do
    first = labels |> Enum.map(& &1.span.start_line) |> Enum.min()
    last = labels |> Enum.map(& &1.span.end_line) |> Enum.max()
    all = Enum.to_list(first..last)

    if length(all) <= max_lines do
      all
    else
      keep = max(2, div(max_lines - 1, 2))
      Enum.take(all, keep) ++ [:ellipsis] ++ Enum.take(all, -keep)
    end
  end

  defp marker_for_line(%Label{span: span} = label, order, source, line_number) do
    if line_number in span.start_line..span.end_line do
      start_column = if line_number == span.start_line, do: span.start_column, else: 1
      end_column = if line_number == span.end_line, do: span.end_column, else: String.length(source) + 1
      start = visual_column(source, start_column)
      finish = visual_column(source, end_column)

      [
        %Marker{
          start: start,
          width: max(1, finish - start),
          style: label.style,
          message: if(line_number == span.end_line, do: label.message),
          order: order
        }
      ]
    else
      []
    end
  end

  defp pack_rows(markers) do
    markers
    |> Enum.sort_by(&{&1.start, style_order(&1.style), &1.order, &1.width})
    |> Enum.reduce([], fn marker, rows -> put_in_first_available_row(rows, marker) end)
    |> Enum.map(&Enum.sort_by(&1, fn marker -> {marker.start, marker.order} end))
  end

  defp put_in_first_available_row([], marker), do: [[marker]]

  defp put_in_first_available_row([row | rest], marker) do
    if Enum.all?(row, &disjoint?(&1, marker)) do
      [row ++ [marker] | rest]
    else
      [row | put_in_first_available_row(rest, marker)]
    end
  end

  defp disjoint?(left, right),
    do: left.start + left.width <= right.start or right.start + right.width <= left.start

  defp clip(source, markers, available) do
    source_width = Doc.display_width(source)

    if source_width <= available do
      {expand_tabs(source), markers, false, false}
    else
      focus = markers |> Enum.map(& &1.start) |> Enum.min(fn -> 1 end)
      left = max(0, focus - div(available, 3) - 1)
      content_width = available - if(left > 0, do: 1, else: 0)
      {slice, actual_left, trailing?} = display_slice(source, left, content_width)
      leading? = actual_left > 0
      prefix_width = if leading?, do: 1, else: 0

      adjusted =
        markers
        |> Enum.map(fn marker -> %{marker | start: max(1, marker.start - actual_left + prefix_width)} end)
        |> Enum.filter(&(&1.start <= available))
        |> Enum.map(fn marker -> %{marker | width: min(marker.width, available - marker.start + 1)} end)

      prefix = if leading?, do: "…", else: ""
      suffix = if trailing?, do: "…", else: ""
      {prefix <> slice <> suffix, adjusted, leading?, trailing?}
    end
  end

  defp display_slice(source, wanted_left, available) do
    graphemes = String.graphemes(source)

    {remaining, skipped_width} =
      Enum.reduce_while(graphemes, {graphemes, 0}, fn _grapheme, {[head | tail], width} ->
        next = Doc.display_width(head, width + 1)
        if width + next <= wanted_left, do: {:cont, {tail, width + next}}, else: {:halt, {[head | tail], width}}
      end)

    {selected, width, rest} =
      Enum.reduce_while(remaining, {[], 0, remaining}, fn _grapheme, {selected, width, [head | tail]} ->
        next = Doc.display_width(head, width + 1)

        if width + next <= max(1, available - 1),
          do: {:cont, {selected ++ [head], width + next, tail}},
          else: {:halt, {selected, width, [head | tail]}}
      end)

    {expand_tabs(Enum.join(selected)), skipped_width, rest != [] and width > 0}
  end

  defp group_doc(%Group{lines: lines}, severity) do
    gutter_width =
      lines
      |> Enum.reject(&(&1 == :ellipsis))
      |> Enum.map(& &1.number)
      |> Enum.max(fn -> 1 end)
      |> Integer.digits()
      |> length()

    lines
    |> Enum.map(fn
      :ellipsis -> Doc.text(String.duplicate(" ", gutter_width) <> " | …")
      line -> line_doc(line, gutter_width, severity)
    end)
    |> then(&Doc.concat(Enum.intersperse(&1, Doc.line())))
  end

  defp line_doc(%Line{} = line, gutter_width, severity) do
    source = Doc.code(String.pad_leading(Integer.to_string(line.number), gutter_width) <> " | " <> line.source)

    markers =
      line.marker_rows
      |> Enum.map(&marker_row_doc(&1, gutter_width, line.multiline, severity))
      |> then(&Doc.concat(Enum.flat_map(&1, fn row -> [Doc.line(), row] end)))

    Doc.concat([source, markers])
  end

  defp marker_row_doc(markers, gutter_width, multiline, severity) do
    gutter =
      if multiline do
        [
          Doc.text(String.duplicate(" ", gutter_width) <> " "),
          Doc.emphasis(:error_marker, ">"),
          Doc.text(" ")
        ]
      else
        [Doc.text(String.duplicate(" ", gutter_width) <> " | ")]
      end

    {parts, _column} =
      Enum.reduce(markers, {gutter, 1}, fn marker, {parts, column} ->
        padding = String.duplicate(" ", max(0, marker.start - column))
        glyph = if marker.style == :secondary, do: "-", else: "^"
        role = marker_role(marker.style, severity, multiline)
        parts = parts ++ [Doc.text(padding), Doc.emphasis(role, String.duplicate(glyph, marker.width))]
        {parts, marker.start + marker.width}
      end)

    messages = markers |> Enum.map(& &1.message) |> Enum.reject(&is_nil/1)
    suffix = if messages == [], do: "", else: " " <> Enum.join(messages, "; ")
    Doc.concat(parts ++ [Doc.text(suffix)])
  end

  defp marker_role(:secondary, _severity, _multiline), do: :secondary_marker
  defp marker_role(:primary, _severity, true), do: :error_marker
  defp marker_role(:primary, :warning, false), do: :warning_marker
  defp marker_role(:primary, _severity, false), do: :error_marker

  defp multiline_on?(%Span{start_line: first, end_line: last}, line), do: first < last and line in first..last

  defp visual_column(source, scalar_column) do
    source
    |> String.codepoints()
    |> Enum.take(max(0, scalar_column - 1))
    |> Enum.join()
    |> Doc.display_width()
    |> Kernel.+(1)
  end

  defp expand_tabs(source) do
    {parts, _column} =
      source
      |> String.graphemes()
      |> Enum.map_reduce(1, fn
        "\t", column ->
          width = 4 - rem(column - 1, 4)
          {String.duplicate(" ", width), column + width}

        grapheme, column ->
          {grapheme, column + Doc.display_width(grapheme, column)}
      end)

    IO.iodata_to_binary(parts)
  end

  defp source_line!(registry, span, line_number) do
    case SourceRegistry.line(registry, span, line_number) do
      {:ok, source} -> source
      :error -> ""
    end
  end

  defp group_order(indexed), do: indexed |> Enum.map(&elem(&1, 1)) |> Enum.min()
  defp style_order(:primary), do: 0
  defp style_order(:secondary), do: 1

  defp normalize_path(nil, _root), do: nil
  defp normalize_path(path, nil), do: path
  defp normalize_path(path, root), do: Path.relative_to(Path.expand(path), Path.expand(root))
end
