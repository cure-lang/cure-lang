defmodule Cure.Diagnostic.SnippetTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Doc, Label, Snippet, SourceRegistry}

  test "disjoint labels share a marker row while overlaps use separate rows" do
    {registry, [left, right, overlap]} =
      labels("alpha beta gamma", [{0, 5, :primary}, {11, 16, :secondary}, {3, 9, :secondary}])

    rendered = render(left, [right, overlap], registry)

    assert rendered =~ "^^^^^"
    assert rendered =~ "^^^^^      -----"
    assert rendered =~ "   ------"
    assert length(String.split(rendered, "\n")) == 4
  end

  test "separated regions elide source vertically and multiline spans use gutter arrows" do
    source = Enum.map_join(1..14, "\n", &"line #{&1}")
    registry = SourceRegistry.new() |> SourceRegistry.register(:source, source, "demo.cure")
    {:ok, first_span} = SourceRegistry.span(registry, :source, 0, 20)
    {:ok, last_span} = SourceRegistry.span(registry, :source, byte_size(source) - 7, byte_size(source))
    primary = %Label{span: first_span, style: :primary, message: "first region"}
    secondary = %Label{span: last_span, style: :secondary, message: "last region"}

    rendered = render(primary, [secondary], registry, max_lines: 7)

    assert rendered =~ " | …"
    assert rendered =~ " > "
    assert rendered =~ "line 14"
  end

  test "zero-width insertions get one caret and long lines clip horizontally" do
    source = String.duplicate("prefix_", 12) <> "target" <> String.duplicate("_suffix", 12)
    registry = SourceRegistry.new() |> SourceRegistry.register(:source, source, "wide.cure")
    offset = :binary.match(source, "target") |> elem(0)
    {:ok, span} = SourceRegistry.span(registry, :source, offset, offset)
    primary = %Label{span: span, style: :primary, message: "insert here"}

    rendered = render(primary, [], registry, width: 36)

    assert rendered =~ "…"
    assert rendered =~ "^ insert here"
  end

  test "CRLF source lines do not leak carriage returns into snippets" do
    source = "fn bad() -> Int = true\r\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:crlf, source, "crlf.cure")
    {:ok, span} = SourceRegistry.span(registry, :crlf, byte_size("fn bad() -> Int = "), byte_size(source) - 2)
    primary = %Label{span: span, style: :primary, message: "this expression is not an Int"}

    rendered = render(primary, [], registry)

    assert rendered =~ "fn bad() -> Int = true\n"
    refute rendered =~ "\r"
    assert rendered =~ "^ this expression is not an Int"
  end

  test "cross-file regions remain separate and ANSI styles marker roles only" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:one, "first", "one.cure")
    registry = SourceRegistry.register(registry, :two, "second", "two.cure")
    {:ok, one} = SourceRegistry.span(registry, :one, 0, 5)
    {:ok, two} = SourceRegistry.span(registry, :two, 0, 6)
    primary = %Label{span: one, style: :primary}
    secondary = %Label{span: two, style: :secondary}
    plan = Snippet.plan(primary, [secondary], registry, width: 40)

    plain = plan |> Snippet.to_doc(:error) |> Doc.plain(width: 40)
    ansi = plan |> Snippet.to_doc(:error) |> Doc.ansi(width: 40)

    assert plain =~ "at one.cure"
    assert plain =~ "at two.cure"
    assert ansi =~ IO.ANSI.red() <> "^^^^^" <> IO.ANSI.reset()
    assert ansi =~ IO.ANSI.cyan() <> "------" <> IO.ANSI.reset()
  end

  defp labels(source, ranges) do
    registry = SourceRegistry.new() |> SourceRegistry.register(:source, source, "demo.cure")

    labels =
      Enum.map(ranges, fn {first, last, style} ->
        {:ok, span} = SourceRegistry.span(registry, :source, first, last)
        %Label{span: span, style: style}
      end)

    {registry, labels}
  end

  defp render(primary, secondary, registry, opts \\ []) do
    opts = Keyword.put_new(opts, :width, 80)
    primary |> Snippet.plan(secondary, registry, opts) |> Snippet.to_doc(:error, opts) |> Doc.plain(opts)
  end
end
