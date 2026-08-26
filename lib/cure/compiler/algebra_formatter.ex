defmodule Cure.Compiler.AlgebraFormatter do
  @moduledoc """
  AST-driven pretty-printer for Cure source, built on top of
  `Cure.Compiler.Algebra` (an `Inspect.Algebra`-style document module).

  Opt-in via `cure fmt --algebra`. The existing byte-level safe
  formatter (`Cure.Compiler.Formatter`) remains the default for
  v0.20.0 and will be promoted to `--algebra` as the default in
  v0.21.0.

  ## Layering

  Rather than rewrite every node's surface syntax, the v0.20.0
  algebra formatter delegates per-node rendering to
  `Cure.Compiler.Printer.quoted_to_string/2`. The AST walker here is
  responsible only for the outer layout:

    * Preserving standalone `{:comment, meta, text}` nodes as real
      `# <text>` lines.
    * Emitting a blank line between consecutive top-level definitions.
    * Descending into `:container` nodes so comments nested inside
      them come back out in source order.

  ## Round-trip verification

  Callers are expected to round-trip the result: re-lex, re-parse,
  and compare the AST (modulo comment placement) against the input.
  `Cure.Compiler.Formatter.format_algebra/2` performs that check and
  falls back to the original buffer on any mismatch.
  """

  alias Cure.Compiler.{Algebra, Printer}

  @default_width 98
  @default_indent "  "

  @doc """
  Render a Cure AST (with `preserve_comments: true` lexer output) into
  a formatted source binary.
  """
  @spec format(term(), keyword()) :: binary()
  def format(ast, opts \\ []) do
    width = Keyword.get(opts, :width, @default_width)
    indent = Keyword.get(opts, :indent, @default_indent)

    ast
    |> document(indent)
    |> Algebra.format(width)
    |> IO.iodata_to_binary()
    |> ensure_trailing_newline()
  end

  @spec document(term(), binary()) :: Algebra.t()
  def document(ast, indent) do
    case ast do
      {:block, _meta, children} ->
        sequence_doc(children, indent, 0)

      {:container, meta, body} ->
        container_doc(meta, body, indent, 0)

      {:comment, _meta, text} when is_binary(text) ->
        Algebra.string("# " <> text)

      _ ->
        Algebra.string(Printer.quoted_to_string(ast, indent: indent))
    end
  end

  # Render a sequence of statements with a blank line between them.
  # Comments attach to the following non-comment statement.
  defp sequence_doc(children, indent, depth) do
    children
    |> group_with_comments()
    |> Enum.map(&group_doc(&1, indent, depth))
    |> intersperse(Algebra.line(2))
    |> Algebra.concat()
  end

  defp group_with_comments(children) do
    {groups, pending} =
      Enum.reduce(children, {[], []}, fn
        {:comment, _, _} = node, {groups, pending} ->
          {groups, pending ++ [node]}

        node, {groups, pending} ->
          {groups ++ [pending ++ [node]], []}
      end)

    if pending == [], do: groups, else: groups ++ [pending]
  end

  defp group_doc(nodes, indent, depth) do
    nodes
    |> Enum.map(&single_node_doc(&1, indent, depth))
    |> intersperse(Algebra.line())
    |> Algebra.concat()
  end

  defp single_node_doc({:comment, _, text}, _indent, _depth) do
    Algebra.string("# " <> text)
  end

  defp single_node_doc({:container, meta, body}, indent, depth) do
    container_doc(meta, body, indent, depth)
  end

  defp single_node_doc({:block, _meta, children}, indent, depth) do
    sequence_doc(children, indent, depth)
  end

  defp single_node_doc(node, indent, _depth) do
    Algebra.string(Printer.quoted_to_string(node, indent: indent))
  end

  # Module-like containers have their header emitted explicitly so we
  # can walk their body as a sequence of algebra docs (which picks up
  # nested comments). Struct and enum containers fall back to the
  # Printer for compact rendering.
  defp container_doc(meta, body, indent, depth) do
    case Keyword.get(meta, :container_type) do
      type when type in [:module, :protocol, :trait, :proof] ->
        header = container_header(meta)
        body_doc = sequence_doc(body, indent, depth + 1)

        Algebra.concat([
          header,
          Algebra.line(),
          Algebra.string(indent),
          Algebra.nest(body_doc, String.length(indent))
        ])

      _ ->
        Algebra.string(Printer.quoted_to_string({:container, meta, body}, indent: indent))
    end
  end

  defp container_header(meta) do
    name = Keyword.get(meta, :name, "Unnamed")
    type_params = Keyword.get(meta, :type_params, [])

    text =
      case Keyword.get(meta, :container_type) do
        :module ->
          "mod " <> name

        :protocol ->
          "proto " <> name <> tp_string(type_params)

        :trait ->
          proto = Keyword.get(meta, :protocol, "")
          for_type = Keyword.get(meta, :for, "")
          "impl " <> proto <> " for " <> for_type

        :proof ->
          "proof " <> name

        _ ->
          name
      end

    Algebra.string(text)
  end

  defp tp_string([]), do: ""
  defp tp_string(list), do: "(" <> Enum.join(list, ", ") <> ")"

  # -- Helpers ---------------------------------------------------------------

  defp intersperse([], _sep), do: []
  defp intersperse([single], _sep), do: [single]
  defp intersperse([head | rest], sep), do: [head, sep | intersperse(rest, sep)]

  defp ensure_trailing_newline(""), do: ""

  defp ensure_trailing_newline(str) do
    if String.ends_with?(str, "\n"), do: str, else: str <> "\n"
  end
end
