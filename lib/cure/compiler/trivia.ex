defmodule Cure.Compiler.Trivia.UnplacedTriviaError do
  @moduledoc """
  Raised by `Cure.Compiler.Trivia.attach/2` when a trivia item (comment,
  doc-comment, or blank run) cannot be placed onto any AST node. The trivia
  model is "total by construction" (spec §5.2): a lossless reprint must never
  silently drop a comment, so an unplaceable item is a hard error, not a
  no-op.
  """
  defexception [:item]

  @impl true
  def message(%__MODULE__{item: item}) do
    "trivia item could not be placed onto any AST node: #{inspect(item)}"
  end
end

defmodule Cure.Compiler.Trivia do
  @moduledoc """
  Post-parse trivia attachment (spec §5.2). Takes the AST and the lexer's
  positioned trivia list (`Lexer.tokenize(src, trivia: true)`) and threads
  each comment / doc-comment / blank-run into the `meta` of the node it
  belongs to, under `:leading` / `:trailing` / `:trailer`. The Printer
  (Task 6) reads those keys back out to reproduce the original layout.

  Attachment is **total**: every item is placed, or `attach/2` raises
  `UnplacedTriviaError`. It never drops trivia.

  ## Placement rule (spec §5.2)

  - A comment on the **same line** as, and **after**, a node's last token →
    that node's `:trailing`.
  - Otherwise → the `:leading` of the next node that starts at or after the
    item's line.
  - An item after the last child of an enclosing container, with no following
    sibling → that container's `:trailer` (innermost such container).
  - Blank runs are leading-only (a blank line has no token to trail); a run
    that sits between a container's last child and the container's end attaches
    to that container's `:trailer` (so it belongs to what precedes it).

  ## Effective span

  Many real node kinds carry no `line`/`col` in their own `meta` (`:pair`,
  `:match_arm`, `:tuple`, type-position `:variable`, …). A node's effective
  span is therefore computed recursively: its own position if present, else the
  min/max over its descendants' positions. A positionless, childless leaf (e.g.
  a lambda `:param` whose third element is a bare string) contributes nothing
  and is transparent to classification.
  """

  alias Cure.Compiler.Trivia.UnplacedTriviaError
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @trivia_keys [:leading, :trailing, :trailer]

  @doc """
  Attach `trivia` (the lexer's positioned trivia list) onto `ast`, returning
  the AST with trivia threaded into node `meta`. Raises `UnplacedTriviaError`
  if any item cannot be placed.
  """
  def attach(ast, []), do: ast

  def attach(ast, trivia) do
    index = build_index(ast)

    placements =
      Enum.map(trivia, fn item ->
        case classify(item, index) do
          nil -> raise UnplacedTriviaError, item: item
          target -> {item, target}
        end
      end)

    pmap = placement_map(placements)
    {new_ast, _next} = do_inject(ast, 0, pmap)
    new_ast
  end

  @doc """
  Move any attached `:leading`/`:trailing`/`:trailer` trivia from `from_node`
  onto `to_node` (concatenating if `to_node` already has some), returning the
  updated `to_node`. Used by restructuring migration rules so a moved node
  carries its comments with it (spec §5.2).
  """
  def carry(from_node, to_node) do
    from_meta = node_meta(from_node)
    to_meta = node_meta(to_node)

    new_to_meta =
      Enum.reduce(@trivia_keys, to_meta, fn key, meta ->
        case Keyword.get(from_meta, key) do
          nil -> meta
          items -> Keyword.update(meta, key, items, &(&1 ++ items))
        end
      end)

    put_node_meta(to_node, new_to_meta)
  end

  # ── Position index ────────────────────────────────────────────────────────

  # A flat list of records, one per spannable node, in some order. Each record:
  #   %{id, sl, sc, el, ec, container?, child_spans}
  # where (sl,sc)/(el,ec) are the min/max positions in the node's subtree and
  # `child_spans` is [{sl, el}] for a container's direct spannable children.
  defp build_index(ast) do
    {records, _next} = collect(ast, 0, [])
    records |> Enum.reject(&is_nil/1)
  end

  # Assign ids in a fixed pre-order so `do_inject/3` can re-derive the same id
  # per node by walking identically. Returns {acc, next_id}.
  defp collect({_k, meta, ch} = node, id, acc) when is_list(meta) and is_list(ch) do
    rec = record(node, id, true)
    Enum.reduce(ch, {[rec | acc], id + 1}, fn child, {a, n} -> collect(child, n, a) end)
  end

  defp collect({_k, meta, name, inner} = node, id, acc)
       when is_list(meta) and is_binary(name) do
    collect(inner, id + 1, [record(node, id, false) | acc])
  end

  defp collect({_k, meta, _v} = node, id, acc) when is_list(meta) do
    {[record(node, id, false) | acc], id + 1}
  end

  defp collect(l, id, acc) when is_list(l) do
    Enum.reduce(l, {acc, id}, fn child, {a, n} -> collect(child, n, a) end)
  end

  defp collect(_other, id, acc), do: {acc, id}

  defp record(node, id, container?) do
    case points(node) do
      [] ->
        nil

      pts ->
        {sl, sc} = Enum.min(pts)
        {el, ec} = Enum.max(pts)

        %{
          id: id,
          sl: sl,
          sc: sc,
          el: el,
          ec: ec,
          # Not every AST node with a child list is a layout container. Match
          # arms, pairs, calls, and collection nodes are rendered inline; a
          # comment after their final child must belong to the enclosing
          # statement/block or the printer's span renderer will bypass it.
          container?: container? and trivia_container?(node),
          child_spans: if(container?, do: direct_child_spans(node), else: [])
        }
    end
  end

  defp trivia_container?({:block, _meta, _children}), do: true

  # A zero-child `:container` is a module/header marker, not a printable
  # statement list. Treating it as the deepest trailer target steals blanks and
  # comments from the function or top-level block that follows it.
  defp trivia_container?({:container, _meta, children}) when is_list(children) and children != [], do: true

  defp trivia_container?(_node), do: false

  defp direct_child_spans({_k, _meta, ch}) when is_list(ch) do
    ch
    |> Enum.map(&node_span/1)
    |> Enum.reject(&is_nil/1)
  end

  defp node_span(node) do
    case points(node) do
      [] ->
        nil

      pts ->
        {sl, _} = Enum.min(pts)
        {el, _} = Enum.max(pts)
        {sl, el}
    end
  end

  # Every {line, col} position anywhere in the node's subtree.
  defp points({_k, meta, ch}) when is_list(meta) and is_list(ch) do
    own_point(meta) ++ Enum.flat_map(ch, &points/1)
  end

  defp points({_k, meta, name, inner}) when is_list(meta) and is_binary(name) do
    own_point(meta) ++ points(inner)
  end

  defp points({_k, meta, _v}) when is_list(meta), do: own_point(meta)
  defp points(l) when is_list(l), do: Enum.flat_map(l, &points/1)
  defp points(_), do: []

  defp own_point(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: %Cure.Diagnostic.Span{} = span} ->
        [{span.start_line, span.start_column}, {span.end_line, span.end_column}]

      _ ->
        case Keyword.get(meta, :line) do
          nil -> []
          line -> [{line, Keyword.get(meta, :col, 0)}]
        end
    end
  end

  # ── Classification ────────────────────────────────────────────────────────

  # Blanks are leading-only, and prefer to belong to what precedes them (a
  # container's trailer) so they don't pollute the following node's leading
  # list with non-comment items.
  defp classify({:blank, _count, line}, index) do
    # A blank between sibling statements belongs to the following statement so
    # the statement-list printer can preserve exactly one separator. If there
    # is no following node, fall back to the enclosing container's trailer.
    leading_target(index, line) || trailer_target(index, line)
  end

  defp classify({_kind, _text, line, col}, index) do
    trailing_target(index, line, col) ||
      leading_target(index, line) ||
      trailer_target(index, line)
  end

  # Same line as, and after, a node whose content ends before `col`. Attach to
  # the OUTERMOST such node (earliest start) so the trailing comment renders
  # after the whole construct on that line, never mid-expression.
  defp trailing_target(index, line, col) do
    index
    |> Enum.filter(fn r -> r.el == line and r.ec < col end)
    |> case do
      [] -> nil
      cands -> {:trailing, pick(cands, &{&1.sl, &1.sc, &1.id}, :min).id}
    end
  end

  # The next node starting at or after `line`; attach to its leading. Prefer the
  # outermost node at that start position (a container over its first child).
  defp leading_target(index, line) do
    index
    |> Enum.filter(fn r -> r.sl >= line end)
    |> case do
      [] -> nil
      cands -> {:leading, pick(cands, &{&1.sl, &1.sc, &1.id}, :min).id}
    end
  end

  # The innermost container that starts at/before `line` and has no direct child
  # starting after `line` (the item is past its last child). Deepest wins.
  defp trailer_target(index, line) do
    index
    |> Enum.filter(fn r ->
      r.container? and r.sl <= line and
        not Enum.any?(r.child_spans, fn {csl, _cel} -> csl > line end)
    end)
    |> case do
      [] -> nil
      cands -> {:trailer, pick(cands, & &1.id, :max).id}
    end
  end

  defp pick(records, key_fun, :min), do: Enum.min_by(records, key_fun)
  defp pick(records, key_fun, :max), do: Enum.max_by(records, key_fun)

  # ── Injection ─────────────────────────────────────────────────────────────

  defp placement_map(placements) do
    Enum.reduce(placements, %{}, fn {item, {kind, id}}, acc ->
      slot = Map.get(acc, id, %{leading: [], trailing: [], trailer: []})
      Map.put(acc, id, Map.update!(slot, kind, &(&1 ++ [item])))
    end)
  end

  # Re-walk with the exact same id scheme as collect/3, merging placed trivia
  # into each node's meta. Returns {new_node, next_id}.
  defp do_inject({k, meta, ch}, id, pmap) when is_list(meta) and is_list(ch) do
    meta = merge_meta(meta, Map.get(pmap, id))

    {new_ch, next} =
      Enum.reduce(ch, {[], id + 1}, fn child, {a, n} ->
        {c, n2} = do_inject(child, n, pmap)
        {[c | a], n2}
      end)

    {{k, meta, Enum.reverse(new_ch)}, next}
  end

  defp do_inject({k, meta, name, inner}, id, pmap) when is_list(meta) and is_binary(name) do
    meta = merge_meta(meta, Map.get(pmap, id))
    {new_inner, next} = do_inject(inner, id + 1, pmap)
    {{k, meta, name, new_inner}, next}
  end

  defp do_inject({k, meta, v}, id, pmap) when is_list(meta) do
    {{k, merge_meta(meta, Map.get(pmap, id)), v}, id + 1}
  end

  defp do_inject(l, id, pmap) when is_list(l) do
    {new, next} =
      Enum.reduce(l, {[], id}, fn child, {a, n} ->
        {c, n2} = do_inject(child, n, pmap)
        {[c | a], n2}
      end)

    {Enum.reverse(new), next}
  end

  defp do_inject(other, id, _pmap), do: {other, id}

  defp merge_meta(meta, nil), do: meta

  defp merge_meta(meta, slot) do
    Enum.reduce(@trivia_keys, meta, fn key, m ->
      case Map.get(slot, key, []) do
        [] -> m
        items -> Keyword.update(m, key, items, &(&1 ++ items))
      end
    end)
  end

  # ── Node meta accessors (3- and 4-tuple node shapes) ──────────────────────

  defp node_meta({_k, meta, _}) when is_list(meta), do: meta
  defp node_meta({_k, meta, _, _}) when is_list(meta), do: meta
  defp node_meta(_), do: []

  defp put_node_meta({k, _meta, a}, new_meta), do: {k, new_meta, a}
  defp put_node_meta({k, _meta, a, b}, new_meta), do: {k, new_meta, a, b}
  defp put_node_meta(node, _new_meta), do: node
end
