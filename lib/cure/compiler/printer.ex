defmodule Cure.Compiler.Printer do
  @moduledoc """
  Converts a MetaAST tree back into Cure source code.

  This is the inverse of `Cure.Compiler.Parser`. Given a well-formed MetaAST
  (the `{type, keyword_meta, children_or_value}` 3-tuples produced by the
  parser), it emits a Cure source string that round-trips through the
  lexer/parser pipeline.

  ## Options

  - `:indent` -- indentation unit (default: `"  "`)
  """

  @default_indent "  "

  # Spec-defined formatting parameters (PICKUP §8.7 / MATCH §9.7).
  # Aligned form is dropped if the longest clause head exceeds the
  # alignment limit, falling back to the unaligned form. Wrapping is
  # triggered by either a multi-line right-hand side or a final
  # rendered line exceeding `max_line_width`.
  @alignment_limit 40
  @max_line_width 100

  # Process-dictionary key holding the session `FixityTable` for the duration of
  # a render. Precedence-aware parenthesisation (`op_prec/1` and friends, deep in
  # the recursive render) consults it to rank ANY operator — built-in or
  # user-declared — instead of a hardcoded duplicate of `Std.Operators`. Stored
  # process-scoped rather than threaded through every render clause; ExUnit async
  # tests each run in their own process, so this is isolation-safe.
  @fixity_key :cure_printer_fixity_table

  @doc """
  Render a MetaAST node as a Cure source string.

  ## Options

  - `:indent` — indentation unit (default: two spaces)
  - `:fixity` — the session `Cure.Compiler.Parser.FixityTable` the source parsed
    against. Defaults to the built-in operator table, which already ranks every
    built-in operator; pass the module's assembled table to rank user-declared
    operators correctly (otherwise a custom operator is treated as unknown and
    its operands are conservatively parenthesised). The module-specific table is
    the one produced by `Cure.Compiler.Parser.FixityResolver.assemble/5` — the
    same use-propagated union the parser resolved the module against.
  """
  @spec quoted_to_string(term(), keyword()) :: String.t()
  def quoted_to_string(ast, opts \\ []) do
    indent = Keyword.get(opts, :indent, @default_indent)
    table = Keyword.get(opts, :fixity) || Cure.Compiler.Parser.BuiltinFixity.table()
    prev = Process.put(@fixity_key, table)

    try do
      case ast do
        # The outermost node of a multi-definition file is the program's
        # top-level statement list. Apply the §5.4 top-of-file policy here (rule 3:
        # exactly one blank line between every top-level definition; rule 1: no
        # leading blanks) — NOT in the generic `{:block, …}` clause, because a
        # function body is also a `:block` and may itself render at depth 0.
        {:block, meta, exprs} -> render_program(exprs, meta, indent)
        _ -> render(ast, 0, indent)
      end
    after
      if prev == nil, do: Process.delete(@fixity_key), else: Process.put(@fixity_key, prev)
    end
  end

  # Render the whole-file statement list, then re-apply the *block's own* trivia:
  # a `:leading` comment at the very top of the file, a `:trailing` comment on the
  # file's last line (a genuine end-of-file trailing comment — spec §5.2 forbids
  # dropping it), and any `:trailer` lines after the last statement. All three
  # helpers no-op on `nil`, and blank runs render to nothing, so a file whose
  # block carries no trivia (the corpus fixpoint gate, and every file the plain
  # Printer sees) is byte-identical to before.
  defp render_program(exprs, meta, indent) do
    nodes = flatten_top_level(exprs)

    # Rule 3 puts one blank between top-level items — EXCEPT a decorator hugs
    # the item it decorates (no blank between them). The parser absorbs a
    # decorator written directly above its `mod`/`def` into that node, so a
    # decorator only survives as a standalone top-level sibling when a rule
    # (e.g. group-hoist) relocates it; rendering it tight matches the absorbed
    # form, so `print∘reparse∘print` is a fixpoint and `cure migrate` is
    # text-idempotent instead of shedding a blank line on its second run.
    #
    # A blank precedes item `i` iff `i > 0` and its predecessor is not a
    # decorator. Pairing each rendered line with the preceding node via a
    # one-position shift (`[nil | nodes]`) keeps this a single O(n) pass;
    # re-reading `Enum.at(nodes, i - 1)` per item was O(n²) in the statement
    # count. Nodes are always tuples, so the leading `nil` marks position 0.
    body =
      nodes
      |> Enum.map(&render(&1, 0, indent))
      |> Enum.zip([nil | nodes])
      |> Enum.map(fn {rendered, prev} ->
        {rendered, prev != nil and not match?({:decorator, _, _}, prev)}
      end)
      |> join_statements("")

    body
    |> prepend_leading(Keyword.get(meta, :leading), 0, indent)
    |> append_trailing(Keyword.get(meta, :trailing))
    |> append_trailer(Keyword.get(meta, :trailer), 0, indent)
  end

  # A bare `mod Name` header leaves its sibling definitions wrapped in a single
  # `:block` node. That wrapper has NO surface syntax (it renders as a plain
  # statement list) and is dropped on reparse — the definitions become top-level
  # siblings. Flatten it here so the §5.4 top-of-file rule-3 blank policy sees the
  # same statement set the reparse will; otherwise `print∘reparse∘print` inserts
  # blanks the first print did not, and the corpus fixpoint gate fails. The
  # wrapper's OWN trivia (a section-header comment attached to the block's
  # `:leading`, a `:trailer` after its last statement) is carried onto the edge
  # statements so flattening the syntax-less wrapper loses no comment.
  defp flatten_top_level(exprs) do
    Enum.flat_map(exprs, fn
      {:block, bmeta, inner} when is_list(inner) and inner != [] ->
        inner |> flatten_top_level() |> carry_block_trivia(bmeta)

      other ->
        [other]
    end)
  end

  defp carry_block_trivia(inner, bmeta) do
    inner
    |> prepend_node_trivia(:leading, Keyword.get(bmeta, :leading))
    |> append_node_trivia(:trailer, Keyword.get(bmeta, :trailer))
    |> append_node_trivia(:trailing, Keyword.get(bmeta, :trailing))
  end

  defp prepend_node_trivia(list, _key, nil), do: list

  defp prepend_node_trivia([{tag, meta, ch} | rest], key, items) when is_list(meta),
    do: [{tag, Keyword.update(meta, key, items, &(items ++ &1)), ch} | rest]

  defp prepend_node_trivia(list, _key, _items), do: list

  defp append_node_trivia(list, _key, nil), do: list

  defp append_node_trivia(list, key, items) when is_list(items) and items != [] do
    case List.pop_at(list, -1) do
      {{tag, meta, ch}, front} when is_list(meta) ->
        front ++ [{tag, Keyword.update(meta, key, items, &(&1 ++ items)), ch}]

      _ ->
        list
    end
  end

  defp append_node_trivia(list, _key, _items), do: list

  # Render a block body / statement list applying §5.4 rule 4: a single author
  # blank between two statements is preserved (a run capped at 1), signalled by a
  # `:blank` item in either the preceding statement's `:trailer` or the following
  # statement's `:leading`; blanks adjacent to the block's open/close are dropped
  # (never injected before the first or after the last statement). `child_depth`
  # is the depth at which the statements render; the caller supplies the leading
  # pad for the first line. With no trivia attached (e.g. the corpus fixpoint
  # gate) every `blank?` is false, so output is byte-identical to a plain
  # "\n"<>pad join.
  defp render_stmt_list(exprs, child_depth, indent) do
    pad = String.duplicate(indent, child_depth)

    case exprs do
      [] ->
        ""

      [only] ->
        coerce(render(only, child_depth, indent))

      [first | rest] ->
        {pairs, _prev} =
          Enum.reduce(rest, {[{render(first, child_depth, indent), false}], first}, fn e, {acc, prev} ->
            blank? = trailer_blank?(prev) or leading_blank?(e)
            {[{render(e, child_depth, indent), blank?} | acc], e}
          end)

        join_statements(Enum.reverse(pairs), pad)
    end
  end

  # Join rendered statements, inserting exactly one blank line before any
  # statement flagged `blank?` (§5.4 rules 3/4). `pad` indents each statement
  # after the first; the blank line itself is emitted empty. Elements are
  # coerced to strings (mirroring `Enum.join`), since a stray keyword-named
  # `:variable` renders to a bare atom (e.g. a dangling `end`).
  defp join_statements([], _pad), do: ""

  defp join_statements([{first, _} | rest], pad) do
    Enum.reduce(rest, coerce(first), fn {rendered, blank?}, acc ->
      sep = if blank?, do: "\n\n" <> pad, else: "\n" <> pad
      acc <> sep <> coerce(rendered)
    end)
  end

  defp coerce(s) when is_binary(s), do: s
  defp coerce(other), do: Kernel.to_string(other)

  # True when a node carries a blank-run item in its attached `:leading` /
  # `:trailer` trivia, respectively.
  defp leading_blank?(node), do: has_blank?(trivia_meta(node), :leading)
  defp trailer_blank?(node), do: has_blank?(trivia_meta(node), :trailer)

  defp has_blank?(meta, key) do
    case Keyword.get(meta, key) do
      nil -> false
      items -> Enum.any?(items, &match?({:blank, _, _}, &1))
    end
  end

  # -- Trivia-aware dispatch wrapper ------------------------------------------
  #
  # Every node is rendered through this single `render/3` clause, which
  # delegates the actual syntax to the per-kind `to_string/3` clauses and then
  # layers on any attached trivia (spec §5.2 / §5.4): `:leading` comment lines
  # emitted (each at the node's own indent) before the node, `:trailing`
  # comments appended on the node's own line, and `:trailer` lines emitted
  # after the node at the node's indent. Every recursive child render also goes
  # through `render/3`, so trivia is applied uniformly at every depth.
  #
  # CRITICAL: when a node carries NONE of `:leading` / `:trailing` /
  # `:trailer`, this returns the per-kind `to_string/3` output byte-for-byte.
  # An AST printed without `Trivia.attach/2` (e.g. the corpus fixpoint gate)
  # has no trivia keys anywhere, so its output is identical to the pre-trivia
  # Printer.
  defp render(node, depth, indent) do
    meta = trivia_meta(node)
    leading = Keyword.get(meta, :leading)
    trailing = Keyword.get(meta, :trailing)
    trailer = Keyword.get(meta, :trailer)

    if leading == nil and trailing == nil and trailer == nil do
      to_string(node, depth, indent)
    else
      to_string(node, depth, indent)
      |> prepend_leading(leading, depth, indent)
      |> append_trailing(trailing)
      |> append_trailer(trailer, depth, indent)
    end
  end

  defp trivia_meta({_k, meta, _}) when is_list(meta), do: meta
  defp trivia_meta({_k, meta, _, _}) when is_list(meta), do: meta
  defp trivia_meta(_), do: []

  # True when a node carries a `:leading` comment. Splicing such a node into an
  # INLINE position (after `-> ` in a lambda) strands its `# c\n…` rendering
  # mid-line, where the reparser reattaches the comment elsewhere — breaking
  # reprint idempotence. Callers that render a body inline break to a fresh line
  # when this is true.
  defp has_leading?(node) do
    case Keyword.get(trivia_meta(node), :leading) do
      nil -> false
      [] -> false
      _ -> true
    end
  end

  # `:leading` items become full lines emitted before the node. The first line
  # takes the pad supplied by the parent join site; every subsequent line (and
  # the node itself) is re-padded here. Blank lines are emitted empty.
  defp prepend_leading(rendered, nil, _depth, _indent), do: rendered

  defp prepend_leading(rendered, items, depth, indent) do
    pad = String.duplicate(indent, depth)

    case Enum.flat_map(items, &trivia_lines/1) do
      [] ->
        rendered

      [first | rest] ->
        rest_str = Enum.map_join(rest, "", fn l -> "\n" <> pad_or_empty(l, pad) end)
        first <> rest_str <> "\n" <> pad <> rendered
    end
  end

  # `:trailing` comments sit on the node's own final line.
  defp append_trailing(rendered, nil), do: rendered

  defp append_trailing(rendered, items) do
    Enum.reduce(items, rendered, fn item, acc -> acc <> "  " <> comment_text(item) end)
  end

  # `:trailer` items become full lines after the node, at the node's indent.
  defp append_trailer(rendered, nil, _depth, _indent), do: rendered

  defp append_trailer(rendered, items, depth, indent) do
    pad = String.duplicate(indent, depth)

    items
    |> Enum.flat_map(&trivia_lines/1)
    |> Enum.reduce(rendered, fn l, acc -> acc <> "\n" <> pad_or_empty(l, pad) end)
  end

  # Physical lines for a trivia item. Blank runs emit NOTHING: the Trivia
  # classifier attaches a blank to the innermost/deepest container that ends
  # before it (spec §5.2), which is routinely a node buried inside an
  # expression (a call in a cons cell, an operand in a `%[...]` tuple, …).
  # Cure has no way to write a blank line there -- a collection literal cannot
  # span a newline without failing to reparse -- so a blank is dropped rather
  # than emitted into a position that cannot hold it. Comments are never
  # dropped; they attach to statement-level nodes where a full line is legal.
  defp trivia_lines({:blank, _count, _}), do: []
  defp trivia_lines({:comment, text, _, _}), do: ["# " <> text]

  defp trivia_lines({:doc_comment, text, _, _}) do
    # A fenced doc token's text can carry trailing "\n"s — an artifact of its
    # construction (an `### tail` opening-tail prepended over an empty body) and
    # any genuine trailing blank body lines, which carry no meaning in a doc
    # comment. Splitting them verbatim would emit spurious empty `## ` lines that
    # reparse as extra doc comments, so drop every trailing newline first.
    # Internal blank lines are preserved.
    text
    |> String.trim_trailing("\n")
    |> String.split("\n")
    |> Enum.map(&("## " <> &1))
  end

  defp comment_text({:comment, text, _, _}), do: "# " <> text
  defp comment_text({:doc_comment, text, _, _}), do: "## " <> text

  defp pad_or_empty("", _pad), do: ""
  defp pad_or_empty(line, pad), do: pad <> line

  # A comma-separated expression span (map/record pairs, list/tuple elements,
  # call args). Cure has NO multi-line collection literals -- a `[`, `(`, `%{`
  # spanning a newline fails to reparse (the layout lexer emits a DEDENT the
  # bracket parser rejects) -- so a span is always emitted on one line, exactly
  # as before trivia support. Each element is rendered with the per-kind
  # `to_string/3` directly rather than the trivia-aware `render/3`, so an
  # element's OWN attached trivia is skipped (there is no single-line position
  # for a comment or blank there). The element's inner subtree still recurses
  # through `render/3`, so e.g. statement comments inside a lambda body are
  # kept. In the std corpus the only trivia that lands on a span element is a
  # blank run (never a comment), so nothing a lossless reprint must keep is
  # lost. Trivia attached to the span CONTAINER node itself flows normally
  # through `render/3` at the enclosing statement level.
  defp render_span(children, sep, depth, indent) do
    Enum.map_join(children, sep <> " ", &to_string(&1, depth, indent))
  end

  defp symbol_to_string(nil), do: ":nil"
  defp symbol_to_string(value), do: ":#{value}"

  # -- Literals --------------------------------------------------------------

  defp to_string({:literal, meta, value}, _depth, _indent) do
    case Keyword.get(meta, :subtype) do
      :integer -> Integer.to_string(value)
      :float -> float_to_string(value)
      :string -> ~s("#{escape_string(value)}")
      :boolean -> Atom.to_string(value)
      :null -> "nil"
      :symbol -> symbol_to_string(value)
      :regex -> regex_to_string(value)
      :char -> char_to_string(value)
      :bytes -> bytes_to_string(meta, value)
      _ -> inspect(value)
    end
  end

  # `()` — the unit value, the sole inhabitant of `Unit`. The parser produces its own
  # node kind for it rather than a `:literal`, so it needs its own clause here.
  defp to_string({:unit_value, _meta}, _depth, _indent), do: "()"

  # -- Variables -------------------------------------------------------------

  defp to_string({:variable, _meta, name}, _depth, _indent), do: name

  # -- Block -----------------------------------------------------------------

  # A block body (§5.4 rule 4): cap blank runs at 1 and trim blanks adjacent to
  # the block's open/close; otherwise preserve the author's single blank between
  # two statements. A blank between statements S[i-1] and S[i] is attached (per
  # the Trivia classifier) to *either* S[i-1]'s `:trailer` or S[i]'s `:leading`,
  # so we check both sides of each pair. A run of N blanks is one `:blank` item,
  # so this caps at exactly one line; blanks adjacent to open/close attach to the
  # block/last-statement and are dropped here (never injected before the first or
  # after the last statement). With no trivia attached (e.g. the corpus fixpoint
  # gate), every `blank?` is false, so output is byte-identical to a plain
  # "\n"<>pad join.
  defp to_string({:block, _meta, exprs}, depth, indent) do
    render_stmt_list(exprs, depth, indent)
  end

  # -- Binary Operators ------------------------------------------------------

  defp to_string({:binary_op, meta, [left, right]}, depth, indent) do
    op = Keyword.get(meta, :operator)
    op_str = operator_to_string(op)
    parent = op_prec(op)
    left_s = operand_str(left, depth, indent, parent, :left)
    right_s = operand_str(right, depth, indent, parent, :right)
    "#{left_s} #{op_str} #{right_s}"
  end

  # -- Unary Operators -------------------------------------------------------

  defp to_string({:unary_op, meta, [operand]}, depth, indent) do
    op = Keyword.get(meta, :operator)
    # A prefix operator binds in the `Prefix` group (tighter than every infix
    # group): its operand needs parentheses whenever it is a lower-precedence
    # expression, or `-(x + 1)` would reprint as `-x + 1` (= `(-x) + 1`) and
    # `not (a and b)` as `not a and b` (= `(not a) and b`) — both meaning-changing.
    inner = operand_str(operand, depth, indent, unary_prec(op), :right)

    case op do
      :not -> "not #{inner}"
      # A leading `-` on the operand would abut into `--`, which the lexer reads
      # as the start of a transition vocabulary (`-->`/`--|`) and fails on — so `-(-x)`
      # must reprint as `- -x`, not `--x`. Separate only when the operand's own
      # rendering starts with `-` (a nested unary minus / negative literal).
      :- -> if String.starts_with?(inner, "-"), do: "- #{inner}", else: "-#{inner}"
      # Word-spelled prefix operators (e.g. `bnot`) need a separating space, or
      # `bnot a` reprints as the single identifier `bnota`. Only symbolic
      # single-character operators like `-` may abut their operand.
      _ -> "#{op}#{unary_sep(op)}#{inner}"
    end
  end

  # -- Assignment (let binding) -----------------------------------------------

  defp to_string({:assignment, meta, [pattern, value]}, depth, indent) do
    type_ann =
      case Keyword.get(meta, :type_annotation) do
        nil -> ""
        type_ast -> ": #{render(type_ast, depth, indent)}"
      end

    lhs = render(pattern, depth, indent)
    rhs = rhs_to_string(value, depth, indent)

    if Keyword.get(meta, :let) do
      keyword = if Keyword.get(meta, :have), do: "have", else: "let"
      "#{keyword} #{lhs}#{type_ann} = #{rhs}"
    else
      "#{lhs} = #{rhs}"
    end
  end

  defp to_string({:proof_chain, _meta, [first | steps]}, depth, indent) do
    first_pad = String.duplicate(indent, depth + 1)
    step_pad = String.duplicate(indent, depth + 1)

    rendered_steps =
      steps
      |> Enum.with_index()
      |> Enum.map(fn {{:proof_step, _step_meta, [_marker, right, justification]}, index} ->
        right = render(right, depth + 1, indent)
        because = proof_justification_to_string(justification, depth, indent)

        if index == 0 do
          "#{first_pad}#{render(first, depth + 1, indent)} == #{right}\n#{first_pad}#{because}"
        else
          "#{step_pad}_ == #{right}\n#{step_pad}#{because}"
        end
      end)
      |> Enum.join("\n\n")

    "proof chain\n#{rendered_steps}"
  end

  # -- Conditional -----------------------------------------------------------

  defp to_string({:conditional, _meta, [condition, then_br, else_br]}, depth, indent) do
    cond_str = render(condition, depth, indent)

    case else_br do
      {:literal, meta, nil} when is_list(meta) ->
        if Keyword.get(meta, :subtype) == :null do
          "if #{cond_str} then #{render(then_br, depth, indent)}"
        else
          "if #{cond_str} then #{render(then_br, depth, indent)} else #{render(else_br, depth, indent)}"
        end

      {:conditional, _, _} ->
        # elif chain
        then_str = render(then_br, depth, indent)
        elif_str = conditional_to_elif(else_br, depth, indent)
        "if #{cond_str} then #{then_str} #{elif_str}"

      _ ->
        "if #{cond_str} then #{render(then_br, depth, indent)} else #{render(else_br, depth, indent)}"
    end
  end

  # -- Pattern Match (MATCH §9 -- Canonical Block Form) ---------------------
  #
  # Per the formal spec (`docs/MATCH.md` §9), the canonical surface form
  # of a `match` expression is a block: the keyword and its scrutinee on
  # one line, followed by clauses indented one `indent_step` deeper. The
  # `->` tokens are aligned within a single block (§9.2, §9.14).
  #
  # Single-clause matches whose pattern is irrefutable are rewritten to
  # the equivalent `let` binding (MATCH §9.6, hint H-MATCH-USE-LET).
  # Multi-line right-hand sides force every clause in the block into the
  # wrapped form (§9.9).

  defp to_string({:pattern_match, _meta, [scrutinee | arms]}, depth, indent) do
    cond do
      arms == [] ->
        # An empty `match` is malformed (E-MATCH-EMPTY), but the
        # printer must still produce some surface text so type-checker
        # diagnostics can attach to the keyword.
        "match #{render(scrutinee, depth, indent)}"

      true ->
        # MATCH §9.6 also describes a single-arm-irrefutable -> `let`
        # rewrite hint (`H-MATCH-USE-LET`). Since Cure's surface has no
        # `let … in …` form, the canonical printer leaves the `match`
        # unchanged here; a dedicated formatter pass may surface the
        # rewrite hint without altering the AST.
        render_match_block(scrutinee, arms, depth, indent)
    end
  end

  # -- Pickup (PICKUP §8 -- Canonical Block Form) ---------------------------
  #
  # Per the formal spec (`docs/PICKUP.md` §8), the canonical surface
  # form of a `pickup` expression is a block: the keyword on its own
  # line, followed by clauses indented one `indent_step` deeper. The
  # `->` tokens are aligned within a single block (§8.2, §8.14).
  #
  # A degenerate `pickup` -- whose only clause is the terminator -- is
  # rewritten to the body expression (§8.6, hint H-PICKUP-DEGENERATE).
  # A trailing `true ->` clause is normalised to `else ->` (§8.3, hint
  # H-PICKUP-PREFER-ELSE). Multi-line right-hand sides force every
  # clause into the wrapped form (§8.9).

  defp to_string({:pickup, _meta, clauses}, depth, indent) do
    clauses = normalize_pickup_terminator(clauses)

    case clauses do
      [{:pickup_else, _, [body]}] ->
        # PICKUP §8.6: degenerate `pickup` -- single terminator only --
        # collapses to the body.
        render(body, depth, indent)

      [] ->
        # The parser rejects this with E-PICKUP-NO-ELSE; for
        # defensive printing we still emit the keyword.
        "pickup"

      _ ->
        render_pickup_block(clauses, depth, indent)
    end
  end

  # -- Match Arm -------------------------------------------------------------

  defp to_string({:match_arm, meta, [body]}, depth, indent) do
    match_arm_to_string({:match_arm, meta, [body]}, depth, indent)
  end

  # Inline pickup clauses are not normally rendered on their own (the
  # `:pickup` clause above always handles them as a list), but we keep a
  # safe fallback so trees produced by macro expansion or partial
  # quoting still print legibly.
  defp to_string({:pickup_clause, _meta, [guard, body]}, depth, indent) do
    "#{render(guard, depth, indent)} -> #{render(body, depth, indent)}"
  end

  defp to_string({:pickup_else, _meta, [body]}, depth, indent) do
    "else -> #{render(body, depth, indent)}"
  end

  # -- Function Call ---------------------------------------------------------

  # `Tuple(T1, …, Tn)` type surface (n-ary telescope, `parse_tuple_type`). Each
  # position's binder is retained: an anonymous position (binder `"_"`) prints
  # just its type; a named position prints `b: T`, so a dependent telescope
  # (`Tuple(n: Nat, Vector(a, n))`) round-trips losslessly.
  defp to_string({:tuple_type, meta, types}, depth, indent) do
    binders = Keyword.get(meta, :binders, [])
    # Position-align binders with types in one O(n) pass. `binders` may be
    # shorter than `types` (an all-anonymous telescope carries none), so pad
    # with `nil` rather than re-reading `Enum.at(binders, i)` per position.
    padded = binders ++ List.duplicate(nil, max(length(types) - length(binders), 0))

    positions =
      types
      |> Enum.zip(padded)
      |> Enum.map_join(", ", fn
        {t, b} when is_binary(b) and b != "_" -> "#{b}: #{render(t, depth, indent)}"
        {t, _} -> render(t, depth, indent)
      end)

    "Tuple(#{positions})"
  end

  defp to_string({:named_call_argument, meta, [arg]}, depth, indent) do
    "#{Keyword.fetch!(meta, :label)}: #{render(arg, depth, indent)}"
  end

  defp to_string({:function_call, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name, "unknown")
    labels = Keyword.get(meta, :arg_labels)

    cond do
      # Record construction: Name{field: val}
      Keyword.get(meta, :record) == true ->
        fields_str = pairs_to_string(args, depth, indent)
        "#{name}{#{fields_str}}"

      # Send: send target, message
      name == "send" and not Keyword.has_key?(meta, :pipe) and is_nil(labels) ->
        case args do
          [target, message] ->
            "send #{render(target, depth, indent)}, #{render(message, depth, indent)}"

          _ ->
            "#{name}(#{call_args_to_string(args, depth, indent, labels)})"
        end

      # Pipe call. `|>` binds loosely (the `Pipe` group), so a left operand
      # whose own precedence is lower — a bare `<-|` send, a conditional — must
      # be parenthesised or the reprint reparses differently.
      Keyword.get(meta, :pipe) == true ->
        pipe_parent = prec_of("|>")

        case args do
          [piped | rest] when rest != [] ->
            rest_labels = if is_list(labels), do: Enum.drop(labels, 1), else: nil

            "#{operand_str(piped, depth, indent, pipe_parent, :left)} |> #{name}(#{call_args_to_string(rest, depth, indent, rest_labels)})"

          [piped] ->
            "#{operand_str(piped, depth, indent, pipe_parent, :left)} |> #{name}"

          [] ->
            name
        end

      true ->
        "#{quote_if_reserved(name)}(#{call_args_to_string(args, depth, indent, labels)})"
    end
  end

  # -- Record Update ----------------------------------------------------------

  defp to_string({:record_update, meta, [base | fields]}, depth, indent) do
    name = Keyword.get(meta, :name)
    base_str = render(base, depth, indent)
    fields_str = pairs_to_string(fields, depth, indent)
    "#{name}{#{base_str} | #{fields_str}}"
  end

  # -- Attribute Access (dot) ------------------------------------------------

  defp to_string({:attribute_access, meta, [parent]}, depth, indent) do
    attr = Keyword.get(meta, :attribute)
    # Dot access binds tightest (the `Dot` group); a lower-precedence base needs
    # parens or `(a + b).x` reprints as `a + b.x` (= `a + (b.x)`).
    "#{operand_str(parent, depth, indent, prec_of("."), :left)}.#{attr}"
  end

  # -- Range -----------------------------------------------------------------

  defp to_string({:range, meta, [left, right]}, depth, indent) do
    op = if Keyword.get(meta, :inclusive), do: "..=", else: ".."
    # Range binds in the non-associative `Range` group; operands that bind looser
    # need parens or `(a == b)..c` reprints as `a == b..c` (= `a == (b .. c)`).
    parent = prec_of("..")

    "#{operand_str(left, depth, indent, parent, :left)}#{op}#{operand_str(right, depth, indent, parent, :right)}"
  end

  # -- Collections -----------------------------------------------------------

  defp to_string({:list, meta, elements}, depth, indent) do
    if Keyword.get(meta, :cons) do
      case elements do
        [head, tail] ->
          "[#{render(head, depth, indent)} | #{render(tail, depth, indent)}]"

        _ ->
          "[#{args_to_string(elements, depth, indent)}]"
      end
    else
      "[#{args_to_string(elements, depth, indent)}]"
    end
  end

  defp to_string({:tuple, meta, elements}, depth, indent) do
    # A tuple in TYPE position (`(A, B)`, e.g. `List((String, String))`) is
    # parsed with empty meta, whereas a VALUE tuple `%[a, b]` carries the
    # lexer's line/col. Render each back in its own surface syntax so a type
    # tuple round-trips as `(A, B)` rather than the value form `%[A, B]`
    # (which is not valid in a type position).
    if meta == [] do
      "(#{args_to_string(elements, depth, indent)})"
    else
      "%[#{args_to_string(elements, depth, indent)}]"
    end
  end

  defp to_string({:map, _meta, pairs}, depth, indent) do
    "%{#{pairs_to_string(pairs, depth, indent)}}"
  end

  defp to_string({:pair, _meta, [key, value]}, depth, indent) do
    pair_to_string(key, value, depth, indent)
  end

  # -- Comprehension ---------------------------------------------------------

  defp to_string({:comprehension, _meta, [body | generators_and_filters]}, depth, indent) do
    body_str = render(body, depth, indent)
    clauses = Enum.map(generators_and_filters, &gen_or_filter_to_string(&1, depth, indent))
    "[#{body_str} for #{Enum.join(clauses, ", ")}]"
  end

  defp to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    gen_or_filter_to_string({:generator, [], [pattern, collection]}, depth, indent)
  end

  defp to_string({:filter, _meta, [expr]}, depth, indent) do
    gen_or_filter_to_string({:filter, [], [expr]}, depth, indent)
  end

  # -- String Interpolation --------------------------------------------------

  defp to_string({:string_interpolation, _meta, parts}, depth, indent) do
    inner =
      Enum.map_join(parts, fn
        {:literal, meta, s} when is_list(meta) and is_binary(s) ->
          if Keyword.get(meta, :subtype) == :string do
            escape_string(s)
          else
            "\#{#{render({:literal, meta, s}, depth, indent)}}"
          end

        expr ->
          "\#{#{render(expr, depth, indent)}}"
      end)

    ~s("#{inner}")
  end

  # -- Lambda ----------------------------------------------------------------

  defp to_string({:lambda, meta, [body]}, depth, indent) do
    params = Keyword.get(meta, :params, [])
    params_str = Enum.map_join(params, ", ", fn {:param, _, name} -> name end)

    if has_leading?(body) do
      # A leading comment on the body can't ride inline after `-> ` — it would
      # strand `# c\nbody` mid-line and drift to the file top on reparse. Break to
      # an indented line so the comment stays attached to the body it precedes.
      pad = String.duplicate(indent, depth + 1)
      "fn(#{params_str}) ->\n" <> pad <> lambda_body_to_string(body, depth + 1, indent)
    else
      body_str = lambda_body_to_string(body, depth, indent)
      "fn(#{params_str}) -> #{body_str}"
    end
  end

  # -- Function Definition ---------------------------------------------------

  defp to_string({:function_def, meta, body}, depth, indent) do
    fn_def_to_string(meta, body, depth, indent)
  end

  defp to_string({:lift_module, meta, []}, depth, indent) do
    name = lift_module_name_to_string(Keyword.get(meta, :module))
    pad = String.duplicate(indent, depth + 1)

    lines =
      [
        if(Keyword.get(meta, :behaviour), do: "behaviour #{Keyword.get(meta, :behaviour)}"),
        Enum.map(Keyword.get(meta, :callbacks, []), &lift_callback_to_string(&1, depth + 1, indent)),
        Enum.map(Keyword.get(meta, :declarations, []), &render(&1, depth + 1, indent))
      ]
      |> List.flatten()
      |> Enum.reject(&is_nil/1)

    body = Enum.join(lines, "\n#{pad}")
    "lift module #{name}\n#{pad}#{body}"
  end

  # A `computed directly by` / `computed by` macro invocation that deferred to
  # the elaborator parses to `:computed_use`. Reconstruct the surface call from
  # the matched rule's segments (carried on the node as `:syntax_segments`)
  # interleaved with the parsed arguments: a file being reprinted has no access
  # to the stdlib rule that defined the macro, so the literal separators
  # (`state`/`messages`/…) and hole order must travel on the node itself. Without
  # this clause `cure fmt`/`migrate` RAISED UnprintableNodeError on every actor
  # demo built on the folded `computed directly by` surface (examples/**).
  defp to_string({:computed_use, meta, [_elab, {:macro_input, _mi, args}]}, depth, indent) do
    keyword = Keyword.fetch!(meta, :keyword)

    case {keyword, args} do
      {"regex",
       [
         {:literal, _pattern_meta, pattern},
         {:literal, _flags_meta, flags}
       ]}
      when is_binary(pattern) and is_binary(flags) ->
        "/" <> pattern <> "/" <> flags

      _ ->
        segments = Keyword.get(meta, :syntax_segments, [])
        pad = String.duplicate(indent, depth + 1)
        {rendered, _leftover} = computed_use_segments(segments, args, depth, indent, pad)
        keyword <> Enum.join(rendered, "")
    end
  end

  # -- Container (module, record, enum, protocol, and trait) ----------------

  defp to_string({:container, meta, body}, depth, indent) do
    container_to_string(meta, body, depth, indent)
  end

  # -- Type Annotation -------------------------------------------------------

  defp to_string({:type_annotation, meta, children}, depth, indent) do
    type_annotation_to_string(meta, children, depth, indent)
  end

  # -- Import ----------------------------------------------------------------

  defp to_string({:import, meta, _children}, _depth, _indent) do
    source = Keyword.get(meta, :source)
    items = Keyword.get(meta, :items)
    alias_name = Keyword.get(meta, :alias)

    base = "use #{source}"

    base =
      if items && items != [] do
        base <> ".{#{Enum.join(items, ", ")}}"
      else
        base
      end

    if alias_name do
      base <> " as #{alias_name}"
    else
      base
    end
  end

  # -- Early Return / Throw / Yield / Spawn ---------------------------------

  defp to_string({:early_return, _meta, [expr]}, depth, indent) do
    "return #{render(expr, depth, indent)}"
  end

  # Melquiades send node. The author's chosen surface form is carried on
  # meta[:melquiades_form]:
  #
  #   :ascii    -> `target <-| message`
  #   :unicode  -> `target ✉ message`
  #   :keyword  -> `send target, message` (the statement form)
  #
  # Any other value falls back to the ASCII operator form.
  defp to_string({:send, meta, [target, message]}, depth, indent) do
    # The Melquiades send operator binds in the non-associative `Melquiades`
    # group; operands that bind looser need parens or `(pid <-| msg) + 1`
    # reprints as `pid <-| msg + 1` (= `pid <-| (msg + 1)`).
    parent = prec_of("<-|")
    target_str = operand_str(target, depth, indent, parent, :left)
    message_str = operand_str(message, depth, indent, parent, :right)

    case Keyword.get(meta, :melquiades_form, :ascii) do
      :unicode -> "#{target_str} ✉ #{message_str}"
      :keyword -> "send #{target_str}, #{message_str}"
      _ -> "#{target_str} <-| #{message_str}"
    end
  end

  defp to_string({:throw, _meta, [expr]}, depth, indent) do
    "throw #{render(expr, depth, indent)}"
  end

  defp to_string({:yield, _meta, [expr]}, depth, indent) do
    "yield #{render(expr, depth, indent)}"
  end

  defp to_string({:async_operation, meta, children}, depth, indent) do
    case Keyword.get(meta, :timeout) do
      nil when children == [] ->
        "receive"

      nil ->
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"

      _ ->
        # receive with timeout
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"
    end
  end

  # -- Exception Handling ----------------------------------------------------

  defp to_string({:exception_handling, _meta, children}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    case children do
      [try_body | rest] ->
        try_str = "try\n#{pad}#{render(try_body, depth + 1, indent)}"

        {catch_arms, rest} =
          Enum.split_while(rest, fn
            {:match_arm, _, _} -> true
            _ -> false
          end)

        catch_str =
          if catch_arms != [] do
            arms =
              catch_arms
              |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
              |> Enum.join("\n#{pad}")

            "\ncatch\n#{pad}#{arms}"
          else
            ""
          end

        finally_str =
          case rest do
            [finally_body] ->
              "\nfinally\n#{pad}#{render(finally_body, depth + 1, indent)}"

            _ ->
              ""
          end

        "#{try_str}#{catch_str}#{finally_str}"

      _ ->
        "try"
    end
  end

  # -- Decorator / Property --------------------------------------------------

  defp to_string({:decorator, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name)
    "@#{name}(#{args_to_string(args, depth, indent)})"
  end

  defp to_string({:property, meta, _value}, _depth, _indent) do
    name = Keyword.get(meta, :name)
    "@#{name}"
  end

  # -- Line comment ----------------------------------------------------------

  defp to_string({:comment, _meta, text}, _depth, _indent) when is_binary(text) do
    # v0.20.0: free-standing `#` comment nodes round-trip as `# <text>`.
    "# " <> text
  end

  # -- Binary segment --------------------------------------------------------
  #
  # Round-trips the v0.20.0 segment AST back into surface syntax.
  # A segment with no specifiers renders as the plain value; otherwise
  # the specifier chain is emitted as `::type-signedness-endianness-size-unit`.

  defp to_string({:bin_segment, meta, [value]}, depth, indent) do
    value_str = render(value, depth, indent)
    spec_str = bin_segment_specifier_string(meta, depth, indent)

    if spec_str == "" do
      value_str
    else
      "#{value_str}::#{spec_str}"
    end
  end

  # -- Pin pattern (v0.18.0) -------------------------------------------------
  #
  # `^name` references a previously-bound variable in a pattern rather than
  # rebinding it.

  defp to_string({:pin, _meta, [inner]}, depth, indent) do
    "^" <> render(inner, depth, indent)
  end

  # -- As-pattern (`name @ inner`) -------------------------------------------
  #
  # Binds the whole matched value to `name` in addition to destructuring it.
  # The name is a bare string; the inner is the destructuring pattern.

  defp to_string({:as_pattern, _meta, [name, inner]}, depth, indent) when is_binary(name) do
    name <> " @ " <> render(inner, depth, indent)
  end

  # -- Forced (dot) pattern (`.x` / `.(compound)`) ---------------------------
  #
  # A leading `.` marks a forced-equation pattern: the inner term is a value
  # the scrutinee must be convertible with, not a fresh binder. A bare
  # variable/literal prints as `.x`; anything compound prints as `.(...)`.

  defp to_string({:forced_pattern, _meta, [inner]}, depth, indent) do
    inner_str = render(inner, depth, indent)

    case inner do
      {:variable, _, _} -> "." <> inner_str
      {:literal, _, _} -> "." <> inner_str
      _ -> ".(" <> inner_str <> ")"
    end
  end

  # -- Named-implicit dot pattern (`{ name = inner }`) -----------------------
  #
  # Annotates a constructor's erased implicit index `name` with a forced
  # value in a pattern-argument position. This is a 4-tuple node, not the
  # standard `{tag, meta, children}` shape.

  defp to_string({:named_implicit_pat, meta, [inner]}, depth, indent) do
    "{ " <> Keyword.get(meta, :name) <> " = " <> render(inner, depth, indent) <> " }"
  end

  # -- Hole (`?name` / `?_`) -------------------------------------------------
  #
  # Anonymous holes carry `_`; compiler-generated `???` placeholders carry `?`.

  defp to_string({:hole, meta, _children}, _depth, _indent) do
    case Keyword.get(meta, :name) do
      "?" -> "???"
      name -> "?" <> name
    end
  end

  # -- assert_type (`assert_type expr : Type`) -------------------------------

  defp to_string({:assert_type, _meta, [expr, type_ast]}, depth, indent) do
    "assert_type " <> render(expr, depth, indent) <> " : " <> render(type_ast, depth, indent)
  end

  # -- Dependent function type (Π) -------------------------------------------
  #
  # `(x: A, B) -> C` — at least one named domain. `binders` carries one entry
  # per domain (nil for an anonymous domain); the children are the domains
  # followed by the codomain.

  defp to_string({:pi_type, meta, children}, depth, indent) do
    binders = Keyword.get(meta, :binders, [])
    {doms, [ret]} = Enum.split(children, length(children) - 1)

    dom_strs =
      binders
      |> Enum.zip(doms)
      |> Enum.map(fn
        {nil, d} -> render(d, depth, indent)
        {name, d} -> "#{name}: #{render(d, depth, indent)}"
      end)

    "(" <> Enum.join(dom_strs, ", ") <> ") -> " <> render(ret, depth, indent)
  end

  # -- Dependent pair type (Σ) -----------------------------------------------
  #
  # `Sigma(x: DomType, BodyType)`.

  defp to_string({:sigma_type, meta, [dom_type, body_type]}, depth, indent) do
    binder = Keyword.get(meta, :binder)

    "Sigma(" <>
      binder <>
      ": " <>
      render(dom_type, depth, indent) <>
      ", " <> render(body_type, depth, indent) <> ")"
  end

  # Proof-backed refinement type: `{value: Base | Proposition}`.
  defp to_string({:refinement_type, meta, [base_type, proposition]}, depth, indent) do
    binder = Keyword.get(meta, :binder)

    "{" <>
      binder <>
      ": " <>
      render(base_type, depth, indent) <>
      " | " <> render(proposition, depth, indent) <> "}"
  end

  # -- Typed pattern ----------------------------------------------------------

  # `n: Int` in a match arm — binds `n` at the annotated type. The annotation may
  # itself be a union (`rest: String | Bool`).
  defp to_string({:typed_pattern, _meta, [name, type_ast]}, depth, indent) do
    name <> ": " <> render(type_ast, depth, indent)
  end

  # -- Anonymous union type ---------------------------------------------------

  # `Int | String`. Members print in SOURCE order — canonicalisation (sort, dedupe,
  # flatten) happens in the elaborator, not here, so printing stays lossless.
  defp to_string({:union_type, _meta, members}, depth, indent) do
    Enum.map_join(members, " | ", &render(&1, depth, indent))
  end

  # -- GADT constructor signature --------------------------------------------
  #
  # `Name : Dom -> ... -> Result`. The third slot contains one canonical
  # `:arrow_chain` node. A `:named_dom` child carries a dependent binder
  # `(name: Type)` in its own metadata and child list.

  defp to_string({:gadt_ctor, meta, [{:arrow_chain, _chain_meta, elems}]}, depth, indent) do
    name = Keyword.get(meta, :name)

    chain =
      Enum.map_join(elems, " -> ", fn
        {:named_dom, dom_meta, [inner]} ->
          dname = Keyword.fetch!(dom_meta, :name)
          inner_rendered = render_ctor_function_type(inner, depth, indent)

          inner_rendered =
            case inner do
              {:pi_type, _, _} ->
                "(" <> inner_rendered <> ")"

              {:function_call, function_meta, _} ->
                if Keyword.get(function_meta, :function_type),
                  do: "(" <> inner_rendered <> ")",
                  else: inner_rendered

              _ ->
                inner_rendered
            end

          case Keyword.get(dom_meta, :grade) do
            nil -> "(#{dname}: #{inner_rendered})"
            grade -> "(@#{grade} #{dname} : #{inner_rendered})"
          end

        # A RELEVANT IMPLICIT binder `{name: Type}` — implicit (solved, omitted at
        # the call site) yet retained (ω). Parallel to `:named_dom` but braced.
        {:implicit_dom, dom_meta, [inner]} ->
          dname = Keyword.fetch!(dom_meta, :name)
          inner_rendered = render_ctor_function_type(inner, depth, indent)

          inner_rendered =
            case inner do
              {:pi_type, _, _} ->
                "(" <> inner_rendered <> ")"

              {:function_call, function_meta, _} ->
                if Keyword.get(function_meta, :function_type),
                  do: "(" <> inner_rendered <> ")",
                  else: inner_rendered

              _ ->
                inner_rendered
            end

          "{#{dname}: #{inner_rendered}}"

        # A function-typed constructor FIELD must stay grouped away from the
        # constructor's own arrow telescope. Without this outer pair, a field
        # parsed from `((rest: A) -> B(rest))` prints as `(rest: A) -> B(rest)`;
        # reparsing then mistakes `rest` for a constructor-level named field.
        {:pi_type, _, _} = function_type ->
          "(" <> render_ctor_function_type(function_type, depth, indent) <> ")"

        {:function_call, function_meta, _} = function_type ->
          if Keyword.get(function_meta, :function_type),
            do: "(" <> render_ctor_function_type(function_type, depth, indent) <> ")",
            else: render(function_type, depth, indent)

        other ->
          render(other, depth, indent)
      end)

    "#{name} : #{chain}"
  end

  # -- Indexed (GADT) type family --------------------------------------------
  #
  # `type Name[(params)] indices (indices)` followed by an indented block of
  # GADT constructor signatures. A `@builtin(:key)`-style decorator threaded
  # into `meta[:decorator]` prints on the preceding line.

  defp to_string({:indexed_type, meta, ctors}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])
    indices = Keyword.get(meta, :indices, [])

    params_str =
      if params == [], do: "", else: "(#{typed_params_to_string(params, depth, indent)})"

    header = "type #{name}#{params_str} indices (#{typed_params_to_string(indices, depth, indent)})"
    body_pad = String.duplicate(indent, depth + 1)

    ctors_str =
      ctors
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{body_pad}")

    type_block = "#{header}\n#{body_pad}#{ctors_str}"

    case Keyword.get(meta, :decorator) do
      nil ->
        type_block

      {:decorator, dm, args} ->
        dec_name = Keyword.get(dm, :name)
        self_pad = String.duplicate(indent, depth)
        "@#{dec_name}(#{args_to_string(args, depth, indent)})\n#{self_pad}#{type_block}"
    end
  end

  # -- Interface (typeclass declaration) -------------------------------------
  #
  # `interface Name[(params)]` followed by an indented block of method
  # signatures / defaults.

  defp to_string({:interface, meta, body}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])

    params_str = if params == [], do: "", else: "(#{Enum.join(params, ", ")})"
    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "interface #{name}#{params_str}\n#{pad}#{body_str}"
  end

  # -- Implementation (typeclass instance) -----------------------------------
  #
  # `implementation Iface for Type [as Name] [requires constraints]` followed by
  # an indented block of method definitions.

  defp to_string({:implementation, meta, body}, depth, indent) do
    iface = Keyword.get(meta, :interface)
    for_type = Keyword.get(meta, :for_type)
    as_name = Keyword.get(meta, :as)
    constraints = Keyword.get(meta, :constraints, [])

    as_str = if as_name, do: " as #{as_name}", else: ""

    requirements_str =
      if constraints != [] do
        " requires " <> Enum.map_join(constraints, ", ", &render(&1, depth, indent))
      else
        ""
      end

    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    head =
      "implementation #{iface} for #{render(for_type, depth, indent)}#{as_str}#{requirements_str}"

    "#{head}\n#{pad}#{body_str}"
  end

  # -- With-abstraction (capability A) ---------------------------------------
  #
  # `with <scrut> [proof <name>]` with match arms, refining the goal by the
  # scrutinee's value. Rendered like `match` but with the `with` keyword.

  defp to_string({:with_abs, meta, [scrutinee | arms]}, depth, indent) do
    proof = Keyword.get(meta, :proof)
    proof_str = if proof, do: " proof #{proof}", else: ""

    case arms do
      [] -> "with " <> render(scrutinee, depth, indent) <> proof_str
      _ -> render_scrutinee_block("with ", scrutinee, proof_str, arms, depth, indent)
    end
  end

  # -- Binary generator (`<<pat <- source>>`) --------------------------------
  #
  # A comprehension qualifier that iterates a bitstring. The pattern is a
  # bytes literal whose segments are rendered inline between `<<` and `<-`.

  defp to_string({:binary_generator, _meta, [pattern, source]}, depth, indent) do
    pat_inner =
      case pattern do
        {:literal, _, segs} when is_list(segs) ->
          Enum.map_join(segs, ", ", &render(&1, depth, indent))

        _ ->
          render(pattern, depth, indent)
      end

    "<<" <> pat_inner <> " <- " <> render(source, depth, indent) <> ">>"
  end

  # -- Propositional-equality rewrite (`rewrite proof in body`) --------------

  defp to_string({:rewrite_expr, _meta, [proof, body]}, depth, indent) do
    "rewrite " <> render(proof, depth, indent) <> " in " <> render(body, depth, indent)
  end

  defp to_string({:rewrite_command, meta, [proof]}, depth, indent) do
    direction = if Keyword.get(meta, :direction) == :backwards, do: " backwards", else: ""

    target =
      case Keyword.get(meta, :target, :goal) do
        :goal -> ""
        {:at, occurrence} -> " at #{occurrence}"
        {:in, name} -> " in #{name}"
      end

    "rewrite#{direction} using " <> render(proof, depth, indent) <> target
  end

  defp to_string({:simplify_command, _meta, []}, _depth, _indent), do: "simplify"

  defp to_string({:simplify_command, _meta, [rules]}, depth, indent),
    do: "simplify using " <> render(rules, depth, indent)

  defp to_string({:induction, _meta, [subject | cases]}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    rendered =
      cases
      |> Enum.map(fn {:induction_case, _case_meta, [pattern, body]} ->
        body_text = if is_nil(body), do: "impossible", else: render(body, depth + 1, indent)

        if String.contains?(body_text, "\n") do
          nested = body_text |> String.split("\n") |> Enum.map_join("\n", &(pad <> indent <> &1))
          "#{pad}case #{render(pattern, depth + 1, indent)} =>\n#{nested}"
        else
          "#{pad}case #{render(pattern, depth + 1, indent)} => #{body_text}"
        end
      end)
      |> Enum.join("\n\n")

    "induction #{render(subject, depth, indent)}\n#{rendered}"
  end

  # -- Macro definitions -----------------------------------------------------

  defp to_string({:macro_def, meta, rules}, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)

    # A structured-family macro carries header params (`macro actor <name:
    # ModuleName>`) in `leading_segments`; render them so the header round-trips.
    header =
      case Keyword.get(meta, :leading_segments, []) do
        [] -> "macro #{name}"
        segments -> "macro #{name} #{macro_segments_to_string(segments)}"
      end

    body =
      rules
      |> Enum.flat_map(&macro_rule_lines(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")
      |> String.split("\n")
      |> Enum.reject(&(String.trim(&1) == ""))
      |> Enum.join("\n")

    "#{header}\n#{pad}#{body}"
  end

  # -- Fixity declarations (Phase 3) ----------------------------------------
  #
  # `precedencegroup`/`infix`/`prefix`/`postfix` reprint to the exact surface the
  # parser accepts (parser.ex `parse_precedencegroup`/`parse_fixity`). Operator
  # lexemes are always backtick-quoted so any symbolic spelling (`+`, `<>`, `..`)
  # round-trips through the lexer as a single identifier token, keeping
  # print∘reparse a fixpoint regardless of the operator's other lexical role.
  defp to_string({:precedencegroup, meta, _}, depth, indent) do
    name = Atom.to_string(Keyword.fetch!(meta, :name))
    pad = String.duplicate(indent, depth + 1)

    fields =
      [
        case Keyword.get(meta, :assoc) do
          nil -> nil
          assoc -> "associativity: #{assoc}"
        end,
        precedencegroup_names_field("higher_than", Keyword.get(meta, :higher_than)),
        precedencegroup_names_field("lower_than", Keyword.get(meta, :lower_than))
      ]
      |> Enum.reject(&is_nil/1)

    case fields do
      [] -> "precedencegroup #{name}"
      _ -> "precedencegroup #{name}\n#{pad}" <> Enum.join(fields, "\n#{pad}")
    end
  end

  defp to_string({:fixity, meta, _}, _depth, _indent) do
    builtin = if Keyword.get(meta, :builtin, false), do: "builtin ", else: ""
    fixity = Keyword.fetch!(meta, :fixity)
    op = Keyword.fetch!(meta, :operator)
    group = Atom.to_string(Keyword.fetch!(meta, :group))
    "#{builtin}#{fixity} `#{op}` : #{group}"
  end

  # -- Quasiquotation (`quote <form>`, `$(e)`, `$(e ...)`) -------------------

  # SP5.1 surface sugar (parser.ex `parse_quote`/`parse_splice`). The printer
  # backs `cure fmt`/`migrate`, and the stdlib now quotes (fsm/actor/app/
  # supervisor), so these must reprint to the exact surface that reparses to the
  # same node — not raise. A splice is legal only inside a quote, so its clause
  # only fires while rendering a quoted form's inner tree.
  defp to_string({:quoted_syntax, _meta, [inner]}, depth, indent) do
    "quote " <> render(inner, depth, indent)
  end

  defp to_string({:splice, _meta, [expr]}, depth, indent) do
    "$(" <> render(expr, depth, indent) <> ")"
  end

  defp to_string({:splice_group, _meta, [expr]}, depth, indent) do
    "$(" <> render(expr, depth, indent) <> " ...)"
  end

  # Optional captures inside a source-defined syntax-family production retain
  # an explicit wrapper in the parser AST. At the surface, however, absence is
  # represented by no tokens and presence by the captured value itself.
  defp to_string({:family_option, meta, []}, _depth, _indent) when is_list(meta), do: ""

  defp to_string({:family_option, meta, [values]}, depth, indent)
       when is_list(meta) and is_list(values),
       do: render_family_production_values(values, depth, indent)

  defp to_string({:family_option, meta, [value]}, depth, indent) when is_list(meta),
    do: render(value, depth, indent)

  defp to_string(other, _depth, _indent) when is_binary(other), do: other

  defp to_string(other, _depth, _indent) do
    raise Cure.Compiler.Printer.UnprintableNodeError, node: other
  end

  # `higher_than:` / `lower_than:` group-name lists for a `precedencegroup` body
  # (see the `:precedencegroup` clause above). `nil`/`[]` omit the line entirely.
  defp precedencegroup_names_field(_key, nil), do: nil
  defp precedencegroup_names_field(_key, []), do: nil

  defp precedencegroup_names_field(key, names) when is_list(names) do
    "#{key}: " <> Enum.map_join(names, " ", &Atom.to_string/1)
  end

  # Constructor fields use a dedicated arrow-chain grammar. A multi-domain Π
  # that the general printer writes `(rest: A, Proof(rest)) -> Result(rest)` must
  # therefore be rendered here as `(rest: A) -> Proof(rest) -> Result(rest)`;
  # both denote the same Π telescope, but only the latter is accepted inside the
  # constructor parser's grouped field production.
  defp render_ctor_function_type({:pi_type, meta, children}, depth, indent) do
    binders = Keyword.get(meta, :binders, [])
    {domains, [result]} = Enum.split(children, length(children) - 1)

    domains =
      binders
      |> Enum.zip(domains)
      |> Enum.map(fn
        {nil, domain} -> render(domain, depth, indent)
        {name, domain} -> "(#{name}: #{render(domain, depth, indent)})"
      end)

    Enum.join(domains ++ [render(result, depth, indent)], " -> ")
  end

  defp render_ctor_function_type(
         {:function_call, meta, children} = function_type,
         depth,
         indent
       ) do
    if Keyword.get(meta, :function_type) do
      {domains, [result]} = Enum.split(children, length(children) - 1)
      domains = Enum.map(domains, &("(" <> render(&1, depth, indent) <> ")"))
      Enum.join(domains ++ [render(result, depth, indent)], " -> ")
    else
      render(function_type, depth, indent)
    end
  end

  defp render_ctor_function_type(other, depth, indent), do: render(other, depth, indent)

  defp lift_module_name_to_string({:macro_hole, name}), do: name
  defp lift_module_name_to_string({:macro_path_hole, prefix, name}), do: prefix <> "." <> name
  defp lift_module_name_to_string(name), do: to_string(name)

  defp lift_callback_to_string(%{name: name, params: params, body: body}, depth, indent) do
    header = "callback #{name}(#{typed_params_to_string(params, depth, indent)}) ->"

    case body do
      {:block, _meta, _exprs} ->
        body_depth = depth + 1
        pad = String.duplicate(indent, body_depth)
        header <> "\n" <> pad <> render(body, body_depth, indent)

      _ ->
        header <> " " <> render(body, depth, indent)
    end
  end

  defp macro_rule_lines(%{kind: kind, keyword: keyword, segments: segments, template: template} = rule, depth, indent)
       when kind in [:syntax, :computed] do
    verb =
      cond do
        kind == :computed and rule[:direct_inputs] -> "computed directly by"
        kind == :computed -> "computed by"
        true -> "becomes"
      end

    obligations = macro_obligations_to_string(rule)
    context = if rule[:contextual], do: " contextual", else: ""

    head =
      "syntax #{keyword} #{macro_segments_to_string(segments)}#{obligations}#{context} #{verb} #{render(template, depth, indent)}"

    [head | macro_rule_examples(rule, depth, indent)]
  end

  # A Tier-3 `computed by <fn>` rule stores its expander in `:elab` and carries no
  # `:template`, so the clause above (which requires `template`) never matched it
  # and the catch-all dropped it — silently deleting the legacy `syntax actor …
  # computed by derive_actor` rule (whence the generated `ActorSyntax` record).
  defp macro_rule_lines(%{kind: :computed, keyword: keyword, segments: segments, elab: elab} = rule, depth, indent) do
    obligations = macro_obligations_to_string(rule)
    context = if rule[:contextual], do: " contextual", else: ""
    verb = if rule[:direct_inputs], do: "computed directly by", else: "computed by"

    head =
      "syntax #{keyword} #{macro_segments_to_string(segments)}#{obligations}#{context} #{verb} #{render(elab, depth, indent)}"

    [head | macro_rule_examples(rule, depth, indent)]
  end

  defp macro_rule_lines(%{kind: :literal, segments: segments, template: template}, depth, indent),
    do: ["literal #{macro_segments_to_string(segments)} becomes #{render(template, depth, indent)}"]

  defp macro_rule_lines(%{kind: :explain, clauses: clauses}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    lines =
      Enum.map(clauses, fn %{point: point, body: body} ->
        "#{macro_point_to_string(point)} => #{render(body, depth + 1, indent)}"
      end)

    ["explain\n#{pad}" <> Enum.join(lines, "\n#{pad}")]
  end

  # Structured-family macro body (parser.ex `parse_syntax_family` /
  # `parse_macro_accepts` / `parse_macro_expands_with`). Without these clauses the
  # catch-all below dropped the entire family declaration on reprint, so `cure
  # fmt`/`migrate` silently deleted the structured OTP surface (actor/fsm.cure).
  defp macro_rule_lines(%{kind: :syntax_family, name: name} = rule, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    include_lines =
      rule
      |> Map.get(:includes, [])
      |> Enum.map(fn {inc, _line, _col} -> "includes #{inc}" end)

    field_lines =
      rule
      |> Map.get(:fields, [])
      |> Enum.map(&family_field_to_string/1)

    production_lines =
      rule
      |> Map.get(:productions, [])
      |> Enum.map(&("syntax " <> macro_production_segments_to_string(&1.segments)))

    ["syntax family #{name}\n#{pad}" <> Enum.join(include_lines ++ production_lines ++ field_lines, "\n#{pad}")]
  end

  defp macro_rule_lines(%{kind: :accepts, family: family}, _depth, _indent),
    do: ["accepts #{family}"]

  defp macro_rule_lines(%{kind: :expands_with, expander: expander}, depth, indent),
    do: ["expands with #{render(expander, depth, indent)}"]

  defp macro_rule_lines(_rule, _depth, _indent), do: []

  defp macro_rule_examples(rule, depth, indent) do
    rule
    |> Map.get(:examples, [])
    |> Enum.map(fn example ->
      use_site = macro_use_site_to_string(example.use_site)
      expected = render(elem(example.expected, 1), depth + 1, indent)
      "#{String.duplicate(indent, max(depth - 1, 0))}example #{use_site} expands #{expected}"
    end)
  end

  # A `syntax family` field: `[optional|repeated|one_or_more] <name> <Shape>`.
  defp family_field_to_string(%{name: name, shape: shape} = field) do
    prefix =
      case Map.get(field, :cardinality, :required) do
        :optional -> "optional "
        :repeated -> "repeated "
        :one_or_more -> "one_or_more "
        _ -> ""
      end

    "#{prefix}#{name} #{shape}#{macro_obligations_to_string(field)}"
  end

  defp macro_obligations_to_string(owner) do
    owner
    |> Map.get(:obligations, [])
    |> Enum.map_join("", fn %{interface: interface, capture: capture} ->
      " where #{interface}(#{capture})"
    end)
  end

  # Reconstruct a `:computed_use` invocation's surface by walking the matched
  # rule's segments and interleaving literals with the parsed arguments (which
  # arrive in the same segment order, one per hole segment).
  defp computed_use_segments(segments, args, depth, indent, pad) do
    Enum.reduce(segments, {[], args}, fn segment, {acc, remaining} ->
      {piece, rest} = computed_use_segment(segment, remaining, depth, indent, pad)
      {acc ++ [piece], rest}
    end)
  end

  defp computed_use_segment({:lit, word}, args, _depth, _indent, _pad), do: {" " <> word, args}

  # A `<name: ModuleName>` hole binds a symbol literal (`:"Cure.Echo"`); the
  # surface writes it bare (`Cure.Echo`), so it must NOT go through the symbol
  # renderer (which would prefix a colon and break the reparse).
  defp computed_use_segment({:hole, %{kind: "ModuleName"}}, [arg | rest], depth, indent, _pad),
    do: {" " <> computed_use_module_name(arg, depth, indent), rest}

  defp computed_use_segment({:hole, _}, [arg | rest], depth, indent, _pad),
    do: {" " <> render(arg, depth, indent), rest}

  defp computed_use_segment(
         {:family, %{fields: fields}},
         [{:family_input, _meta, values} | rest],
         depth,
         indent,
         pad
       ) do
    rendered =
      fields
      |> Enum.zip(values)
      |> Enum.flat_map(fn {field, value} -> render_family_capture(field, value, depth, indent, pad) end)
      |> Enum.join("")

    {rendered, rest}
  end

  defp computed_use_segment({kind, %{delimiter: "dedent"}}, [arg | rest], depth, indent, pad)
       when kind in [:code_hole, :raw_hole, :declarations_hole],
       do: {"\n" <> pad <> render(arg, depth + 1, indent), rest}

  defp computed_use_segment({kind, _}, [arg | rest], depth, indent, _pad)
       when kind in [:code_hole, :raw_hole, :declarations_hole],
       do: {" " <> render(arg, depth, indent), rest}

  defp computed_use_module_name({:literal, _meta, value}, _depth, _indent) when is_atom(value),
    do: Atom.to_string(value)

  defp computed_use_module_name(arg, depth, indent), do: render(arg, depth, indent)

  defp render_family_capture(%{name: name, cardinality: :optional}, {:family_option, meta, values}, depth, indent, pad) do
    if Keyword.get(meta, :present, false) do
      Enum.flat_map(values, fn value ->
        ["\n#{pad}#{name}" | render_family_capture_value(value, depth, indent, pad)]
      end)
    else
      []
    end
  end

  defp render_family_capture(
         %{grammar: %{productions: productions, fields: grammar_fields}},
         {:family_input, _meta, values},
         depth,
         indent,
         pad
       ) do
    bindings = Map.new(Enum.zip(Enum.map(grammar_fields, & &1.name), values))
    production = select_family_production(productions, bindings)
    head = render_family_production(production.segments, bindings, depth, indent)

    nested =
      grammar_fields
      |> Enum.reject(&(&1.name in production.fields))
      |> Enum.flat_map(fn field ->
        render_family_capture(field, Map.get(bindings, field.name), depth + 1, indent, pad <> indent)
      end)
      |> Enum.join("")

    ["\n#{pad}#{head}#{nested}"]
  end

  defp render_family_capture(%{cardinality: cardinality} = field, values, depth, indent, pad)
       when cardinality in [:repeated, :one_or_more] and is_list(values),
       do: Enum.flat_map(values, &render_family_capture(field, &1, depth, indent, pad))

  defp render_family_capture(%{name: name}, value, depth, indent, pad),
    do: ["\n#{pad}#{name}" | render_family_capture_value(value, depth, indent, pad)]

  defp select_family_production(productions, bindings) do
    participating_fields = productions |> Enum.flat_map(& &1.fields) |> MapSet.new()

    Enum.find(productions, List.first(productions), fn production ->
      Enum.all?(participating_fields, fn name ->
        case Map.get(bindings, name) do
          {:family_option, meta, _} when is_list(meta) ->
            Keyword.get(meta, :present, false) == name in production.fields

          _ ->
            name in production.fields
        end
      end)
    end)
  end

  defp render_family_capture_value({:case_block, _meta, arms}, depth, indent, pad) do
    body_pad = pad <> indent
    ["\n", body_pad, Enum.map_join(arms, "\n#{body_pad}", &render(&1, depth + 2, indent))]
  end

  defp render_family_capture_value({:declarations_block, _meta, declarations}, depth, indent, pad)
       when is_list(declarations) do
    body_pad = pad <> indent

    [
      "\n",
      body_pad,
      Enum.map_join(declarations, "\n#{body_pad}", &render(&1, depth + 2, indent))
    ]
  end

  defp render_family_capture_value(value, depth, indent, _pad),
    do: [" ", render(value, depth + 1, indent)]

  defp render_family_production(segments, bindings, depth, indent) do
    {pieces, _previous} =
      segments
      |> Enum.with_index()
      |> Enum.map_reduce(nil, fn {segment, index}, previous ->
        text =
          case segment do
            {:lit, word} ->
              word

            {:hole, %{name: name}} ->
              render_family_production_value(Map.fetch!(bindings, name), depth, indent)
          end

        separator =
          if compact_production_boundary?(previous, segment, index), do: "", else: if(previous, do: " ", else: "")

        {separator <> text, segment}
      end)

    Enum.join(pieces)
  end

  # `Parameters` captures are represented by a list even when they occupy one
  # production hole. Keep that representation internal and restore the
  # comma-separated parameter surface here.
  defp render_family_production_value(values, depth, indent) when is_list(values),
    do: render_family_production_values(values, depth, indent)

  defp render_family_production_value(value, depth, indent), do: render(value, depth, indent)

  defp render_family_production_values([{:param, _, _} | _] = values, depth, indent),
    do: typed_params_to_string(values, depth, indent)

  defp render_family_production_values(values, depth, indent),
    do: Enum.map_join(values, ", ", &render(&1, depth, indent))

  defp compact_production_boundary?({:lit, "-"}, {:lit, word}, _index) when word in ["-", "->"], do: true
  defp compact_production_boundary?({:lit, "-"}, {:hole, _}, _index), do: true
  defp compact_production_boundary?({:hole, _}, {:lit, "-"}, index), do: index > 1
  defp compact_production_boundary?(_previous, _current, _index), do: false

  defp macro_segments_to_string(segments), do: Enum.map_join(segments, " ", &macro_segment_to_string/1)

  defp macro_production_segments_to_string(segments) do
    {pieces, _previous} =
      segments
      |> Enum.with_index()
      |> Enum.map_reduce(nil, fn {segment, index}, previous ->
        separator =
          if compact_production_boundary?(previous, segment, index), do: "", else: if(previous, do: " ", else: "")

        {separator <> macro_segment_to_string(segment), segment}
      end)

    Enum.join(pieces)
  end

  defp macro_segment_to_string({:lit, word}), do: word
  defp macro_segment_to_string({:hole, %{name: name, kind: kind}}), do: "<#{name}: #{kind}>"

  defp macro_segment_to_string({:raw_hole, %{name: name, delimiter: delimiter}}),
    do: "<#{name}: raw until #{delimiter}>"

  defp macro_segment_to_string({:code_hole, %{name: name, delimiter: delimiter}}),
    do: "<#{name}: Code until #{delimiter}>"

  defp macro_segment_to_string({:declarations_hole, %{name: name, delimiter: delimiter}}),
    do: "<#{name}: Declarations until #{delimiter}>"

  defp macro_segment_to_string({:repeat, segment}), do: macro_segment_to_string(segment) <> "..."
  defp macro_segment_to_string({:optional, segments}), do: "(#{macro_segments_to_string(segments)})?"
  defp macro_segment_to_string(other), do: to_string(other)

  defp macro_token_to_string(%Cure.Compiler.Token{value: value}) when is_binary(value), do: value
  defp macro_token_to_string(%Cure.Compiler.Token{value: value}) when is_atom(value), do: Atom.to_string(value)
  defp macro_token_to_string(%Cure.Compiler.Token{value: value}), do: to_string(value)
  defp macro_token_to_string(other), do: to_string(other)

  defp macro_use_site_to_string(tokens) do
    tokens
    |> Enum.map(&macro_token_to_string/1)
    |> Enum.join(" ")
    |> String.replace(" . ", ".")
  end

  defp macro_point_to_string({:category, category}), do: category
  defp macro_point_to_string({:keyword, keyword}), do: "keyword \"#{keyword}\""

  # ── Helpers ──────────────────────────────────────────────────────────────

  # v0.22.0: multi-statement bodies carry a `block_shape` in meta. Round-trip
  # the author's chosen shape -- brace (`{...}`) or end-terminated
  # (`stmt1; stmt2; end`). Indented bodies without an explicit shape fall
  # through to the generic `to_string/3` path.
  defp lambda_body_to_string({:block, meta, exprs} = block, depth, indent) do
    case Keyword.get(meta, :block_shape) do
      :brace ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth, indent))
        "{ #{body} }"

      :end ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth, indent))
        "#{body}; end"

      _ ->
        render(block, depth, indent)
    end
  end

  defp lambda_body_to_string(other, depth, indent) do
    render(other, depth, indent)
  end

  defp operator_to_string(:+), do: "+"
  defp operator_to_string(:-), do: "-"
  defp operator_to_string(:*), do: "*"
  defp operator_to_string(:/), do: "/"
  defp operator_to_string(:rem), do: "%"
  defp operator_to_string(:==), do: "=="
  defp operator_to_string(:!=), do: "!="
  defp operator_to_string(:<), do: "<"
  defp operator_to_string(:>), do: ">"
  defp operator_to_string(:<=), do: "<="
  defp operator_to_string(:>=), do: ">="
  defp operator_to_string(:and), do: "and"
  defp operator_to_string(:or), do: "or"
  defp operator_to_string(:<>), do: "<>"
  defp operator_to_string(:..), do: ".."
  defp operator_to_string(:"..="), do: "..="
  defp operator_to_string(:|>), do: "|>"
  defp operator_to_string(:.), do: "."
  defp operator_to_string(:=), do: "="
  defp operator_to_string(other), do: Atom.to_string(other)

  # -- Precedence-aware parenthesisation -------------------------------------
  #
  # The parser is a Pratt parser driven by the session `FixityTable`. Reprinting
  # must re-insert exactly the parentheses needed to recover the SAME parse — no
  # more (over-parenthesising is ugly and breaks the print-fixpoint), no fewer
  # (under-parenthesising silently changes meaning). Precedences below are read
  # from that same `FixityTable` (via `op_prec`/`prec_of`, keyed by each
  # operator's surface lexeme), so the printer and parser cannot drift and
  # user-declared operators rank correctly — there is no hardcoded copy to keep
  # in agreement.

  # Render `child` as an operand of a parent operator of precedence `parent`
  # (`{level, assoc}` or `:unknown`) on the given `side`, wrapping in parens only
  # when the parse would otherwise change.
  defp operand_str(child, depth, indent, parent, side) do
    s = render(child, depth, indent)
    if needs_parens?(child_prec(child), parent, side), do: "(#{s})", else: s
  end

  # An atomic/primary operand (variable, literal, call, access, …) never needs
  # parens; a control-flow operand (`if`/`match`/lambda/assignment) always does.
  defp needs_parens?(:atom, _parent, _side), do: false
  defp needs_parens?(:lowest, _parent, _side), do: true
  # Unknown parent operator: be conservative and parenthesise any compound child.
  defp needs_parens?(_child, :unknown, _side), do: true

  defp needs_parens?({clevel, _cassoc}, {plevel, passoc}, side) do
    cond do
      clevel < plevel -> true
      clevel > plevel -> false
      # Equal precedence: parens needed unless the child sits on the parent's
      # associative side (`a - b - c` = `(a - b) - c`, so a left child of a
      # left-assoc op needs none; its right child does).
      true -> not associates?(passoc, side)
    end
  end

  defp associates?(:left, :left), do: true
  defp associates?(:right, :right), do: true
  defp associates?(_assoc, _side), do: false

  # Precedence of a child node, as it matters for operand parenthesisation.
  defp child_prec({:binary_op, meta, _}) do
    case op_prec(Keyword.get(meta, :operator)) do
      :unknown -> :lowest
      prec -> prec
    end
  end

  defp child_prec({:unary_op, meta, _}), do: unary_prec(Keyword.get(meta, :operator))
  # Infix operators the parser lowers to their own node types (not :binary_op);
  # rank them through the same fixity table as :binary_op so the scales agree.
  defp child_prec({:range, _meta, _}), do: prec_of("..")
  defp child_prec({:send, _meta, _}), do: prec_of("<-|")
  defp child_prec({:attribute_access, _meta, _}), do: prec_of(".")
  # `|>` lowers to a pipe-tagged :function_call, binding loosely (the `Pipe`
  # group); an ordinary call is a primary (atom) and never needs parens.
  defp child_prec({:function_call, meta, _}) do
    if Keyword.get(meta, :pipe) == true, do: prec_of("|>"), else: :atom
  end

  # Right-extending prefix keywords (`throw`/`yield`/`return`/`spawn`) grab
  # everything to their right, so as a left operand they must be parenthesised.
  defp child_prec({:throw, _meta, _}), do: :lowest
  defp child_prec({:yield, _meta, _}), do: :lowest
  defp child_prec({:early_return, _meta, _}), do: :lowest
  defp child_prec({:async_operation, _meta, _}), do: :lowest
  defp child_prec({:conditional, _meta, _}), do: :lowest
  defp child_prec({:pattern_match, _meta, _}), do: :lowest
  defp child_prec({:pickup, _meta, _}), do: :lowest
  defp child_prec({:lambda, _meta, _}), do: :lowest
  defp child_prec({:assignment, _meta, _}), do: :lowest
  defp child_prec(_other), do: :atom

  # {binding_power, assoc} for an infix operator atom, or `:unknown`, resolved
  # through the session `FixityTable` (`Std.Operators` plus any user-declared
  # groups). The operator atom's surface lexeme keys the table, so `operator_to_string`
  # — which already maps every operator atom to its lexeme — is the lookup key.
  # Only the ORDER of binding powers matters here, and the table preserves the
  # legacy precedence order, so built-in reprints are unchanged; user-declared
  # operators now rank correctly instead of falling through to `:unknown`.
  defp op_prec(op), do: prec_of(operator_to_string(op))

  defp prec_of(lexeme),
    do: Cure.Compiler.Parser.FixityTable.precedence(current_fixity_table(), lexeme)

  # A prefix operator absent from the table (should not happen for the built-in
  # unary operators) binds tighter than any declared group, so its operand is
  # parenthesised whenever it is a compound expression — the conservative choice.
  @unknown_prefix_bp 1_000_000

  # Prefix (unary) precedence for the operand-parenthesisation of a `{:unary_op}`.
  # A prefix operator's group (e.g. `-`) differs from its infix group, so the
  # prefix binding power is read directly. The associativity is fixed `:right`:
  # unary operators nest rightward (`- -x`), independent of the group's declared
  # infix associativity, and only the parent side's assoc is consulted.
  defp unary_prec(op) do
    case Cure.Compiler.Parser.FixityTable.prefix_bp(current_fixity_table(), operator_to_string(op)) do
      bp when is_integer(bp) -> {bp, :right}
      :not_prefix -> {@unknown_prefix_bp, :right}
    end
  end

  defp current_fixity_table do
    Process.get(@fixity_key) || Cure.Compiler.Parser.BuiltinFixity.table()
  end

  defp args_to_string(args, depth, indent) do
    render_span(args, ",", depth, indent)
  end

  # A function call's argument list is the ONE comma-separated construct whose
  # delimiters (`(` … `)`) can span newlines and still reparse -- list (`[…]`),
  # tuple (`%[…]`), and map (`%{…}`) literals cannot, so a comment never attaches
  # to their elements. When an argument carries its own leading/trailing comment,
  # the single-line span has nowhere to put it and would drop it (a lossless-
  # reprint violation, and a spurious `:comment_dropped` migration rejection), so
  # the argument list is rendered one-per-line -- the only layout that both keeps
  # the comment and reparses. With no argument comment, this is byte-for-byte the
  # single-line span, so the common path is untouched.
  defp call_args_to_string(args, depth, indent, labels) do
    multiline? = Enum.any?(args, &has_comment_trivia?/1)
    args = labelled_call_args(args, labels)

    if multiline? do
      render_call_args_multiline(args, depth, indent)
    else
      render_span(args, ",", depth, indent)
    end
  end

  defp labelled_call_args(args, labels) when is_list(labels) and length(args) == length(labels) do
    Enum.zip(args, labels)
    |> Enum.map(fn
      {arg, nil} -> arg
      {arg, label} -> {:named_call_argument, [label: label], [arg]}
    end)
  end

  defp labelled_call_args(args, _labels), do: args

  defp has_comment_trivia?(node) do
    meta = trivia_meta(node)
    comment_item?(Keyword.get(meta, :leading)) or comment_item?(Keyword.get(meta, :trailing))
  end

  defp comment_item?(nil), do: false

  defp comment_item?(items) do
    Enum.any?(items, fn
      {:comment, _, _, _} -> true
      {:doc_comment, _, _, _} -> true
      _ -> false
    end)
  end

  # One argument per line: leading comment lines (at the inner pad), then the
  # value with its separating comma emitted BEFORE any trailing comment (else the
  # `#` swallows the comma and the list reparses one element short), and the
  # closing `)` returns to the caller's indent.
  defp render_call_args_multiline(args, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    close_pad = String.duplicate(indent, depth)
    last = length(args) - 1

    body =
      args
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {arg, i} ->
        meta = trivia_meta(arg)
        comma = if i == last, do: "", else: ","

        value_line =
          append_trailing(inner_pad <> to_string(arg, depth + 1, indent) <> comma, Keyword.get(meta, :trailing))

        (leading_comment_lines(Keyword.get(meta, :leading), inner_pad) ++ [value_line])
        |> Enum.join("\n")
      end)

    "\n" <> body <> "\n" <> close_pad
  end

  defp leading_comment_lines(nil, _pad), do: []

  defp leading_comment_lines(items, pad) do
    items |> Enum.flat_map(&trivia_lines/1) |> Enum.map(&pad_or_empty(&1, pad))
  end

  defp pairs_to_string(pairs, depth, indent) do
    render_span(pairs, ",", depth, indent)
  end

  defp pair_to_string(key, value, depth, indent) do
    case key do
      {:literal, meta, atom_val} when is_list(meta) and is_atom(atom_val) ->
        if Keyword.get(meta, :subtype) == :symbol do
          "#{atom_val}: #{render(value, depth, indent)}"
        else
          "#{render(key, depth, indent)} => #{render(value, depth, indent)}"
        end

      _ ->
        "#{render(key, depth, indent)} => #{render(value, depth, indent)}"
    end
  end

  defp match_arm_to_string({:match_arm, meta, [body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)
    pat_str = render(pattern, depth, indent)
    body_str = arm_body_to_string(meta, body, depth, indent)

    if guard do
      "#{pat_str} when #{render(guard, depth, indent)} -> #{body_str}"
    else
      "#{pat_str} -> #{body_str}"
    end
  end

  defp gen_or_filter_to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    "#{render(pattern, depth, indent)} <- #{render(collection, depth, indent)}"
  end

  defp gen_or_filter_to_string({:filter, _meta, [expr]}, depth, indent) do
    render(expr, depth, indent)
  end

  defp gen_or_filter_to_string({:binary_generator, _meta, _} = node, depth, indent) do
    render(node, depth, indent)
  end

  defp conditional_to_elif({:conditional, _meta, [cond_ast, then_br, else_br]}, depth, indent) do
    cond_str = render(cond_ast, depth, indent)
    then_str = render(then_br, depth, indent)

    case else_br do
      {:literal, meta, nil} when is_list(meta) ->
        if Keyword.get(meta, :subtype) == :null do
          "elif #{cond_str} then #{then_str}"
        else
          "elif #{cond_str} then #{then_str} else #{render(else_br, depth, indent)}"
        end

      {:conditional, _, _} ->
        "elif #{cond_str} then #{then_str} #{conditional_to_elif(else_br, depth, indent)}"

      _ ->
        "elif #{cond_str} then #{then_str} else #{render(else_br, depth, indent)}"
    end
  end

  defp rhs_to_string({:block, _meta, exprs}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)
    "\n#{pad}" <> render_stmt_list(exprs, depth + 1, indent)
  end

  # A body carrying its OWN leading comment cannot be rendered inline after `=`:
  # `= # note` would comment the body out. Break it to the next line — the form
  # the source used — so the comment sits above the body and the reprint is both
  # lossless and idempotent (rendering inline drifted the comment across passes:
  # body-leading → `=`-trailing → statement-leading). No leading comment ⇒ the
  # inline form, byte-for-byte as before.
  defp rhs_to_string(ast, depth, indent) do
    if comment_item?(Keyword.get(trivia_meta(ast), :leading)) do
      pad = String.duplicate(indent, depth + 1)
      "\n#{pad}" <> render(ast, depth + 1, indent)
    else
      render(ast, depth, indent)
    end
  end

  # -- Function Definition ---------------------------------------------------

  defp fn_def_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    visibility = Keyword.get(meta, :visibility, :public)
    params = Keyword.get(meta, :params, [])
    return_type = Keyword.get(meta, :return_type)
    guard = Keyword.get(meta, :guards)
    constraints = Keyword.get(meta, :constraints, [])
    clauses = Keyword.get(meta, :clauses)
    extern = Keyword.get(meta, :extern)
    decorator = Keyword.get(meta, :decorator)

    prefix = if visibility == :private, do: "local fn", else: "fn"
    params_str = typed_params_to_string(params, depth, indent)
    ret_str = if return_type, do: " -> #{render(return_type, depth, indent)}", else: ""

    guard_str =
      if guard, do: " when #{render(guard, depth, indent)}", else: ""

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &render(&1, depth, indent))
        " requires #{cs}"
      else
        ""
      end

    sig = "#{prefix} #{quote_if_reserved(name)}(#{params_str})#{ret_str}#{guard_str}#{constraints_str}"

    result =
      cond do
        clauses != nil and clauses != [] ->
          pad = String.duplicate(indent, depth + 1)

          clauses_str =
            clauses
            |> Enum.map(&fn_clause_to_string(&1, depth + 1, indent))
            |> Enum.join("\n#{pad}")

          "#{sig}\n#{pad}#{clauses_str}"

        body == [] ->
          # Signature only (protocol)
          sig

        true ->
          [body_ast] = body
          "#{sig} = #{rhs_to_string(body_ast, depth, indent)}"
      end

    result = maybe_prepend_decorator(result, extern, decorator, depth, indent)
    result
  end

  defp maybe_prepend_decorator(result, nil, nil, _depth, _indent), do: result

  defp maybe_prepend_decorator(result, extern, _decorator, depth, indent) when extern != nil do
    {m, f, a} =
      case extern do
        {m, f, a} -> {m, f, a}
        _ -> {nil, nil, nil}
      end

    if m do
      # The decorator prints on its own line; the definition on the next.
      # Re-indent the continuation so a decorated definition nested inside a
      # module/interface body keeps its `result` line aligned (the parent's
      # join only pads the first line).
      "@extern(#{extern_ref_to_string(m)}, #{extern_ref_to_string(f)}, #{a})\n#{String.duplicate(indent, depth)}#{result}"
    else
      result
    end
  end

  defp maybe_prepend_decorator(result, _extern, {:decorator, dm, args}, depth, indent) do
    dec_name = Keyword.get(dm, :name)

    args_str =
      case args do
        [{:literal, meta, bval}] when is_list(meta) ->
          if Keyword.get(meta, :subtype) == :boolean do
            # Single boolean arg: emit as @name true / @name false (no parens)
            " #{bval}"
          else
            "(#{render(hd(args), depth, indent)})"
          end

        [] ->
          ""

        _ ->
          "(#{args_to_string(args, depth, indent)})"
      end

    "@#{dec_name}#{args_str}\n#{String.duplicate(indent, depth)}#{result}"
  end

  defp maybe_prepend_decorator(result, _, _, _, _), do: result

  # An `@extern` module/function reference. A dotted or PascalCase module atom
  # (`:"Some.Foreign.Module"`) came from the bare dotted surface form
  # `Some.Foreign.Module` and must round-trip WITHOUT a leading colon
  # (rendering `:Elixir.Cure...` would reparse as attribute-access, not an
  # atom). A plain lowercase atom (`:erlang`) keeps its symbol colon.
  defp extern_ref_to_string(ref) when is_atom(ref) do
    s = Atom.to_string(ref)

    cond do
      String.contains?(s, ".") -> s
      String.match?(s, ~r/^[A-Z]/) -> s
      true -> ":#{s}"
    end
  end

  defp extern_ref_to_string(ref), do: "#{ref}"

  # Backtick-quote a name that would otherwise lex as a keyword/operator so it
  # round-trips as an ordinary identifier (e.g. the `Std.Bool` connectives
  # `` `not` ``/`` `and` ``/`` `or` ``).
  defp quote_if_reserved(name) when is_binary(name) do
    if Cure.Compiler.Lexer.reserved_word?(name) or pure_operator_name?(name),
      do: "`#{name}`",
      else: name
  end

  defp quote_if_reserved(name), do: name

  # A function named by an operator lexeme (`==`, `<`, `!=`, `<=`, `>=`, `>`, …)
  # — legal via a backtick definition — lexes as an operator token when emitted
  # bare, so it must be re-quoted to reparse as a name. Such a name is composed
  # entirely of operator symbols: it contains no identifier characters. Ordinary
  # identifiers and qualified paths (`Std.Bool.not`) contain alphanumerics and
  # are left unquoted (qualified reserved-word tails round-trip on their own).
  defp pure_operator_name?(name),
    do: name != "" and not Regex.match?(~r/[A-Za-z0-9_]/, name)

  defp typed_params_to_string(params, depth, indent) do
    Enum.map_join(params, ", ", fn {:param, meta, name} ->
      kind = Keyword.get(meta, :kind)
      type_ast = Keyword.get(meta, :type)
      default = Keyword.get(meta, :default)

      prefix =
        case kind do
          :variadic -> "*"
          :keyword_variadic -> "**"
          _ -> ""
        end

      type_str = if type_ast, do: ": #{render(type_ast, depth, indent)}", else: ""
      default_str = if default, do: " = #{render(default, depth, indent)}", else: ""
      rendered = "#{prefix}#{name}#{type_str}#{default_str}"

      # An implicit parameter (`{n: Nat}`, `{T: Type}`) is brace-delimited; the
      # braces are what mark it implicit, so dropping them silently turns it into
      # an ordinary positional parameter (an arity/calling-convention change).
      if Keyword.get(meta, :implicit), do: "{#{rendered}}", else: rendered
    end)
  end

  defp fn_clause_to_string(%{params: params, guard: guard, body: [body_ast]}, depth, indent) do
    params_str = Enum.map_join(params, ", ", &render(&1, depth, indent))
    guard_str = if guard, do: " when #{render(guard, depth, indent)}", else: ""
    body_str = render(body_ast, depth, indent)
    "| #{params_str}#{guard_str} -> #{body_str}"
  end

  # -- Container -------------------------------------------------------------

  defp container_to_string(meta, body, depth, indent) do
    type = Keyword.get(meta, :container_type)

    result =
      case type do
        :module -> module_to_string(meta, body, depth, indent)
        :struct -> record_to_string(meta, body, depth, indent)
        :enum -> enum_to_string(meta, body, depth, indent)
        :protocol -> protocol_to_string(meta, body, depth, indent)
        :trait -> impl_to_string(meta, body, depth, indent)
        :proof -> proof_to_string(meta, body, depth, indent)
        :primitive -> primitive_to_string(meta, body, depth, indent)
        :opaque -> opaque_to_string(meta, body, depth, indent)
        _ -> inspect({:container, meta, body})
      end

    # A module-level decorator (`@group(:g)`) attaches to the container itself and
    # prints on its own line directly above it — the canonical above-`mod` form.
    maybe_prepend_decorator(result, nil, Keyword.get(meta, :decorator), depth, indent)
  end

  # -- Primitive type home (`primitive Name`) --------------------------------
  #
  # An irreducible base type (`Int`, `Float`, `Binary`, `Atom`) given a documented
  # module home. The body is empty; a `@builtin(:tag)` decorator (in meta) prints
  # on the preceding line via `maybe_prepend_decorator/5` in `container_to_string`.
  defp primitive_to_string(meta, _body, _depth, _indent), do: "primitive #{Keyword.get(meta, :name)}"

  # -- Opaque type (`opaque type Name(params)`) ------------------------------
  #
  # A constructor-less, non-eliminable carrier type (Agda `postulate`). The body
  # is empty and the optional head params come from `:type_params`. Without this
  # case the container catch-all `inspect/1`-ed the raw tuple, producing output
  # that fails to reparse — which surfaced as `cure migrate` aborting any file
  # containing an `opaque type` (the whole-file verify reprint could not
  # round-trip).
  defp opaque_to_string(meta, _body, _depth, _indent) do
    tp = Keyword.get(meta, :type_params)
    tp_str = if tp && tp != [], do: "(#{Enum.join(tp, ", ")})", else: ""
    "opaque type #{Keyword.get(meta, :name)}#{tp_str}"
  end

  # -- Proof container (`proof Name`) ----------------------------------------
  #
  # A proof container is a module-like block of function definitions.
  defp proof_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    case body do
      [] -> "proof #{name}"
      _ -> "proof #{name}\n#{pad}#{body_str}"
    end
  end

  defp module_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)

    # A bare `mod Name` header (empty body — its definitions are siblings in the
    # enclosing statement list, not nested) must not emit a dangling indented
    # blank line.
    case body do
      [] ->
        "mod #{name}"

      _ ->
        pad = String.duplicate(indent, depth + 1)

        body_str =
          body
          |> Enum.map(&render(&1, depth + 1, indent))
          |> Enum.join("\n#{pad}")

        "mod #{name}\n#{pad}#{body_str}"
    end
  end

  defp record_to_string(meta, fields, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    fields_str =
      fields
      |> Enum.map(fn {:param, field_meta, field_name} ->
        type_ast = Keyword.get(field_meta, :type)
        "#{field_name}: #{render(type_ast, depth + 1, indent)}"
      end)
      |> Enum.join("\n#{pad}")

    "rec #{name}#{tp_str}\n#{pad}#{fields_str}"
  end

  defp enum_to_string(meta, variants, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    variants_str =
      case variants do
        [] ->
          # The empty (uninhabited) type is written `type Empty = |`.
          "|"

        _ ->
          variants
          |> Enum.map(&variant_to_string(&1, depth, indent))
          |> Enum.join(" | ")
      end

    "type #{name}#{tp_str} = #{variants_str}"
  end

  defp variant_to_string({:function_def, meta, []}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])

    if params != [] do
      params_str = Enum.map_join(params, ", ", &render(&1, depth, indent))
      "#{name}(#{params_str})"
    else
      # A nullary constructor `Foo()` keeps its parens: bare `Foo` reparses to a
      # `{:variable, …}` type reference, not a constructor.
      "#{name}()"
    end
  end

  defp variant_to_string({:variable, _meta, name}, _depth, _indent), do: name
  defp variant_to_string(other, depth, indent), do: render(other, depth, indent)

  defp protocol_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "proto #{name}#{tp_str}\n#{pad}#{body_str}"
  end

  defp impl_to_string(meta, body, depth, indent) do
    protocol = Keyword.get(meta, :protocol)
    for_type = Keyword.get(meta, :for)
    constraints = Keyword.get(meta, :constraints, [])
    pad = String.duplicate(indent, depth + 1)

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &render(&1, depth, indent))
        " requires #{cs}"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&render(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "impl #{protocol} for #{for_type}#{constraints_str}\n#{pad}#{body_str}"
  end

  # -- Type Annotation -------------------------------------------------------

  defp type_annotation_to_string(meta, children, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)
    params = Keyword.get(meta, :params)

    tp_str =
      cond do
        params && params != [] ->
          "(#{typed_params_to_string(params, depth, indent)})"

        type_params && type_params != [] ->
          "(#{Enum.join(type_params, ", ")})"

        true ->
          ""
      end

    # A `:type_annotation` is produced by BOTH `type X = BareName` / `type X =
    # (Nat) -> Nat` (a plain synonym) and `typealias X = RHS`. The two keywords
    # are interchangeable EXCEPT when the RHS is an applied type `Foo(args)`:
    # under `type`, `Foo(args)` reparses as a nominal single-constructor
    # `:container` (an ADT), flipping the node kind, whereas `typealias` keeps it a
    # transparent synonym. Such a `{:function_call, …}` RHS therefore MUST reprint
    # with `typealias`; every other shape keeps the `type` spelling that all
    # non-alias code round-trips through.
    keyword =
      if Keyword.get(meta, :typealias) == true or applied_type_rhs?(children),
        do: "typealias",
        else: "type"

    case children do
      [type_expr] ->
        "#{keyword} #{name}#{tp_str} = #{render(type_expr, depth, indent)}"

      _ ->
        "#{keyword} #{name}#{tp_str} = #{args_to_string(children, depth, indent)}"
    end
  end

  defp applied_type_rhs?([{:function_call, _, _}]), do: true
  defp applied_type_rhs?(_), do: false

  # -- Literal helpers -------------------------------------------------------

  defp escape_string(s) when is_binary(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\t", "\\t")
  end

  defp float_to_string(f) when is_float(f) do
    # Use shortest representation that round-trips correctly
    short = :erlang.float_to_binary(f, [:short])

    # Ensure it contains a dot so it parses as a float
    if String.contains?(short, ".") or String.contains?(short, "e") do
      short
    else
      short <> ".0"
    end
  end

  defp regex_to_string({body, flags}), do: "/#{body}/#{flags}"
  defp regex_to_string(other), do: inspect(other)

  defp char_to_string(c) when is_integer(c) do
    case c do
      ?\n -> "'\\n'"
      ?\t -> "'\\t'"
      ?\\ -> "'\\\\'"
      ?' -> "'\\''"
      0 -> "'\\0'"
      _ -> "'#{<<c::utf8>>}'"
    end
  end

  defp bytes_to_string(_meta, []), do: "<<>>"

  defp bytes_to_string(_meta, [{:bin_segment, _, _} | _] = segments) do
    # v0.20.0: bytes literal carries a list of `{:bin_segment, ...}` children.
    inner = Enum.map_join(segments, ", ", &render(&1, 0, @default_indent))
    "<<#{inner}>>"
  end

  defp bytes_to_string(_meta, elements) when is_list(elements) do
    inner = Enum.map_join(elements, ", ", &render(&1, 0, @default_indent))
    "<<#{inner}>>"
  end

  defp bytes_to_string(_meta, _value), do: "<<>>"

  # Build the specifier chain for a bin_segment. Returns an empty
  # string if no specifiers are present; otherwise a hyphen-joined
  # list such as `utf8`, `binary-size(n)`, or `signed-big-32`.
  defp bin_segment_specifier_string(meta, depth, indent) do
    parts = []
    parts = maybe_append(parts, Keyword.get(meta, :type))
    parts = maybe_append(parts, Keyword.get(meta, :signedness))
    parts = maybe_append(parts, Keyword.get(meta, :endianness))

    parts =
      case Keyword.get(meta, :size) do
        nil -> parts
        {:literal, _, n} when is_integer(n) -> parts ++ [Integer.to_string(n)]
        ast -> parts ++ ["size(" <> render(ast, depth, indent) <> ")"]
      end

    parts =
      case Keyword.get(meta, :unit) do
        nil -> parts
        n when is_integer(n) -> parts ++ ["unit(" <> Integer.to_string(n) <> ")"]
        {:literal, _, n} when is_integer(n) -> parts ++ ["unit(" <> Integer.to_string(n) <> ")"]
        _ -> parts
      end

    Enum.join(parts, "-")
  end

  defp maybe_append(parts, nil), do: parts
  defp maybe_append(parts, atom) when is_atom(atom), do: parts ++ [Atom.to_string(atom)]
  defp maybe_append(parts, _), do: parts

  # ── Match Block Rendering (MATCH §9) ────────────────────────────────────
  #
  # The strategy is the one prescribed by the spec:
  #
  #   1. Render every clause's head text (`pattern` or `pattern when guard`)
  #      and every clause's right-hand side text using the inline
  #      printer.
  #   2. If any branch is multi-line (its rendered RHS contains a
  #      newline) or any aligned line would exceed `max_line_width`,
  #      switch the entire block to the wrapped form.
  #   3. Otherwise, align all `->` arrows by padding heads to the
  #      width of the widest head, unless that width exceeds
  #      `alignment_limit`, in which case fall back to the unaligned
  #      form.

  defp render_match_block(scrutinee, arms, depth, indent) do
    render_scrutinee_block("match ", scrutinee, "", arms, depth, indent)
  end

  # Shared renderer for `match`/`with` scrutinee blocks: a keyword, the
  # scrutinee, an optional trailing suffix (e.g. ` proof p`), and aligned or
  # wrapped match arms.
  defp render_scrutinee_block(keyword, scrutinee, suffix, arms, depth, indent) do
    pad_kw = String.duplicate(indent, depth)
    pad = pad_kw <> indent
    scrut_str = render(scrutinee, depth, indent)

    heads = Enum.map(arms, &match_arm_head(&1, depth + 1, indent))
    rhs_inline = Enum.map(arms, &match_arm_rhs_inline(&1, depth + 1, indent))
    multiline_rhs? = Enum.any?(rhs_inline, &multiline?/1)

    max_head = max_grapheme_width(heads)
    align? = max_head <= @alignment_limit

    aligned_lines =
      if align? do
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} ->
          pad_str = String.duplicate(" ", max_head - grapheme_width(h))
          pad <> h <> pad_str <> " -> " <> r
        end)
      else
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} -> pad <> h <> " -> " <> r end)
      end

    too_long? = Enum.any?(aligned_lines, fn line -> grapheme_width(line) > @max_line_width end)

    clauses_str =
      cond do
        multiline_rhs? or too_long? ->
          arms
          |> Enum.zip(heads)
          |> Enum.map(fn {arm, head} -> render_match_arm_wrapped(arm, head, depth + 1, indent) end)
          |> Enum.join("\n" <> pad)

        true ->
          aligned_lines
          |> Enum.map(&String.trim_leading(&1, pad_kw <> indent))
          |> Enum.join("\n" <> pad)
      end

    keyword <> scrut_str <> suffix <> "\n" <> pad <> clauses_str
  end

  defp match_arm_head({:match_arm, meta, [_body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)
    pat_str = render(pattern, depth, indent)

    if guard do
      pat_str <> " when " <> render(guard, depth, indent)
    else
      pat_str
    end
  end

  # A `with`-abstraction rematch arm (`Parent | WithPat -> …`, spec §4) carries
  # its patterns in meta: the enclosing `parent_patterns` and the `pattern`
  # matched against the with-scrutinee, joined by `|` in surface syntax.
  defp match_arm_head({:with_rematch_arm, meta, [_body]}, depth, indent) do
    rematch_patterns(meta)
    |> Enum.map_join(" | ", &render(&1, depth, indent))
  end

  defp match_arm_rhs_inline({:match_arm, meta, [body]}, depth, indent) do
    arm_body_to_string(meta, body, depth, indent)
  end

  defp match_arm_rhs_inline({:with_rematch_arm, meta, [body]}, depth, indent) do
    arm_body_to_string(meta, body, depth, indent)
  end

  defp render_match_arm_wrapped({:match_arm, meta, [body]}, head, depth, indent) do
    if Keyword.get(meta, :impossible) do
      head <> " -> impossible"
    else
      inner_pad = String.duplicate(indent, depth + 1)
      body_str = wrapped_body_to_string(body, depth, indent)
      head <> " ->\n" <> inner_pad <> body_str
    end
  end

  defp render_match_arm_wrapped({:with_rematch_arm, _meta, [body]}, head, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    body_str = wrapped_body_to_string(body, depth, indent)
    head <> " ->\n" <> inner_pad <> body_str
  end

  defp rematch_patterns(meta) do
    Keyword.get(meta, :parent_patterns, []) ++ [Keyword.get(meta, :pattern)]
  end

  # A space after a prefix operator unless it is a purely symbolic
  # (non-alphabetic) spelling like `-` that can safely abut its operand;
  # word-spelled operators such as `bnot` must not fuse into the operand.
  defp unary_sep(op) do
    case Atom.to_string(op) do
      <<c, _::binary>> when c in ?a..?z or c in ?A..?Z -> " "
      _ -> ""
    end
  end

  # An arm whose body is the soft-keyword `impossible` (an absurd/unreachable
  # case, spec §4) carries `meta[:impossible]` with a nil body; render the
  # keyword back.
  defp arm_body_to_string(meta, body, depth, indent) do
    if Keyword.get(meta, :impossible) do
      "impossible"
    else
      render(body, depth, indent)
    end
  end

  # ── Pickup Block Rendering (PICKUP §8) ───────────────────────────────────

  defp render_pickup_block(clauses, depth, indent) do
    pad_kw = String.duplicate(indent, depth)
    pad = pad_kw <> indent

    heads = Enum.map(clauses, &pickup_clause_head(&1, depth + 1, indent))
    rhs_inline = Enum.map(clauses, &pickup_clause_rhs_inline(&1, depth + 1, indent))
    multiline_rhs? = Enum.any?(rhs_inline, &multiline?/1)

    max_head = max_grapheme_width(heads)
    align? = max_head <= @alignment_limit

    aligned_lines =
      if align? do
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} ->
          pad_str = String.duplicate(" ", max_head - grapheme_width(h))
          pad <> h <> pad_str <> " -> " <> r
        end)
      else
        Enum.zip(heads, rhs_inline)
        |> Enum.map(fn {h, r} -> pad <> h <> " -> " <> r end)
      end

    too_long? = Enum.any?(aligned_lines, fn line -> grapheme_width(line) > @max_line_width end)

    clauses_str =
      cond do
        multiline_rhs? or too_long? ->
          clauses
          |> Enum.zip(heads)
          |> Enum.map(fn {clause, head} ->
            render_pickup_clause_wrapped(clause, head, depth + 1, indent)
          end)
          |> Enum.join("\n" <> pad)

        true ->
          aligned_lines
          |> Enum.map(&String.trim_leading(&1, pad_kw <> indent))
          |> Enum.join("\n" <> pad)
      end

    "pickup\n" <> pad <> clauses_str
  end

  defp pickup_clause_head({:pickup_else, _meta, [_body]}, _depth, _indent), do: "else"

  defp pickup_clause_head({:pickup_clause, _meta, [guard, _body]}, depth, indent) do
    render(guard, depth, indent)
  end

  defp pickup_clause_rhs_inline({:pickup_else, _meta, [body]}, depth, indent) do
    render(body, depth, indent)
  end

  defp pickup_clause_rhs_inline({:pickup_clause, _meta, [_guard, body]}, depth, indent) do
    render(body, depth, indent)
  end

  defp render_pickup_clause_wrapped({:pickup_else, _meta, [body]}, _head, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    body_str = wrapped_body_to_string(body, depth, indent)
    "else ->\n" <> inner_pad <> body_str
  end

  defp render_pickup_clause_wrapped({:pickup_clause, _meta, [_guard, body]}, head, depth, indent) do
    inner_pad = String.duplicate(indent, depth + 1)
    body_str = wrapped_body_to_string(body, depth, indent)
    head <> " ->\n" <> inner_pad <> body_str
  end

  # PICKUP §8.3: a trailing `true ->` clause is normalised to `else ->`.
  # Non-terminal `true ->` clauses are left alone (the type checker
  # will raise W-PICKUP-UNREACHABLE for the clauses that follow).
  defp normalize_pickup_terminator([]), do: []

  defp normalize_pickup_terminator(clauses) do
    {init, [last]} = Enum.split(clauses, length(clauses) - 1)

    normalised_last =
      case last do
        {:pickup_clause, meta, [{:literal, _, true}, body]} ->
          {:pickup_else, meta, [body]}

        _ ->
          last
      end

    init ++ [normalised_last]
  end

  # When the right-hand side is a multi-line block, we render it as a
  # block expression with the appropriate indentation. Otherwise we
  # render it inline (using the standard printer), which is fine for
  # any expression that fits on a single line.
  defp wrapped_body_to_string({:block, meta, exprs} = block, depth, indent) do
    case Keyword.get(meta, :block_shape) do
      :brace ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth + 1, indent))
        "{ " <> body <> " }"

      :end ->
        body = Enum.map_join(exprs, "; ", &render(&1, depth + 1, indent))
        body <> "; end"

      _ ->
        # Render each statement on its own line, indented one step
        # deeper than the clause head.
        inner_pad = String.duplicate(indent, depth + 1)

        exprs
        |> Enum.map(&render(&1, depth + 1, indent))
        |> Enum.join("\n" <> inner_pad)
        |> case do
          "" -> render(block, depth + 1, indent)
          rendered -> rendered
        end
    end
  end

  defp wrapped_body_to_string(other, depth, indent) do
    render(other, depth + 1, indent)
  end

  defp multiline?(str) when is_binary(str), do: String.contains?(str, "\n")

  defp grapheme_width(str) when is_binary(str), do: String.length(str)

  defp max_grapheme_width([]), do: 0

  defp max_grapheme_width(list) do
    list
    |> Enum.map(&grapheme_width/1)
    |> Enum.max()
  end

  defp proof_justification_to_string({:proof_justification, _meta, statements}, depth, indent) do
    command_pad = String.duplicate(indent, depth + 2)
    rendered = Enum.map_join(statements, "\n#{command_pad}", &render(&1, depth + 2, indent))
    "because\n#{command_pad}#{rendered}"
  end

  defp proof_justification_to_string(justification, depth, indent),
    do: "because #{render(justification, depth + 1, indent)}"
end
