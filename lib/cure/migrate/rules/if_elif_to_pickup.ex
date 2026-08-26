defmodule Cure.Migrate.Rules.IfElifToPickup do
  @moduledoc """
  Migration rule: legacy `if`/`elif`/`else` → the v1.0.0 `pickup` primitive
  (spec §5.5). Ports the AST transform from `Mix.Tasks.Cure.Rewrite`
  (`conditional_to_pickup/3`, `do_chain/4`): a `{:conditional, …}` chain whose
  terminal `else` is populated becomes a `{:pickup, …}`; a chain with no real
  `else` (terminal `{:literal, [subtype: :null], nil}`) cannot be made total and
  is left untouched (PICKUP §5.2) — and, being unchanged even in an ideal world,
  is not warned about.

  ## Why verify-by-reparse, not structural ancestry

  Cure's layout lexer suppresses `:indent`/`:dedent` inside round parens
  (`lexer.ex:1379,1384`, gated only by `(`/`)` at `lexer.ex:179-180`), so a
  multi-line `pickup` block cannot live inside a parenthesised context and would
  fail to re-parse there. That context cannot be detected structurally: round
  parens are consumed at ≥6 distinct parser sites, and `parse_grouped/1`
  (`parser.ex:526-533`) *discards* the grouping node entirely — a grouped
  conditional used as an operand, e.g. `(if c then 1 else 2) + 1`, is
  AST-indistinguishable from a bare top-level one. The information is erased
  before this rule runs.

  So each conditional is rewritten **one at a time**: replace exactly that node
  with its `pickup` form, reprint the *whole* file, and re-lex+re-parse. Commit
  the substitution only if the reprint reparses **to a structurally equivalent
  AST**; otherwise leave that conditional as-is. Reparse *success* alone is not
  enough: `(if c then 1 else 2) + 1` parses as `binary_op(+, conditional, 1)`,
  and printing the pickup in that operand position yields `pickup … else -> 2 + 1`
  — which reparses happily but silently absorbs the `+ 1` into the else clause, a
  different program. Comparing the reparsed structure to the candidate (meta and
  trivia stripped) rejects exactly these meaning-changing rewrites. Either way
  the rule **warns** on every legacy `if/elif` it finds (the parity contract of
  Task 10 is "warn on exactly the inputs that would change in an ideal world",
  independent of the paren guard).

  A reverted conditional is flagged in its own `meta` with `@skip_key` so it is
  not re-found after a *nested* rewrite mutates its subtree (value-equality would
  break there); the flags are stripped from the returned AST.
  """

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate.Rule

  @skip_key :__migrate_if_elif_skip__

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_if_elif_pickup,
      description: "legacy `if`/`elif`/`else` is migrated to the `pickup` primitive",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "legacy `if`/`elif` will be migrated to `pickup`"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, _ctx) do
    {final, lines, committed?} = loop(ast, [], false)
    final = strip_skips(final)

    cond do
      committed? -> {:rewrite, final, Enum.reverse(lines)}
      lines != [] -> {:warn, Enum.reverse(lines)}
      true -> :no_change
    end
  end

  # Rewrite one chain-head conditional per pass, verifying by whole-file reparse.
  # `lines` accumulates (reversed) the source line of every head found, whether
  # or not its substitution was committed.
  defp loop(ast, lines, committed?) do
    case find_head(ast, [], false) do
      :none ->
        {ast, lines, committed?}

      {:ok, path, node} ->
        lines = [line_of(node) | lines]
        candidate = replace_at(ast, path, rewrite_node(node))

        if reparses_equivalently?(candidate) do
          loop(candidate, lines, true)
        else
          # Keep the conditional, flag it so it is not re-found, and continue.
          loop(replace_at(ast, path, flag_skip(node)), lines, committed?)
        end
    end
  end

  # ── Finding the next rewritable chain head (pre-order) ─────────────────────
  #
  # A conditional is a *chain head* unless it sits in the `else` position of an
  # enclosing conditional (that is an `elif` continuation, folded into its head's
  # `pickup` by `conditional_to_pickup/3`). We only ever return a head that is
  # not already skip-flagged and that has a real `else` (is rewritable). We still
  # recurse into skipped / continuation / then / cond subtrees, so conditionals
  # nested inside them get their own turn.

  defp find_head({:conditional, meta, [c, t, e]} = node, path, cont?) do
    if not cont? and not skipped?(meta) and rewritable?(node) do
      {:ok, Enum.reverse(path), node}
    else
      # child 2 (else) continues the chain; children 0/1 start fresh
      find_children([{c, false}, {t, false}, {e, true}], 0, path)
    end
  end

  defp find_head({_k, _m, ch}, path, _cont?) when is_list(ch) do
    find_children(Enum.map(ch, &{&1, false}), 0, path)
  end

  defp find_head({_k, _m, name, inner}, path, _cont?) when is_binary(name) do
    find_head(inner, [0 | path], false)
  end

  defp find_head(l, path, _cont?) when is_list(l) do
    find_children(Enum.map(l, &{&1, false}), 0, path)
  end

  defp find_head(_leaf, _path, _cont?), do: :none

  defp find_children([], _i, _path), do: :none

  defp find_children([{child, cont?} | rest], i, path) do
    case find_head(child, [i | path], cont?) do
      {:ok, _, _} = hit -> hit
      :none -> find_children(rest, i + 1, path)
    end
  end

  # ── Path-addressed replacement (mirrors find_head's child indexing) ────────

  defp replace_at(_node, [], new), do: new

  defp replace_at({k, m, ch}, [i | rest], new) when is_list(ch) do
    {k, m, List.update_at(ch, i, &replace_at(&1, rest, new))}
  end

  defp replace_at({k, m, name, inner}, [0 | rest], new) when is_binary(name) do
    {k, m, name, replace_at(inner, rest, new)}
  end

  defp replace_at(l, [i | rest], new) when is_list(l) do
    List.update_at(l, i, &replace_at(&1, rest, new))
  end

  # ── Conditional → pickup (ported from Mix.Tasks.Cure.Rewrite) ──────────────

  # Convert one chain-head conditional to a pickup, keeping the node's own meta
  # (so its leading/trailing trivia — spec §5.2 — travels to the pickup) and its
  # branch subtrees intact (so branch comments survive, and nested conditionals
  # get processed in later passes).
  defp rewrite_node({:conditional, meta, [c, t, e]}) do
    {:ok, clauses} = conditional_to_pickup(c, t, e)
    {:pickup, meta, clauses}
  end

  defp rewritable?({:conditional, _meta, [c, t, e]}) do
    match?({:ok, _}, conditional_to_pickup(c, t, e))
  end

  defp conditional_to_pickup(cond_expr, then_branch, else_branch) do
    case do_chain(cond_expr, then_branch, else_branch, []) do
      {:no_else, _} -> :no_else
      {:ok, clauses} -> {:ok, clauses}
    end
  end

  defp do_chain(cond_expr, then_branch, {:conditional, _meta, [c2, t2, e2]}, acc) do
    do_chain(c2, t2, e2, [{:pickup_clause, [], [cond_expr, then_branch]} | acc])
  end

  defp do_chain(cond_expr, then_branch, {:literal, meta, nil} = else_branch, acc)
       when is_list(meta) do
    if Keyword.get(meta, :subtype) == :null do
      {:no_else, Enum.reverse(acc)}
    else
      clauses =
        Enum.reverse([
          {:pickup_else, [], [else_branch]},
          {:pickup_clause, [], [cond_expr, then_branch]} | acc
        ])

      {:ok, clauses}
    end
  end

  defp do_chain(cond_expr, then_branch, else_branch, acc) do
    clauses =
      Enum.reverse([
        {:pickup_else, [], [else_branch]},
        {:pickup_clause, [], [cond_expr, then_branch]}
        | acc
      ])

    {:ok, clauses}
  end

  # ── Reparse check + skip flags ─────────────────────────────────────────────

  # Reprint the candidate, reparse it, and require the reparsed AST to be
  # structurally identical to the candidate (meta + trivia erased). Rejects both
  # reprints that fail to parse (paren-context pickup) and reprints that parse to
  # a *different* program (operand-position absorption, see @moduledoc).
  defp reparses_equivalently?(candidate) do
    src = Printer.quoted_to_string(candidate)

    with {:ok, toks} <- Lexer.tokenize(src, file: "migrate_reparse", emit_events: false),
         {:ok, reparsed} <- Parser.parse(toks, file: "migrate_reparse", emit_events: false) do
      structural(candidate) == structural(reparsed)
    else
      _ -> false
    end
  end

  # Erase every node's meta (positions AND attached trivia), keeping only kind,
  # structure, and leaf values — the shape that must be preserved by a rewrite.
  defp structural({k, _m, ch}) when is_list(ch), do: {k, Enum.map(ch, &structural/1)}
  defp structural({k, _m, name, inner}) when is_binary(name), do: {k, name, structural(inner)}
  defp structural({k, _m, v}), do: {k, v}
  defp structural(l) when is_list(l), do: Enum.map(l, &structural/1)
  defp structural(other), do: other

  defp line_of({:conditional, meta, _}),
    do: Rule.source_span(meta, :opener) || Rule.source_line(meta)

  defp skipped?(meta), do: Keyword.get(meta, @skip_key, false)

  defp flag_skip({:conditional, meta, ch}), do: {:conditional, [{@skip_key, true} | meta], ch}

  # Remove every @skip_key flag we injected, so the returned AST is clean.
  defp strip_skips({:conditional, meta, ch}) do
    {:conditional, Keyword.delete(meta, @skip_key), Enum.map(ch, &strip_skips/1)}
  end

  defp strip_skips({k, m, ch}) when is_list(ch), do: {k, m, Enum.map(ch, &strip_skips/1)}
  defp strip_skips({k, m, name, inner}) when is_binary(name), do: {k, m, name, strip_skips(inner)}
  defp strip_skips(l) when is_list(l), do: Enum.map(l, &strip_skips/1)
  defp strip_skips(other), do: other
end
