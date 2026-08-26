defmodule Antigen.Shrink do
  @moduledoc """
  Value-level greedy post-shrink. Minimizes a reified `Challenge` artifact under a
  caller-supplied same-violation-shape predicate, via untyped structural rewrites.
  Purely deterministic (fixed enumeration, no RNG/clock); bounded by a step budget.
  """
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.Term

  @minimal_atoms [{:ctor, :Z, []}, {:ctor, :vnil, []}, {:ctor, :T, []}, {:type, 0}]

  @spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer()) :: Challenge.t()
  def minimize(%Challenge{} = ch, pred, budget) do
    {out, _b} = sweep(ch, pred, budget)
    out
  end

  # greedy: first accepted candidate → restart sweep; else fixpoint. Budget = pred calls.
  defp sweep(ch, pred, budget) do
    case first_accepted(candidates(ch), pred, budget) do
      {:accepted, ch2, budget2} -> sweep(reseed(ch2), pred, budget2)
      {:none, budget2} -> {ch, budget2}
    end
  end

  defp first_accepted(_cands, _pred, 0), do: {:none, 0}
  defp first_accepted([], _pred, b), do: {:none, b}

  defp first_accepted([k | rest], pred, b) do
    if well_formed?(k) do
      if safe_pred(pred, k), do: {:accepted, k, b - 1}, else: first_accepted(rest, pred, b - 1)
    else
      # shape-invalid: no pred call, no budget spent
      first_accepted(rest, pred, b)
    end
  end

  defp safe_pred(pred, k) do
    pred.(k)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  @doc false
  def reseed(%Challenge{} = ch), do: %{ch | seed: :erlang.phash2({ch.kind, ch.payload})}

  # ── candidate enumeration (pinned order: ctx → type → term) ──────────────────
  @doc false
  def candidates(%Challenge{kind: k, payload: p} = ch) when k in [:typed_term, :mutant_term] do
    # EXACT existing behavior for the de-Bruijn-ctx kinds (ctx-drop + type/term rewrites)
    ctx_candidates(ch) ++ field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
  end

  # no Term pieces (spec §3/§5.3)
  def candidates(%Challenge{kind: :elab_program}), do: []

  def candidates(%Challenge{} = ch), do: piece_candidates(ch)

  # Per-piece term rewrites via the corpus bridge, for every non-de-Bruijn kind.
  defp piece_candidates(%Challenge{kind: k, assay: a, label: l, seed: s, note: n} = ch) do
    {scaffold, pieces} = Challenge.to_pieces(ch)

    pieces
    |> Enum.with_index()
    |> Enum.flat_map(fn {{pid, term}, i} ->
      Enum.map(term_candidates(term), fn term2 ->
        new_pieces = List.replace_at(pieces, i, {pid, term2})
        Challenge.from_pieces(k, a, l, s, n, scaffold, new_pieces)
      end)
    end)
  end

  # rule 3: drop each unreferenced absolute ctx position d (index 0 = innermost/list head)
  #
  # NOTE the explicit `//1` step: `0..(n - 1)` WITHOUT a step is an Elixir
  # footgun — when n=0 this is `0..-1`, whose implicit step is -1, so it
  # enumerates `[0, -1]` (two phantom elements), not `[]`. For an empty ctx
  # (the default) those phantom drops produce a no-op candidate that
  # `first_accepted` would accept every sweep, burning the whole budget on
  # nothing. `//1` makes n=0 correctly yield an empty range.
  defp ctx_candidates(%Challenge{payload: p} = ch) do
    n = length(p.ctx)

    0..(n - 1)//1
    |> Enum.map(fn d -> drop_candidate(ch, d) end)
    |> Enum.reject(&is_nil/1)
  end

  defp drop_candidate(%Challenge{payload: p} = ch, d) do
    ctx = p.ctx

    referenced? =
      occurs?(p.term, d) or occurs?(p.type, d) or
        ctx
        |> Enum.with_index()
        |> Enum.any?(fn {e, pos} -> pos < d and occurs?(e, d - pos - 1) end)

    if referenced? do
      nil
    else
      new_ctx =
        ctx
        |> Enum.with_index()
        |> Enum.reject(fn {_e, pos} -> pos == d end)
        |> Enum.map(fn
          # local k>=d-pos shift down
          {e, pos} when pos < d -> Term.shift(e, -1, d - pos)
          # pos>d: content unchanged
          {e, _pos} -> e
        end)

      %{ch | payload: %{p | ctx: new_ctx, term: Term.shift(p.term, -1, d + 1), type: Term.shift(p.type, -1, d + 1)}}
    end
  end

  defp field_cands(ch, field, t) do
    Enum.map(term_candidates(t), fn t2 ->
      %{ch | payload: Map.put(ch.payload, field, t2)}
    end)
  end

  # all single-edit variants of a term, pre-order (edits AT this node before children)
  defp term_candidates(t) do
    here = rule1(t) ++ rule2(t) ++ rule4(t)

    deeper =
      Enum.flat_map(child_slots(t), fn {rebuild, child} ->
        Enum.map(term_candidates(child), rebuild)
      end)

    here ++ deeper
  end

  # rule 1: subterm → minimal atom, only for compound (>1 node) positions
  defp rule1(t) do
    if node_count(t) > 1, do: @minimal_atoms, else: []
  end

  # rule 2: S^k Z → S^(k-1) Z
  defp rule2({:ctor, :S, [n]}), do: [n]
  defp rule2(_), do: []

  # rule 4: structural unwrap (Task 1: non-ctx rules incl. lam/case de Bruijn)
  defp rule4({:app, f, a}), do: [f, a]
  defp rule4({:ctor, _n, args}), do: args

  defp rule4({:case, scrut, _m, branches}) do
    # scrut + arity-0 branch bodies only
    [scrut | for({_c, 0, body} <- branches, do: body)]
  end

  defp rule4({:lam, _g, _dom, body}) do
    if occurs?(body, 0), do: [], else: [Term.shift(body, -1, 0)]
  end

  defp rule4(_), do: []

  # child slots: {rebuild_fn, child} for every immediate sub-term (all Core formers)
  defp child_slots({:app, f, a}), do: [{&{:app, &1, a}, f}, {&{:app, f, &1}, a}]
  defp child_slots({:lam, g, d, b}), do: [{&{:lam, g, &1, b}, d}, {&{:lam, g, d, &1}, b}]
  defp child_slots({:pi, g, d, c}), do: [{&{:pi, g, &1, c}, d}, {&{:pi, g, d, &1}, c}]
  defp child_slots({:ctor, n, args}), do: slot_list(args, &{:ctor, n, &1})

  defp child_slots({:data, n, ps, is}) do
    slot_list(ps, &{:data, n, &1, is}) ++ slot_list(is, &{:data, n, ps, &1})
  end

  defp child_slots({:case, s, m, brs}) do
    [{&{:case, &1, m, brs}, s}, {&{:case, s, &1, brs}, m}] ++
      (Enum.with_index(brs)
       |> Enum.map(fn {{c, ar, body}, i} ->
         {fn nb -> {:case, s, m, List.replace_at(brs, i, {c, ar, nb})} end, body}
       end))
  end

  # (The former :prim child-slot clause retired with the {:prim} node, K2:
  # builtin-op spines are ordinary :app chains, covered by the :app clause.
  # The former :rewrite clause retired with the primitive identity forms,
  # Phase C.)
  defp child_slots(_leaf), do: []

  defp slot_list(elems, rebuild_list) do
    elems
    |> Enum.with_index()
    |> Enum.map(fn {e, i} -> {fn ne -> rebuild_list.(List.replace_at(elems, i, ne)) end, e} end)
  end

  # ── measures / helpers ──────────────────────────────────────────────────────
  @spec size(Challenge.t()) :: non_neg_integer()
  def size(%Challenge{payload: p}),
    do: node_count(p.term) + length(p.ctx) + numeral_magnitude(p.term)

  defp node_count(t) when is_tuple(t),
    do: 1 + (t |> Tuple.to_list() |> tl() |> Enum.map(&node_count/1) |> Enum.sum())

  defp node_count(l) when is_list(l), do: l |> Enum.map(&node_count/1) |> Enum.sum()
  defp node_count(_), do: 0

  defp numeral_magnitude({:ctor, :S, [n]}), do: 1 + numeral_magnitude(n)

  defp numeral_magnitude(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&numeral_magnitude/1) |> Enum.sum()

  defp numeral_magnitude(l) when is_list(l), do: l |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(_), do: 0

  # free-occurrence of de-Bruijn index k (crosses binders, incrementing) — mirrors Runner.occurs?/2
  def occurs?({:var, k}, k), do: true
  def occurs?({:var, _}, _k), do: false
  def occurs?({:lam, _g, d, b}, k), do: occurs?(d, k) or occurs?(b, k + 1)
  def occurs?({:pi, _g, d, c}, k), do: occurs?(d, k) or occurs?(c, k + 1)

  def occurs?({:case, s, m, brs}, k) do
    occurs?(s, k) or occurs?(m, k) or
      Enum.any?(brs, fn {_c, ar, body} -> occurs?(body, k + ar) end)
  end

  def occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  def occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  def occurs?(_leaf, _k), do: false

  # shape-only well-formedness (reimplements Runner.well_formed?/1 to avoid a cycle)
  @doc false
  def well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end

  # de-Bruijn closedness of the WHOLE artifact (term/type against ctx length,
  # each ctx entry against the entries outward of it). Test/guard helper.
  def closed?(%Challenge{payload: p}) do
    n = length(p.ctx)

    max_index_below(p.term, 0) < n and max_index_below(p.type, 0) < n and
      p.ctx
      |> Enum.with_index()
      |> Enum.all?(fn {e, pos} -> max_index_below(e, 0) < n - pos - 1 end)
  end

  # highest free index (relative to `depth` binders already entered), or -1 if closed-at-depth
  defp max_index_below({:var, k}, depth) when k >= depth, do: k - depth
  defp max_index_below({:var, _}, _depth), do: -1
  defp max_index_below({:lam, _g, d, b}, depth), do: max(max_index_below(d, depth), max_index_below(b, depth + 1))
  defp max_index_below({:pi, _g, d, c}, depth), do: max(max_index_below(d, depth), max_index_below(c, depth + 1))

  defp max_index_below({:case, s, m, brs}, depth) do
    [
      max_index_below(s, depth),
      max_index_below(m, depth)
      | Enum.map(brs, fn {_c, ar, body} -> max_index_below(body, depth + ar) end)
    ]
    |> Enum.max()
  end

  defp max_index_below(t, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&max_index_below(&1, depth)) |> max_or(-1)

  defp max_index_below(l, depth) when is_list(l),
    do: l |> Enum.map(&max_index_below(&1, depth)) |> max_or(-1)

  defp max_index_below(_leaf, _depth), do: -1
  defp max_or([], default), do: default
  defp max_or(xs, _default), do: Enum.max(xs)

  # test-only: expose the full candidate list for the §7.3 closure sweep
  def candidates_for_test(ch), do: candidates(ch)
end
