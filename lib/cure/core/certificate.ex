defmodule Cure.Core.Certificate do
  @moduledoc """
  Trusted extraction of direct size-change call summaries from checked Core.

  This module is Cure's analogue of Agda's local call collection phase. It
  traverses one definition at a time and records only facts justified directly
  by that body: canonical callees, arities, and argument-change matrices. It
  deliberately does **not** discover SCCs, compute transitive closure, or decide
  termination. Those global operations live outside the TCB in
  `Cure.Elab.TotalityGraph` and `Cure.Elab.TotalityCertificate`; the kernel only
  verifies their finite certificates.
  """

  alias Cure.Core.{Env, SizeChange, Term}

  @direct_summary_version 5
  @diagnostic_provenance_keys [:source_span, :macro_expansion]

  @doc "The semantic format/checker version of trusted direct-call summaries."
  @spec summary_version() :: pos_integer()
  def summary_version, do: @direct_summary_version

  @doc "Hash the checked Core body used as a direct-summary cache identity."
  @spec body_hash(Cure.Core.Term.t()) :: binary()
  def body_hash(body), do: semantic_hash(body)

  @doc """
  Validate a cached local summary without traversing the Core body again.

  This is the warm counterpart to Agda's per-definition call cache: body and
  checker identities must match, every callee remains canonical with the same
  arity, matrix dimensions remain exact, and the summary's own digest must
  authenticate the complete semantic payload.
  """
  @spec cached_summary_valid?(map() | nil, atom(), Cure.Core.Term.t(), Env.t()) :: boolean()
  def cached_summary_valid?(nil, _name, _body, _env), do: false

  def cached_summary_valid?(summary, name, body, %Env{} = env) when is_map(summary) do
    caller = Env.resolve_key(env, env.defs, name)
    {caller_arity, _inner} = peel_lams(body, 0)

    summary.version == @direct_summary_version and
      summary.caller == caller and
      summary.body_hash == body_hash(body) and
      summary.caller_arity == caller_arity and
      summary.summary_hash == summary_hash(summary) and
      Enum.all?(summary.calls, &valid_cached_call?(&1, caller, caller_arity, env))
  rescue
    KeyError -> false
  end

  def cached_summary_valid?(_summary, _name, _body, _env), do: false

  @doc """
  Extract the complete canonical direct-call summary of one checked Core body.

  This is Cure's counterpart to Agda's per-definition `collectCalls`: it is a
  local trusted traversal, not SCC discovery. The result is stable under map
  ordering and is tied to the exact Core body by a semantic hash.
  """
  @spec direct_summary(atom(), Cure.Core.Term.t(), Env.t()) :: map()
  def direct_summary(name, body, %Env{} = env) do
    caller = Env.resolve_key(env, env.defs, name)
    {caller_arity, inner} = peel_lams(body, 0)
    st = initial_state(caller_arity)

    emit = fn callee, args, state, acc ->
      canonical_callee = Env.resolve_key(env, env.defs, callee)
      callee_arity = definition_arity(env, canonical_callee, length(args))
      matrix = build_cross_matrix(callee_arity, caller_arity, args, state)

      call = %{
        callee: canonical_callee,
        callee_arity: callee_arity,
        matrix: matrix
      }

      [call | acc]
    end

    calls =
      walk(emit, inner, st, [])
      |> Enum.reverse()
      |> Enum.with_index(fn call, ordinal ->
        provenance = %{caller: caller, core_path: ordinal}
        semantic = {caller, call.callee, call.callee_arity, call.matrix, provenance}
        Map.merge(call, %{id: semantic_hash(semantic), provenance: provenance})
      end)
      |> Enum.sort_by(fn call -> {call.callee, call.id} end)

    body_hash = body_hash(body)

    summary = %{
      version: @direct_summary_version,
      caller: caller,
      body_hash: body_hash,
      caller_arity: caller_arity,
      calls: calls
    }

    Map.put(summary, :summary_hash, summary_hash(summary))
  end

  @doc "Attach diagnostic-only source data by stable Core call ordinal."
  @spec attach_provenance(map(), %{optional(non_neg_integer()) => map()}) :: map()
  def attach_provenance(summary, provenance_by_path) when is_map(summary) and is_map(provenance_by_path) do
    calls =
      Enum.map(summary.calls, fn call ->
        diagnostic = Map.get(provenance_by_path, call.provenance.core_path, %{})
        %{call | provenance: Map.merge(call.provenance, diagnostic)}
      end)

    %{summary | calls: calls}
  end

  @doc "Remove diagnostic call-site data while preserving semantic call identity."
  @spec semantic_summary(map()) :: map()
  def semantic_summary(summary) when is_map(summary) do
    Map.update(summary, :calls, [], fn calls ->
      Enum.map(calls, fn call ->
        Map.update(call, :provenance, %{}, &Map.drop(&1, @diagnostic_provenance_keys))
      end)
    end)
  end

  defp definition_arity(env, callee, fallback) do
    case Env.get_def(env, callee) do
      %{body: body} when is_tuple(body) and elem(body, 0) not in [:extern, :hole] -> arity_of(body)
      _ -> fallback
    end
  end

  defp valid_cached_call?(call, caller, caller_arity, env) do
    canonical_callee = Env.resolve_key(env, env.defs, call.callee)
    matrix = SizeChange.sparse(call.matrix)

    call.callee == canonical_callee and
      call.callee_arity == definition_arity(env, canonical_callee, call.callee_arity) and
      matrix.rows == call.callee_arity and
      matrix.columns == caller_arity and
      SizeChange.valid?(matrix) and
      call.provenance.caller == caller and
      is_integer(call.provenance.core_path) and call.provenance.core_path >= 0 and
      call.id ==
        semantic_hash({caller, call.callee, call.callee_arity, matrix, semantic_provenance(call.provenance)})
  rescue
    KeyError -> false
    ArgumentError -> false
  end

  defp arity_of(body), do: body |> peel_lams(0) |> elem(0)

  defp semantic_hash(term), do: :crypto.hash(:sha256, :erlang.term_to_binary(term, [:deterministic]))

  defp summary_hash(summary),
    do: summary |> Map.delete(:summary_hash) |> semantic_summary() |> semantic_hash()

  defp semantic_provenance(provenance), do: Map.drop(provenance, @diagnostic_provenance_keys)

  # Per-parameter tracking, generalised from the old single `root`/`smaller`:
  #   roots[j]    — current de Bruijn index of parameter xⱼ
  #   smallers[j] — indices proven structurally < xⱼ
  #   recons[j]   — the constructor form xⱼ was matched against in this branch
  #                 (a Core ctor-of-vars term, or nil), for reconstruct-equal.
  # Param i (0-based, outermost first) starts at de Bruijn index arity-1-i.
  defp initial_state(arity) do
    roots = Enum.map(0..(arity - 1)//1, fn i -> arity - 1 - i end)

    %{
      roots: roots,
      equals: Enum.map(roots, &MapSet.new([&1])),
      smallers: List.duplicate(MapSet.new(), arity),
      recons: List.duplicate(nil, arity)
    }
  end

  # Traverse `term`, invoking `emit.(callee, args, st, acc)` at every call
  # `callee(args…)` to a global. `emit` decides which globals are tracked (the
  # self-name for #14, or any group member for the mutual path) and prepends the
  # corresponding change matrix / edge; the traversal itself is identical either
  # way, so both paths descend into EVERY node that can hide a call — a nested
  # call sitting inside an argument (e.g. Ackermann) is still reached.
  defp walk(emit, term, st, acc) do
    case spine(term) do
      {{:global, g}, args} ->
        acc = emit.(g, args, st, acc)
        Enum.reduce(args, acc, fn a, ac -> walk(emit, a, st, ac) end)

      {{:case, scrut, motive, branches}, args} when args != [] ->
        acc = walk(emit, scrut, st, acc)
        acc = walk(emit, motive, st, acc)
        acc = Enum.reduce(args, acc, fn arg, ac -> walk(emit, arg, st, ac) end)

        Enum.reduce(branches, acc, fn {ctor, arity, body}, ac ->
          branch_state = refine_branch(st, scrut, ctor, arity)
          walk_applied_branch(emit, body, args, branch_state, arity, ac)
        end)

      {head, args} when args != [] ->
        acc = walk(emit, head, st, acc)
        Enum.reduce(args, acc, fn a, ac -> walk(emit, a, st, ac) end)

      _ ->
        walk_node(emit, term, st, acc)
    end
  end

  # `{:case,…}` is the only binder that refines the per-parameter tracking:
  # each branch shifts the frame by its arity, and matching a parameter (or a
  # known-smaller variable) exposes the branch's fields as smaller. Matching a
  # parameter *exactly* also records its reconstruction for reconstruct-equal.
  defp walk_node(emit, {:case, scrut, motive, branches}, st, acc) do
    acc = walk(emit, scrut, st, acc)
    acc = walk(emit, motive, st, acc)

    Enum.reduce(branches, acc, fn {ctor, ar, body}, ac ->
      st2 = refine_branch(st, scrut, ctor, ar)
      walk(emit, body, st2, ac)
    end)
  end

  defp walk_node(emit, {:lam, _g, d, b}, st, acc),
    do: walk(emit, b, shift_state(st, 1), walk(emit, d, st, acc))

  # `:let` binds one variable in `body` only.
  #
  # Correctness-by-inspection, not a bug fix: without this clause the catch-all
  # returns `acc` untouched, so a `let`'s subterms contribute no size-change
  # edges. That FAILS CLOSED (fewer edges ⇒ harder to certify), and recursion is
  # anyway found by `gather_globals/2`, which walks any tuple. Verified: deleting
  # this clause changes no `terminating?/3` verdict I could construct. It is here
  # because a traversal must not silently skip a binder's children.
  defp walk_node(emit, {:let, _g, t, v, b}, st, acc),
    do: walk(emit, b, shift_state(st, 1), walk(emit, v, st, walk(emit, t, st, acc)))

  defp walk_node(emit, {:pi, _g, d, c}, st, acc),
    do: walk(emit, c, shift_state(st, 1), walk(emit, d, st, acc))

  defp walk_node(emit, {:data, _n, ps, is}, st, acc) do
    acc = Enum.reduce(ps, acc, fn t, ac -> walk(emit, t, st, ac) end)
    Enum.reduce(is, acc, fn t, ac -> walk(emit, t, st, ac) end)
  end

  defp walk_node(emit, {:ctor, _n, args}, st, acc),
    do: Enum.reduce(args, acc, fn a, ac -> walk(emit, a, st, ac) end)

  # Fallback for any tuple node not matched above: a genuine leaf (`{:var,_}`,
  # `{:int_lit,_}`, an untracked `{:global,_}`), OR an unrecognized/future form. Descend
  # CONSERVATIVELY into every element that is itself a term-tuple or a list of them —
  # the same fail-closed discipline as `Validator.children/1`. Genuine leaves carry only
  # atoms and integers, so they yield no children and cost nothing.
  #
  # It used to return `acc` unchanged, which reads "no call here" for a node whose shape
  # this module has never seen. A self-call one wrapper deep was then invisible to the
  # change-matrix builder, and the moduledoc's claim that "the kernel never certifies a
  # function it cannot prove total" was false for `terminating?/3` called in isolation.
  # `terminating?/3` is public, and `certify_hardening_test.exs` already calls it directly.
  defp walk_node(emit, term, st, acc) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.reduce(acc, fn
      child, ac when is_tuple(child) -> walk(emit, child, st, ac)
      children, ac when is_list(children) -> Enum.reduce(children, ac, &descend_unknown(emit, &1, st, &2))
      _leaf, ac -> ac
    end)
  end

  defp walk_node(_emit, _term, _st, acc), do: acc

  # A dependent eliminator is represented as a case returning lambdas followed
  # by applications to the transported indices/proofs. In each branch, the
  # lambda binder is definitionally equal to its application argument. Preserve
  # that fact while walking the branch so a subsequent constructor match can
  # expose genuine structural subterms of the original caller parameter.
  defp walk_applied_branch(emit, {:lam, _grade, domain, body}, [arg | rest], st, branch_binders, acc) do
    acc = walk(emit, domain, st, acc)
    arg = Term.shift(arg, branch_binders)
    walk_applied_branch(emit, body, rest, enter_alias(st, arg), branch_binders + 1, acc)
  end

  defp walk_applied_branch(emit, body, _args, st, _branch_binders, acc),
    do: walk(emit, body, st, acc)

  defp descend_unknown(emit, child, st, acc) when is_tuple(child), do: walk(emit, child, st, acc)
  defp descend_unknown(_emit, _child, _st, acc), do: acc

  # Enter a case branch matching `scrut` with constructor `ctor`/arity `ar`:
  # shift the frame by `ar`, then for each parameter decide whether `scrut`
  # exposes new smaller fields and (for an exact parameter match) a reconstruction.
  defp refine_branch(st, scrut, ctor, ar) do
    shifted = shift_state(st, ar)
    recon = build_recon(ctor, ar)

    idx = scrut_index(scrut)

    smallers =
      Enum.zip_with([st.equals, st.smallers, shifted.smallers], fn [equals, sm0, sm_sh] ->
        if idx != nil and (MapSet.member?(equals, idx) or MapSet.member?(sm0, idx)),
          do: add_fields(sm_sh, ar),
          else: sm_sh
      end)

    recons =
      Enum.zip_with([st.equals, shifted.recons], fn [equals, rc_sh] ->
        # reconstruct-EQUAL only on an EXACT parameter match (`scrut` IS xⱼ):
        # then xⱼ is definitionally `ctor(fields)`. A merely-smaller scrutinee
        # never yields `:equal` (guardrail: never `:smaller`/over-claim from a
        # reconstruction), so its recon is left untouched.
        if idx != nil and MapSet.member?(equals, idx), do: recon, else: rc_sh
      end)

    %{shifted | smallers: smallers, recons: recons}
  end

  defp scrut_index({:var, i}), do: i
  defp scrut_index(_), do: nil

  # The reconstruction of `ctor(f₀ … f_{ar-1})` in a freshly-entered branch. The
  # kernel binds ctor fields so the LAST field is de Bruijn 0 (see `eval`'s
  # `reverse(args) ++ env`), so field fᵢ is index `ar-1-i` — i.e. the field list
  # is `[var (ar-1), …, var 0]`. This must be byte-identical to the term the
  # elaborator emits for `ctor(f₀ … f_{ar-1})`, or reconstruct-equal soundly
  # fails to fire (→ `:unknown`).
  defp build_recon(ctor, 0), do: {:ctor, ctor, []}

  defp build_recon(ctor, ar),
    do: {:ctor, ctor, Enum.map((ar - 1)..0//-1, &{:var, &1})}

  # -- change matrix ----------------------------------------------------------

  # Build the (non-square) `m×k` matrix for a call to a group member g of arity m
  # from inside a caller f of arity k: M[i][j] = relation of g-call-arg yᵢ (row,
  # 0..m-1) to f-parameter xⱼ (col, 0..k-1). Identical `arg_relation` + `st`
  # tracking as the self-call case — reconstruct-equal fires across the boundary.
  # Missing call-args (under-application) read `nil` ⇒ `:unknown` (conservative).
  defp build_cross_matrix(m, k, args, st) do
    rows(m, fn i ->
      arg = Enum.at(args, i)
      rows(k, fn j -> arg_relation(arg, param_view(st, j)) end)
    end)
    |> SizeChange.from_dense()
  end

  # Map over `0..(n-1)`, yielding `[]` for `n <= 0` (empty dimension).
  defp rows(n, _f) when n <= 0, do: []
  defp rows(n, f), do: Enum.map(0..(n - 1)//1, f)

  defp param_view(st, j),
    do: %{
      root: Enum.at(st.roots, j),
      equal: Enum.at(st.equals, j),
      smaller: Enum.at(st.smallers, j),
      recon: Enum.at(st.recons, j)
    }

  # Relation of a single call-argument to a single parameter.
  #   :smaller — a variable proven structurally < xⱼ, OR an application whose
  #              spine head is such a variable (higher-order subterm rule below)
  #   :equal   — the same de Bruijn var as xⱼ, OR a constructor application
  #              syntactically identical to xⱼ's reconstruction (reconstruct-equal)
  #   :unknown — anything else (never claim ≤ for a possibly-larger term)
  defp arg_relation(nil, _pv), do: :unknown

  defp arg_relation({:var, i}, %{equal: equal, smaller: smaller}) do
    cond do
      MapSet.member?(smaller, i) -> :smaller
      MapSet.member?(equal, i) -> :equal
      true -> :unknown
    end
  end

  defp arg_relation({:ctor, _c, _as} = arg, %{recon: recon}) do
    if recon != nil and arg == recon, do: :equal, else: :unknown
  end

  # Higher-order subterm rule (Agda/Idris `Core/Termination/SizeChange.idr`,
  # spec `2026-07-18-elaborator-gaps-verified-status.md` §2 K-bug 2): an
  # application `g(a…)` whose spine head `g` is a field of xⱼ exposed as
  # `:smaller` is ITSELF a strict subterm of xⱼ. The elements of an inductive
  # type are well-founded trees, and the immediate children of a node
  # `Bind e g` are exactly `{ g y : y }` — so `g y` is a genuine subterm for
  # ANY argument `y`, and recursion on it is well-founded. This certifies the
  # continuation-style `bind`
  #   Bind(e,g) -> Bind(e, fn y -> bind(g(y), f))
  # whose self-call passes `g(y)` (head `g` smaller) — total. It does NOT admit
  # the diverging control
  #   Bind(e,g) -> Bind(e, fn y -> bind(Bind(e,g), f))
  # whose self-call passes the ctor RECONSTRUCTION `Bind(e,g)` (matched by the
  # `{:ctor,…}` clause above as `:equal`, never `:smaller`). We claim `:smaller`
  # ONLY for a proven-smaller head — never `:equal` (an application is never a
  # parameter's reconstruction), and never when the head is xⱼ itself (`root`):
  # `xⱼ` applied to arguments is not `< xⱼ`.
  defp arg_relation({:app, _, _} = arg, %{smaller: smaller}) do
    case spine(arg) do
      {{:var, i}, _args} -> if MapSet.member?(smaller, i), do: :smaller, else: :unknown
      _ -> :unknown
    end
  end

  defp arg_relation(_arg, _pv), do: :unknown

  # -- per-parameter frame maintenance ----------------------------------------

  # Shift every tracked de Bruijn index up by `by` on entering `by` binders.
  defp shift_state(st, by) do
    %{
      roots: Enum.map(st.roots, &(&1 + by)),
      equals: Enum.map(st.equals, &shift(&1, by)),
      smallers: Enum.map(st.smallers, &shift(&1, by)),
      recons:
        Enum.map(st.recons, fn
          nil -> nil
          t -> shift_term(t, by)
        end)
    }
  end

  defp enter_alias(st, argument) do
    relations = rows(length(st.roots), &arg_relation(argument, param_view(st, &1)))
    shifted = shift_state(st, 1)

    equals =
      Enum.zip_with([shifted.equals, relations], fn [aliases, relation] ->
        if relation == :equal, do: MapSet.put(aliases, 0), else: aliases
      end)

    smallers =
      Enum.zip_with([shifted.smallers, relations], fn [subterms, relation] ->
        if relation == :smaller, do: MapSet.put(subterms, 0), else: subterms
      end)

    %{shifted | equals: equals, smallers: smallers}
  end

  # A branch binds `ar` fresh fields at indices 0..ar-1 (outer indices already
  # shifted up by `ar`); those fields are the smaller subterms.
  defp add_fields(smaller, 0), do: smaller

  defp add_fields(smaller, ar),
    do: Enum.reduce(0..(ar - 1)//1, smaller, &MapSet.put(&2, &1))

  defp shift(set, by), do: MapSet.new(set, &(&1 + by))

  # Shift free de Bruijn vars in a reconstruction term. Reconstructions are only
  # ever built as constructor applications of variables (no inner binders), so a
  # blanket var-shift is exact.
  defp shift_term({:var, i}, by), do: {:var, i + by}
  defp shift_term({:ctor, c, args}, by), do: {:ctor, c, Enum.map(args, &shift_term(&1, by))}
  defp shift_term(other, _by), do: other

  # -- spine / lambda peeling -------------------------------------------------

  # Flatten a left-nested application `((h a) b) …` into `{h, [a, b, …]}`.
  defp spine(term), do: spine(term, [])
  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(head, acc), do: {head, acc}

  # Count leading lambdas and return the wrapped body.
  defp peel_lams({:lam, _g, _d, b}, n), do: peel_lams(b, n + 1)
  defp peel_lams(term, n), do: {n, term}
end
