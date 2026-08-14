defmodule Cure.Core.Certificate do
  @moduledoc """
  Totality decision procedures the kernel re-runs before certifying a global for
  δ-reduction (design spec §7).

  Operates directly on **Core terms** (not the surface AST), keeping the trusted
  kernel self-contained. Coverage is already enforced by the kernel's `case`
  typing (`check_def` re-runs it), so this module supplies the **termination**
  half.

  ## Termination: size-change (Lee–Jones–Ben-Amram)

  The check is *sound but conservative*. A definition certifies when EITHER it
  makes no self-call, OR the **size-change principle** holds for its self-calls
  (single-function self-recursion only; see below). This is a port of Idris
  `Core/Termination/SizeChange.idr`, scoped to a single function, and strictly
  generalises the older "one fixed decreasing position" guard.

  For every self-call `f(y₀ … y_{k-1})` we build a `k×k` **change matrix**
  `M[i][j] ∈ {:smaller | :equal | :unknown}` relating call-argument `yᵢ` to
  parameter `xⱼ`. We track, per parameter and across binders (shifted like de
  Bruijn indices):

    * `root`  — the parameter's current de Bruijn index (`:equal` when an
      argument IS this variable),
    * `smaller` — variables proven structural subterms of the parameter, grown
      when a `case` matches the parameter or an already-smaller variable
      (`:smaller`),
    * `recon` — the constructor form the parameter was matched against in the
      current branch. A call-argument **syntactically identical** to that form is
      `:equal` (**reconstruct-equal**: in the branch where `xⱼ` matched
      `C(f₀…fₘ)`, `xⱼ` is definitionally `C(f₀…fₘ)`). This is Idris's
      `sizeEq s t => Same`, and is what certifies Ackermann's inner call
      `ack(S m, n)`. A larger/non-matching form stays `:unknown`; we never derive
      `:smaller` from a reconstruction.

  The self-call matrices are closed under composition (a semiring: `:unknown`
  absorbs, `:equal` neutral, `:smaller` dominates) to a fixpoint, and the
  definition is certified total iff **every idempotent** matrix `M` in the
  closure (`M∘M == M`) has a strictly-decreasing diagonal (some `M[i][i] ==
  :smaller`) — the LJB non-termination criterion, negated.

  A conservative *rejection* is always sound — the kernel never certifies a
  function it cannot prove total, so δ never unfolds a non-terminating global.
  Every entry is `:smaller`/`:equal` only when justified by the tracking above
  (over-approximation); higher-order recursion, non-variable *strictly*-
  decreasing arguments, and mutual recursion fall outside the criterion and are
  (soundly) rejected.

  ## Mutual recursion (cross-function size-change)

  A cycle that runs *through a sibling* global (`f` calls `g`, `g` calls `f`) is
  invisible to the single-body check — each body is self-call-free. We handle it
  by generalising the size-change machinery from self-calls to intra-group calls
  (a port of Idris `Core/Termination/SizeChange.idr` `addFunctions`):

    1. **Mutual group.** Using the signature `env`, compute the SCC of globals
       mutually reachable with `name` (each reaches the other via `reaches?`). A
       singleton group `{name}` is exactly #14 — we delegate to
       `size_change_total?/2` unchanged, so nothing #14 certifies regresses and
       non-cyclic helpers (a callee that does not reach back) are unaffected.
    2. **Cross-function change edges.** For every call `g(y₀ … y_{m-1})` (g in the
       group, arity m) inside `f`'s body (f arity k), build a **non-square** `m×k`
       matrix `M_{f→g}[i][j] = arg_relation(yᵢ, xⱼ)` — the SAME `arg_relation` and
       per-parameter `roots`/`smallers`/`recons` tracking as #14 (reconstruct-equal
       works across the call boundary). Self-calls are the #14 `f→f` edges.
    3. **Multi-function transitive closure** (the Idris `SCSet`): elements are
       `{f, g, matrix}`; compose `M_{f→g} ∘ M_{g→h} = M_{f→h}` when the shared
       intermediate g's arity matches the inner dimension. Close to a fixpoint,
       dedup by `{f, g, matrix}`.
    4. **Certificate condition.** Certify the whole group total iff EVERY square,
       idempotent **endo-edge** `M_{f→f}` in the closure (`M∘M == M`) has a
       strictly-decreasing diagonal (`M[i][i] == :smaller`). A single group member
       with a bad idempotent loop fails the whole group.

  Over-approximation is preserved verbatim: an entry is `:smaller`/`:equal` only
  via `arg_relation`, never over-claimed across the call boundary, so a
  conservative rejection is always sound. A well-founded mutual pair (e.g.
  `even`/`odd`) whose shared argument decreases through the cycle now certifies;
  a divergent pair is rejected by the size-change criterion itself — its `f→f`
  endo-loop is idempotent with no `:smaller` diagonal.
  """

  alias Cure.Core.Env

  @direct_summary_version 1

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
      semantic = {caller, canonical_callee, callee_arity, matrix}

      call = %{
        id: semantic_hash(semantic),
        callee: canonical_callee,
        callee_arity: callee_arity,
        matrix: matrix,
        provenance: %{caller: caller}
      }

      [call | acc]
    end

    calls =
      walk(emit, inner, st, [])
      |> Enum.reverse()
      |> Enum.sort_by(fn call -> {call.callee, call.id} end)

    body_hash = semantic_hash(body)

    summary = %{
      version: @direct_summary_version,
      caller: caller,
      body_hash: body_hash,
      caller_arity: caller_arity,
      calls: calls
    }

    Map.put(summary, :summary_hash, semantic_hash(summary))
  end

  defp definition_arity(env, callee, fallback) do
    case Env.get_def(env, callee) do
      %{body: body} when is_tuple(body) and elem(body, 0) not in [:extern, :hole] -> arity_of(body)
      _ -> fallback
    end
  end

  defp semantic_hash(term), do: :crypto.hash(:sha256, :erlang.term_to_binary(term, [:deterministic]))

  @doc """
  True when the Core `body` of global `name` is provably terminating under the
  signature `env` (needed to see mutual cycles through sibling globals).
  """
  @spec terminating?(atom(), Cure.Core.Term.t(), Env.t()) :: boolean()
  def terminating?(name, body, env) do
    if pending_callee?(name, body, env) do
      # A callee still carries the elaborator's `{:hole, "__pending__"}` placeholder
      # (its body has not been elaborated yet). Its onward calls are invisible, so
      # the SCC is under-computed and a mutual member would be mis-certified as a
      # non-recursive singleton. Certification must be *deferred*: stay uncertified
      # (opaque to δ, always sound §7) until `TotalityClosure` re-certifies with
      # every body present.
      false
    else
      terminating_ready?(name, body, env)
    end
  end

  @doc """
  The set of names to certify when `name`'s definition certifies total: its whole
  mutual SCC. Callers MUST have already established `terminating?(name, body, env)`
  — for a genuine group that ran `mutual_group_total?/4` over exactly this SCC, so
  every member is proven total *together* (Idris/Agda/Lean certify a mutual block
  as a unit). A non-mutual def yields the singleton `{name}` (unchanged behaviour).
  This computes membership only, never totality.
  """
  @spec total_group(atom(), Cure.Core.Term.t(), Env.t()) :: MapSet.t(atom())
  def total_group(name, body, env), do: mutual_group(name, body, env)

  defp terminating_ready?(name, body, env) do
    group = mutual_group(name, body, env)

    if MapSet.size(group) <= 1 do
      # Single-function group ⇒ exactly #14 (single-function size-change).
      if calls?(name, body), do: size_change_total?(name, body), else: true
    else
      # Genuine mutual group ⇒ cross-function size-change over the whole SCC.
      mutual_group_total?(name, body, group, env)
    end
  end

  # -- size-change termination (Lee–Jones–Ben-Amram) --------------------------
  #
  # Generalises the old "one fixed decreasing position" test to the full
  # size-change principle, scoped to single-function self-recursion. We build,
  # for every self-call in the body, a `k×k` **change matrix** relating each
  # call-argument to each parameter (`:smaller | :equal | :unknown`), close the
  # set under path composition to a fixpoint, and certify total iff every
  # *idempotent* matrix in the closure has a strictly-decreasing (`:smaller`)
  # diagonal entry. This is the LJB non-termination criterion negated.
  #
  # Over-approximation is the invariant: an entry is `:smaller`/`:equal` only
  # when justified by structural subterm tracking (a variable proven smaller, or
  # a term equal to a parameter — see `arg_relation/2`); otherwise `:unknown`.
  # Rejection is always sound. A single fixed decreasing position `p` yields an
  # idempotent loop with `M[p][p] = :smaller`, so everything the old check
  # certified still certifies (strict generalisation).
  defp size_change_total?(name, body) do
    {arity, inner} = peel_lams(body, 0)
    st = initial_state(arity)

    # Self-emit: a call to `name` contributes its own `k×k` change matrix.
    self_emit = fn g, args, s, acc ->
      if g == name, do: [build_matrix(arity, args, s) | acc], else: acc
    end

    matrices = walk(self_emit, inner, st, []) |> Enum.uniq()
    closure = transitive_closure(matrices)

    Enum.all?(closure, fn m -> not idempotent?(m) or smaller_diagonal?(m) end)
  end

  # Per-parameter tracking, generalised from the old single `root`/`smaller`:
  #   roots[j]    — current de Bruijn index of parameter xⱼ
  #   smallers[j] — indices proven structurally < xⱼ
  #   recons[j]   — the constructor form xⱼ was matched against in this branch
  #                 (a Core ctor-of-vars term, or nil), for reconstruct-equal.
  # Param i (0-based, outermost first) starts at de Bruijn index arity-1-i.
  defp initial_state(arity) do
    %{
      roots: Enum.map(0..(arity - 1)//1, fn i -> arity - 1 - i end),
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
      Enum.zip_with([st.roots, st.smallers, shifted.smallers], fn [root, sm0, sm_sh] ->
        if idx != nil and (idx == root or MapSet.member?(sm0, idx)),
          do: add_fields(sm_sh, ar),
          else: sm_sh
      end)

    recons =
      Enum.zip_with([st.roots, shifted.recons], fn [root, rc_sh] ->
        # reconstruct-EQUAL only on an EXACT parameter match (`scrut` IS xⱼ):
        # then xⱼ is definitionally `ctor(fields)`. A merely-smaller scrutinee
        # never yields `:equal` (guardrail: never `:smaller`/over-claim from a
        # reconstruction), so its recon is left untouched.
        if idx != nil and idx == root, do: recon, else: rc_sh
      end)

    %{roots: shifted.roots, smallers: smallers, recons: recons}
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

  # Build the `k×k` matrix for a self-call: M[i][j] = relation of call-arg yᵢ to
  # parameter xⱼ. Rows are call-arguments, columns are parameters.
  defp build_matrix(k, args, st), do: build_cross_matrix(k, k, args, st)

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
  end

  # Map over `0..(n-1)`, yielding `[]` for `n <= 0` (empty dimension).
  defp rows(n, _f) when n <= 0, do: []
  defp rows(n, f), do: Enum.map(0..(n - 1)//1, f)

  defp param_view(st, j),
    do: %{root: Enum.at(st.roots, j), smaller: Enum.at(st.smallers, j), recon: Enum.at(st.recons, j)}

  # Relation of a single call-argument to a single parameter.
  #   :smaller — a variable proven structurally < xⱼ, OR an application whose
  #              spine head is such a variable (higher-order subterm rule below)
  #   :equal   — the same de Bruijn var as xⱼ, OR a constructor application
  #              syntactically identical to xⱼ's reconstruction (reconstruct-equal)
  #   :unknown — anything else (never claim ≤ for a possibly-larger term)
  defp arg_relation(nil, _pv), do: :unknown

  defp arg_relation({:var, i}, %{root: root, smaller: smaller}) do
    cond do
      MapSet.member?(smaller, i) -> :smaller
      i == root -> :equal
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

  # -- SizeChange semiring ----------------------------------------------------

  # Path composition (∘): Unknown absorbs, Equal is neutral, Smaller dominates.
  defp pathmul(:unknown, _), do: :unknown
  defp pathmul(_, :unknown), do: :unknown
  defp pathmul(:smaller, _), do: :smaller
  defp pathmul(_, :smaller), do: :smaller
  defp pathmul(:equal, :equal), do: :equal

  # Parallel arcs / matrix-mult sum: keep the strongest (Smaller > Equal > Unknown).
  defp add_rel(:smaller, _), do: :smaller
  defp add_rel(_, :smaller), do: :smaller
  defp add_rel(:equal, _), do: :equal
  defp add_rel(_, :equal), do: :equal
  defp add_rel(:unknown, :unknown), do: :unknown

  # -- matrix operations ------------------------------------------------------

  # Diagrammatic composition of two `k×k` matrices: (A∘B)[i][j] = Σₖ A[i][k]·B[k][j].
  # We add both `compose(a,b)` and `compose(b,a)` during closure, so the set is
  # closed under composition regardless of this convention's orientation.
  defp compose(a, b) do
    k = length(a)

    if k == 0 do
      []
    else
      Enum.map(0..(k - 1)//1, fn i ->
        Enum.map(0..(k - 1)//1, fn j ->
          Enum.reduce(0..(k - 1)//1, :unknown, fn kk, acc ->
            add_rel(acc, pathmul(entry(a, i, kk), entry(b, kk, j)))
          end)
        end)
      end)
    end
  end

  defp entry(m, i, j), do: m |> Enum.at(i) |> Enum.at(j)

  # Close the initial self-call matrices under composition to a fixpoint. The
  # lattice is finite (`k×k` over 3 values), and dedup by matrix equality makes
  # the worklist strictly shrink, so this always terminates.
  defp transitive_closure(matrices) do
    set = MapSet.new(matrices)
    close(MapSet.to_list(set), set)
  end

  defp close([], set), do: MapSet.to_list(set)

  defp close([m | work], set) do
    {work, set} =
      Enum.reduce(MapSet.to_list(set), {work, set}, fn n, {wk, st} ->
        [compose(m, n), compose(n, m)]
        |> Enum.reduce({wk, st}, fn c, {wk2, st2} ->
          if MapSet.member?(st2, c),
            do: {wk2, st2},
            else: {[c | wk2], MapSet.put(st2, c)}
        end)
      end)

    close(work, set)
  end

  defp idempotent?(m), do: compose(m, m) == m

  defp smaller_diagonal?(m) do
    k = length(m)
    k > 0 and Enum.any?(0..(k - 1)//1, fn i -> entry(m, i, i) == :smaller end)
  end

  # -- cross-function / mutual size-change ------------------------------------

  # The mutual group of `name`: the SCC of globals mutually reachable with it —
  # `{ g : name reaches g AND g reaches name } ∪ {name}`. `name`'s own callees
  # come from the passed `body` (authoritative); siblings' from `env`. A singleton
  # group means no mutual partner (⇒ #14 handles it).
  defp mutual_group(name, body, env) do
    forward = forward_reach(env, callees_of_body(body), MapSet.new([name]))

    forward
    |> MapSet.to_list()
    |> Enum.filter(fn g -> g == name or reaches?(env, callees_env(env, g), name, MapSet.new()) end)
    |> MapSet.new()
  end

  # Forward-reachable set of globals (transitive closure of the call graph).
  defp forward_reach(_env, [], acc), do: acc

  defp forward_reach(env, [g | rest], acc) do
    if MapSet.member?(acc, g),
      do: forward_reach(env, rest, acc),
      else: forward_reach(env, callees_env(env, g) ++ rest, MapSet.put(acc, g))
  end

  # True when any global forward-reachable from `body` (excluding `name`, whose real
  # body is the authoritative one passed in) still carries an elaborator pending-hole
  # placeholder — meaning the call graph is incomplete and the SCC cannot be trusted.
  defp pending_callee?(name, body, env) do
    callees_of_body(body)
    |> then(&forward_reach(env, &1, MapSet.new([name])))
    |> MapSet.delete(name)
    |> Enum.any?(&pending_body?(env, &1))
  end

  defp pending_body?(env, g) do
    not Env.total?(env, g) and match?(%{body: {:hole, _}}, Env.get_def(env, g))
  end

  defp callees_of_body(body), do: body |> called_globals() |> MapSet.to_list()

  defp callees_env(env, g) do
    if Env.total?(env, g) do
      []
    else
      case Env.get_def(env, g) do
        %{body: b} -> callees_of_body(b)
        _ -> []
      end
    end
  end

  # Certify a genuine mutual group total iff every square, idempotent endo-edge
  # `M_{f→f}` in the transitively-closed cross-function edge set has a
  # strictly-decreasing diagonal (the LJB non-termination criterion, negated,
  # generalised to the whole SCC — Idris `findNonTerminatingLoop`). `name`'s body
  # is read from the passed `body`, siblings' from `env`.
  defp mutual_group_total?(name, body, group, env) do
    arities =
      Map.new(group, fn f -> {f, arity_of(body_of(name, body, env, f))} end)

    edges =
      group
      |> Enum.flat_map(fn f -> function_edges(arities, f, body_of(name, body, env, f)) end)
      |> Enum.uniq()

    edges
    |> group_closure()
    |> Enum.all?(fn
      # Endo-edges `{f, f, M}` are square (rows = cols = arity(f)) by
      # construction, so `idempotent?/1` (the #14 square check) applies verbatim —
      # keeping the mutual criterion definitionally identical to #14 on the
      # diagonal, INCLUDING the arity-0 case (an empty endo-edge is idempotent
      # with no `:smaller` diagonal ⇒ rejected, matching a `f = g; g = f` loop).
      {f, f, m} -> not idempotent?(m) or smaller_diagonal?(m)
      {_f, _g, _m} -> true
    end)
  end

  defp body_of(name, body, _env, name), do: body
  defp body_of(_name, _body, env, f), do: (Env.get_def(env, f) || %{})[:body]

  defp arity_of(nil), do: 0
  defp arity_of(body), do: body |> peel_lams(0) |> elem(0)

  # All cross-function change edges `{f, g, M_{f→g}}` from f's body over every
  # intra-group call (self-calls ⇒ the #14 `f→f` edges). `nil` body (missing def)
  # contributes nothing — but a missing sibling cannot be in the group, since the
  # SCC was computed from `env` reachability.
  defp function_edges(_arities, _f, nil), do: []

  defp function_edges(arities, f, body) do
    {k, inner} = peel_lams(body, 0)
    st = initial_state(k)

    emit = fn g, args, s, acc ->
      case Map.get(arities, g) do
        nil -> acc
        m -> [{f, g, build_cross_matrix(m, k, args, s)} | acc]
      end
    end

    walk(emit, inner, st, [])
  end

  # -- multi-function edge composition + closure ------------------------------

  # Diagrammatic composition of two edges sharing an intermediate node:
  # `{a, b, Mx} ∘ {c, d, My}` is defined iff `b == c` and the dimensions agree
  # (cols(My) == rows(Mx) == arity(b)); it yields `{a, d, mat_compose(My, Mx)}`
  # — h-args-vs-a-params through b. Undefined compositions are dropped (sound:
  # every real loop is still generated from the base edges + defined compositions).
  defp compose_pair({a, b, mx}, {b, d, my}) do
    if row_len(my) == length(mx), do: {a, d, mat_compose(my, mx)}, else: nil
  end

  defp compose_pair(_e1, _e2), do: nil

  # General (possibly non-square) matrix composition: (A∘B)[i][j] = Σₗ A[i][l]·B[l][j],
  # with inner dimension l = cols(A) = rows(B). Reduces to `compose/2` when square.
  defp mat_compose(a, b) do
    inner = length(b)
    cols_b = row_len(b)

    rows(length(a), fn i ->
      rows(cols_b, fn j ->
        Enum.reduce(0..(inner - 1)//1, :unknown, fn l, acc ->
          add_rel(acc, pathmul(entry(a, i, l), entry(b, l, j)))
        end)
      end)
    end)
  end

  defp row_len([]), do: 0
  defp row_len([r | _]), do: length(r)

  # Close the base edge set under `compose_pair` to a fixpoint, dedup by
  # `{f, g, matrix}`. The processed-edge indexes are important here: the old
  # implementation compared every work item with every known edge in both
  # directions. Besides attempting source/target-incompatible pairs, it retried
  # an ordered pair when each member later became the work item. The growing
  # closure made that quadratic scan dominate certification for large proof SCCs.
  #
  # `by_source` and `by_target` contain only already-processed edges. When `edge`
  # is popped, compose it with compatible processed predecessors/successors and
  # with itself. Thus every compatible ordered pair is considered exactly once:
  # when its second-processed member is popped. Newly discovered edges enter the
  # same worklist, so this remains the full transitive fixpoint. Finite (bounded
  # names × bounded 3-valued matrices) with a strictly-growing dedup set ⇒ always
  # terminates.
  defp group_closure(edges) do
    set = MapSet.new(edges)
    gc(MapSet.to_list(set), set, %{}, %{})
  end

  defp gc([], set, _by_source, _by_target), do: MapSet.to_list(set)

  defp gc([{source, target, _matrix} = edge | work], set, by_source, by_target) do
    successors = Map.get(by_source, target, MapSet.new())
    predecessors = Map.get(by_target, source, MapSet.new())

    self_compositions = if source == target, do: [compose_pair(edge, edge)], else: []

    compositions =
      self_compositions ++
        Enum.map(successors, &compose_pair(edge, &1)) ++
        Enum.map(predecessors, &compose_pair(&1, edge))

    {work, set} =
      compositions
      |> Enum.reject(&is_nil/1)
      |> Enum.reduce({work, set}, fn composed, {pending, known} ->
        if MapSet.member?(known, composed),
          do: {pending, known},
          else: {[composed | pending], MapSet.put(known, composed)}
      end)

    by_source = Map.update(by_source, source, MapSet.new([edge]), &MapSet.put(&1, edge))
    by_target = Map.update(by_target, target, MapSet.new([edge]), &MapSet.put(&1, edge))

    gc(work, set, by_source, by_target)
  end

  defp reaches?(_env, [], _target, _visited), do: false

  defp reaches?(env, [g | rest], target, visited) do
    cond do
      g == target ->
        true

      MapSet.member?(visited, g) ->
        reaches?(env, rest, target, visited)

      true ->
        next =
          case Env.get_def(env, g) do
            %{body: b} -> b |> called_globals() |> MapSet.to_list()
            _ -> []
          end

        reaches?(env, next ++ rest, target, MapSet.put(visited, g))
    end
  end

  # Every global name referenced anywhere in a Core term.
  defp called_globals(term), do: gather_globals(term, MapSet.new())
  defp gather_globals({:global, n}, acc), do: MapSet.put(acc, n)
  defp gather_globals(t, acc) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_globals/2)
  defp gather_globals(l, acc) when is_list(l), do: Enum.reduce(l, acc, &gather_globals/2)
  defp gather_globals(_, acc), do: acc

  # -- per-parameter frame maintenance ----------------------------------------

  # Shift every tracked de Bruijn index up by `by` on entering `by` binders.
  defp shift_state(st, by) do
    %{
      roots: Enum.map(st.roots, &(&1 + by)),
      smallers: Enum.map(st.smallers, &shift(&1, by)),
      recons:
        Enum.map(st.recons, fn
          nil -> nil
          t -> shift_term(t, by)
        end)
    }
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

  # -- self-call detection (fast path) ----------------------------------------

  defp calls?(name, {:global, n}), do: n == name
  defp calls?(name, {:pi, _g, d, c}), do: calls?(name, d) or calls?(name, c)
  defp calls?(name, {:lam, _g, d, b}), do: calls?(name, d) or calls?(name, b)
  defp calls?(name, {:let, _g, t, v, b}), do: calls?(name, t) or calls?(name, v) or calls?(name, b)
  defp calls?(name, {:app, f, a}), do: calls?(name, f) or calls?(name, a)

  defp calls?(name, {:data, _n, ps, is}),
    do: Enum.any?(ps, &calls?(name, &1)) or Enum.any?(is, &calls?(name, &1))

  defp calls?(name, {:ctor, _n, args}), do: Enum.any?(args, &calls?(name, &1))

  defp calls?(name, {:case, s, m, brs}),
    do:
      calls?(name, s) or calls?(name, m) or
        Enum.any?(brs, fn {_c, _ar, b} -> calls?(name, b) end)

  # Same fail-closed fallback as `walk_node/4`: an unrecognized node is searched, not
  # assumed call-free. This is the fast path that decides whether `size_change_total?/2`
  # runs at all, so a false `false` here certifies a function nobody ever analysed.
  defp calls?(name, term) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.any?(fn
      child when is_tuple(child) -> calls?(name, child)
      children when is_list(children) -> Enum.any?(children, &(is_tuple(&1) and calls?(name, &1)))
      _leaf -> false
    end)
  end

  defp calls?(_name, _term), do: false
end
