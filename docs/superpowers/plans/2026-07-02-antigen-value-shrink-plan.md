# Antigen value-level post-shrink — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** When an assay fires, greedily rewrite the reified `Challenge` artifact into a minimal witness before banking it, so antibodies are minimal. The rewriter is purely structural (untyped); a same-violation-shape predicate is the sole validity gate.

**Architecture:** New `Antigen.Shrink` module — `minimize/3` runs a deterministic greedy sweep of single-edit candidates (4 rules), accepting the first that stays well-formed and keeps the predicate true, to a fixpoint or step budget. `Antigen.Runner`'s infection branch builds the predicate (pinning the violation tag via `same_shape?/2`), minimizes, and banks the minimized artifact.

**Tech Stack:** Elixir; `Cure.Core.Term` (`shift/3`, `term?/1`); `Antigen.Coverage`; `Antigen.Challenge`.

## Global Constraints

- **Predicate is the only validity gate (LOCKED):** the rewriter does untyped structural edits; a candidate is accepted iff `well_formed?(k)` (shape check) AND `pred.(k)` (same-shape violation still fires). `pred` crashes are rescued → reject. No per-edit re-typecheck.
- **Same-shape predicate (LOCKED):** `pred` pins the violation **tag** (leading atom of the detail tuple), NOT `{:violation, _}` — else a `:typed_term` shrink can wander into `{:violation, {:infer_failed, _}}` nonsense (spec §2/§6).
- **Determinism/reproducibility (LOCKED):** no clock, no RNG, no map-ordering dependence in `minimize`. Fixed enumeration. Step-budget only.
- **De Bruijn correctness by construction (LOCKED):** `well_formed?` is shape-only (`Term.term?` accepts any `{:var,k}` with `k≥0`), so it does NOT catch out-of-scope vars. Rule 3 (ctx drop) and rule 4's `:lam`/`:case` cases must be index-correct by construction; §7.3 guards against regressions.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- **One full build/test run at a time.**
- **StreamData quarantine:** `Shrink` is outside `generators/`/`assays/` and uses neither backend — unaffected, but keep it free of the literal `StreamData`.

### Confirmed codebase facts (probed)
- `Cure.Core.Term.shift(term, amount, cutoff \\ 0)` — **positional** cutoff; increments cutoff under binders (`:lam`/`:pi`/`:sigma` body → `c+1`; `:case` branch → `c+arity`). `Term.term?/1` is shape-only.
- `Antigen.Coverage.terms_of(challenge)` returns `[type, term | ctx]` — each ctx entry is a **bare type-term** (not `{name, term}`), so drop/shift acts on it directly.
- `Runner.occurs?/2` (`runner.ex:240-256`, private) is the crosses-binders free-occurrence check — reimplement in `Shrink` (don't reach into Runner's privates).
- `Runner.well_formed?/1` (`runner.ex:328-332`, private) = `Coverage.terms_of(c) |> Enum.all?(&Term.term?/1)` rescue false — **reimplement** the same one-liner in `Shrink` to avoid a Runner↔Shrink cycle (spec §8 said "expose if private"; reimplementing via the same primitives is equivalent and cleaner — a deliberate, documented refinement).
- `Runner.explore/1` infection branch is `runner.ex:24-32`; assay dispatch is `apply(opts[:assay] || assay_module(c.assay), :run, [c])`. The infection branch is shared by **every** `Challenge` kind (`:stub`, `:family`, `:def_group`, `:forcing_pair`, `:indexed_case`, `:rewrite_eq`, `:typed_term`, `:mutant_term`) via the assay registry (`runner.ex:291-302`) — `Shrink` only understands the `:typed_term`/`:mutant_term` payload shape (`type`/`term`/`ctx` keys), so Task 4's integration must gate the `minimize` call on `c.kind`, not apply it unconditionally.
- `Runner.explore/1` has **no** `challenges:` opt today (`runner.ex:13-14`: `challenges = draw(opts[:gen], count)`, unconditional). Task 4 must add it as part of the implementation, not treat it as possibly-already-present.

---

## File Structure

- **Create** `lib/antigen/shrink.ex` — `minimize/3`, `size/1`, `occurs?/2`, `well_formed?/1`, the rule/candidate generators, `child_slots/1`.
- **Modify** `lib/antigen/runner.ex` — infection branch minimizes before banking; `same_shape?/2`, `@shrink_budget`, `shrink_budget/1`.
- **Create** `test/antigen/shrink_test.exs`.

---

## Task 1: `Shrink` engine + term/type rules (1, 2, 4)

**Files:** Create `lib/antigen/shrink.ex`. Test: create `test/antigen/shrink_test.exs`.

**Interfaces:**
- Produces: `Shrink.minimize(challenge, pred, budget) :: Challenge`; `Shrink.size(challenge) :: non_neg_integer`. Handles rules 1 (subterm→atom), 2 (numeral shrink), 4 (structural unwrap incl. `:lam`/`:case` de Bruijn) over the `type` and `term` fields. Context drop (rule 3) is Task 2.

- [ ] **Step 1: Write the failing tests**
```elixir
defmodule Antigen.ShrinkTest do
  use ExUnit.Case, async: true
  alias Antigen.{Shrink, Challenge}

  # a well-typed-ish artifact whose predicate is purely structural for these unit tests
  defp art(term, ctx \\ []) do
    Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
      payload: %{sig: :v1, ctx: ctx, type: {:data, :Nat, [], []}, term: term})
  end

  defp s(n), do: {:ctor, :S, [n]}
  defp num(0), do: {:ctor, :Z, []}
  defp num(k), do: s(num(k - 1))

  test "numeral shrink + subterm→atom reduces under a 'contains an S' predicate to a single S Z" do
    a = art(s(s(s(num(0)))))                       # S(S(S Z)))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    assert out.payload.term == s(num(0))           # minimal term still headed by S
    assert pred.(out)
  end

  test "structural unwrap peels an app/ctor wrapper down to the payload leaf" do
    # plus(vcons(...), Z) — predicate keeps any term still containing a vcons
    inner = {:ctor, :vcons, [num(0), num(0), {:ctor, :vnil, []}]}
    a = art({:app, {:app, {:global, :plus}, inner}, num(0)})
    pred = fn ch -> contains_vcons?(ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    assert out.payload.term == {:ctor, :vnil, []} or match?({:ctor, :vcons, _}, out.payload.term)
    assert Shrink.size(out) < Shrink.size(a)
    assert pred.(out)
  end

  test "lam-body unwrap shifts free vars and is rejected when body uses its own param" do
    # NOT `fn _ -> true end`: rule 1 is tried before rule 4 ("here" order is
    # rule1 ++ rule2 ++ rule4) and fires on ANY node with node_count > 1 — the
    # top-level lam here has node_count 3 (lam + Nat-dom + var), so a fully
    # permissive predicate would let rule 1 replace the WHOLE lam with its
    # first minimal-atom menu item ({:ctor,:Z,[]}) before rule 4's lam-unwrap
    # is ever tried, and the test would observe `{:ctor,:Z,[]}`, not
    # `{:var,0}` (confirmed by hand-trace + probe against the plan's own
    # `size`/`node_count` helpers). The predicate must exclude the minimal
    # atoms so only a `:var`/`:lam`-shaped result is accepted, isolating rule
    # 4's behavior.
    keep_var_or_lam = fn ch -> match?({:var, _}, ch.payload.term) or match?({:lam, _, _}, ch.payload.term) end
    # λx:Nat. (var 1)  — body does NOT use var 0 ⇒ unwrap to (var 0) after shift
    a = art({:lam, {:data, :Nat, [], []}, {:var, 1}}, [{:data, :Nat, [], []}])
    out = Shrink.minimize(a, keep_var_or_lam, 1000)
    assert out.payload.term == {:var, 0}           # shifted down by 1
  end

  test "deterministic + monotone + idempotent" do
    a = art(s(s(num(0))))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    o1 = Shrink.minimize(a, pred, 1000)
    o2 = Shrink.minimize(a, pred, 1000)
    assert o1 == o2
    assert Shrink.size(o1) <= Shrink.size(a)
    assert Shrink.minimize(o1, pred, 1000) == o1   # idempotent
  end

  test "budget bounds the number of accepted edits" do
    # Same rule-1-dominates hazard as the lam test above: `fn _ -> true end`
    # would let rule 1 collapse `num(5)` straight to `{:ctor,:Z,[]}` in the
    # single accepted edit (size 11 -> 1, not size(a) - 1 = 10). Pin the
    # predicate to ":S-headed" so only rule 2's single-S-peel edits are ever
    # accepted, and assert *bounded progress* (behavioral: budget=1 makes
    # strictly less progress than a full minimize, never a hardcoded size
    # delta, since a single accepted edit generally changes `size` by more
    # than 1 — a peel changes both `node_count` and `numeral_magnitude`).
    a = art(num(5))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    out1 = Shrink.minimize(a, pred, 1)
    out_full = Shrink.minimize(a, pred, 1000)
    assert Shrink.size(out1) < Shrink.size(a)              # budget=1 makes some progress
    assert Shrink.size(out1) > Shrink.size(out_full)       # ...but strictly less than full minimization
    assert out_full.payload.term == s(num(0))              # fixpoint: S Z (matches the numeral-shrink test above)
  end

  test "a predicate that raises is safely treated as reject (LOCKED: pred crashes are rescued)" do
    # Global Constraints locks "pred crashes are rescued -> reject", implemented
    # by `safe_pred/2`, but no test anywhere exercised a raising predicate
    # before this — a real gap, since `well_formed?` is shape-only (doesn't
    # check de-Bruijn closedness), so a real assay could plausibly raise on an
    # out-of-scope candidate `pred` builds from. Here `pred` raises
    # specifically on `Z`, so the sweep must safely skip over it (not crash)
    # and settle at the last candidate where `pred` holds without raising.
    a = art(s(s(num(0))))   # S(S(Z))
    pred = fn ch ->
      case ch.payload.term do
        {:ctor, :S, _} -> true
        {:ctor, :Z, []} -> raise "boom"
        _ -> false
      end
    end
    out = Shrink.minimize(a, pred, 1000)   # must not raise
    assert out.payload.term == s(num(0))   # settles at S Z: Z is reachable but pred raises there
    assert pred.(out)
  end

  defp contains_vcons?({:ctor, :vcons, _}), do: true
  defp contains_vcons?(t) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_vcons?/1)
  defp contains_vcons?(l) when is_list(l), do: Enum.any?(l, &contains_vcons?/1)
  defp contains_vcons?(_), do: false
end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/shrink_test.exs` (module undefined).

- [ ] **Step 3: Implement** — create `lib/antigen/shrink.ex`:
```elixir
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
      first_accepted(rest, pred, b)   # shape-invalid: no pred call, no budget spent
    end
  end

  defp safe_pred(pred, k) do
    pred.(k)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  defp reseed(%Challenge{} = ch), do: %{ch | seed: :erlang.phash2({ch.kind, ch.payload})}

  # ── candidate enumeration (pinned order: ctx → type → term) ──────────────────
  # Task 1 covers type + term. Task 2 prepends ctx-drop candidates.
  defp candidates(%Challenge{payload: p} = ch) do
    field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
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
  defp rule4({:fst, p}), do: [p]
  defp rule4({:snd, p}), do: [p]
  defp rule4({:pair, a, b}), do: [a, b]
  defp rule4({:case, scrut, _m, branches}) do
    [scrut | for({_c, 0, body} <- branches, do: body)]   # scrut + arity-0 branch bodies only
  end
  defp rule4({:lam, _dom, body}) do
    if occurs?(body, 0), do: [], else: [Term.shift(body, -1, 0)]
  end
  defp rule4(_), do: []

  # child slots: {rebuild_fn, child} for every immediate sub-term (all Core formers)
  defp child_slots({:app, f, a}), do: [{&{:app, &1, a}, f}, {&{:app, f, &1}, a}]
  defp child_slots({:lam, d, b}), do: [{&{:lam, &1, b}, d}, {&{:lam, d, &1}, b}]
  defp child_slots({:pi, d, c}), do: [{&{:pi, &1, c}, d}, {&{:pi, d, &1}, c}]
  defp child_slots({:sigma, a, b}), do: [{&{:sigma, &1, b}, a}, {&{:sigma, a, &1}, b}]
  defp child_slots({:pair, a, b}), do: [{&{:pair, &1, b}, a}, {&{:pair, a, &1}, b}]
  defp child_slots({:fst, p}), do: [{&{:fst, &1}, p}]
  defp child_slots({:snd, p}), do: [{&{:snd, &1}, p}]
  defp child_slots({:ctor, n, args}), do: slot_list(args, &{:ctor, n, &1})
  defp child_slots({:data, n, ps, is}) do
    slot_list(ps, &{:data, n, &1, is}) ++ slot_list(is, &{:data, n, ps, &1})
  end
  defp child_slots({:case, s, m, brs}) do
    [{&{:case, &1, m, brs}, s}, {&{:case, s, &1, brs}, m}] ++
      Enum.with_index(brs)
      |> Enum.map(fn {{c, ar, body}, i} ->
        {fn nb -> {:case, s, m, List.replace_at(brs, i, {c, ar, nb})} end, body}
      end)
  end
  defp child_slots({:eq, ty, a, b}) do
    [{&{:eq, &1, a, b}, ty}, {&{:eq, ty, &1, b}, a}, {&{:eq, ty, a, &1}, b}]
  end
  defp child_slots({:refl, a}), do: [{&{:refl, &1}, a}]
  # :rewrite/:prim are real Core formers (Cure.Core.Term's node taxonomy) that
  # `Term.gen_term`/`Antigen.Generators.Mutation` never construct today, so
  # this clause is presently unreached — included anyway so term_candidates
  # doesn't silently stop descending if either ever appears (no binder in
  # either, matching Term.shift's own :rewrite/:prim clauses — no cutoff bump).
  defp child_slots({:rewrite, p, m, b}) do
    [{&{:rewrite, &1, m, b}, p}, {&{:rewrite, p, &1, b}, m}, {&{:rewrite, p, m, &1}, b}]
  end
  defp child_slots({:prim, op, args}), do: slot_list(args, &{:prim, op, &1})
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
  def occurs?({:lam, d, b}, k), do: occurs?(d, k) or occurs?(b, k + 1)
  def occurs?({:pi, d, c}, k), do: occurs?(d, k) or occurs?(c, k + 1)
  def occurs?({:sigma, a, b}, k), do: occurs?(a, k) or occurs?(b, k + 1)
  def occurs?({:case, s, m, brs}, k) do
    occurs?(s, k) or occurs?(m, k) or
      Enum.any?(brs, fn {_c, ar, body} -> occurs?(body, k + ar) end)
  end
  def occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  def occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  def occurs?(_leaf, _k), do: false

  # shape-only well-formedness (reimplements Runner.well_formed?/1 to avoid a cycle)
  defp well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end
end
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/shrink.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Shrink engine + term/type rules (subterm→atom, numeral, unwrap)"
```

---

## Task 2: rule 3 — context drop (de Bruijn)

**Files:** Modify `lib/antigen/shrink.ex`, `test/antigen/shrink_test.exs`.

**Interfaces:** Produces: `minimize` now also drops unreferenced `ctx` entries, shifting `term`/`type`/sibling-entry indices per spec §4 rule 3. Prepended to the candidate sweep (ctx before type/term).

- [ ] **Step 1: Write the failing tests**
```elixir
# append to test/antigen/shrink_test.exs
  test "context drop removes an unreferenced entry and shifts higher vars down" do
    # ctx [Nat, Nat]; term uses only var 0 ⇒ entry 1 is droppable, var 0 stays, higher shift
    a = art({:var, 0}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn _ -> true end, 1000)
    assert length(out.payload.ctx) < 2
    # every var in the result is in-scope for its ctx
    assert Antigen.Shrink.closed?(out)
  end

  test "context drop is REJECTED when the entry is referenced" do
    # term uses var 1 ⇒ entry 1 (abs index 1) may not be dropped; but entry 0 (var 0 unused) may
    a = art({:var, 1}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn ch -> Antigen.Shrink.occurs?(ch.payload.term, 0) end, 1000)
    # predicate forces keeping a reference to abs-0 after shifts; result stays closed + valid
    assert Antigen.Shrink.closed?(out)
    assert Antigen.Shrink.occurs?(out.payload.term, 0)
  end

  test "every ctx-drop candidate is de-Bruijn closed (regression guard for §7.3)" do
    a = art({:app, {:var, 0}, {:var, 2}},
            [{:data, :Nat, [], []}, {:data, :Nat, [], []}, {:data, :Nat, [], []}])
    for c <- Antigen.Shrink.candidates_for_test(a) do
      assert Antigen.Shrink.closed?(c), "candidate not closed: #{inspect(c.payload)}"
    end
  end

  test "context drop shifts cross-referencing sibling entries correctly (dependent ctx, §7.3)" do
    # An all-`Nat` ctx (no entry ever references another) can pass `closed?`
    # trivially even if the sibling-shift cutoff (`Term.shift(e, -1, d - pos)`)
    # were wrong, because every shift on such a ctx is a no-op — it never
    # exercises spec §4 rule 3's "asymmetric before/after-drop-position
    # handling". This ctx is genuinely dependent: pos0 references BOTH pos1
    # and pos3, straddling the sole droppable position (pos2), so a wrong
    # cutoff would produce a wrong (but still shape-`closed?`) index. Hand
    # (and mechanically probe-)verified expected output before writing this
    # assertion.
    ctx = [
      {:eq, {:type, 0}, {:var, 0}, {:var, 2}},   # pos0: local 0 -> abs 1 (pos1); local 2 -> abs 3 (pos3)
      {:data, :Vec, [], [{:var, 1}]},             # pos1: local 1 -> abs 3 (pos3)
      {:data, :Nat, [], []},                      # pos2: unreferenced — the sole droppable entry
      {:data, :Nat, [], []}                       # pos3
    ]
    a = art({:var, 0}, ctx)
    assert [c] = Antigen.Shrink.candidates_for_test(a)   # only pos2 is unreferenced
    assert c.payload.ctx == [
      {:eq, {:type, 0}, {:var, 0}, {:var, 1}},    # pos0: local 2 -> local 1 (target abs shifted 3 -> 2)
      {:data, :Vec, [], [{:var, 0}]},             # pos1: local 1 -> local 0 (target abs shifted 3 -> 2)
      {:data, :Nat, [], []}                       # old pos3, now pos2, content unchanged
    ]
    assert Antigen.Shrink.closed?(c)
  end
```

- [ ] **Step 2: Run — expect FAIL** (`ctx` never shrinks; `closed?`/`candidates_for_test` undefined).

- [ ] **Step 3: Implement** — in `lib/antigen/shrink.ex`, prepend ctx candidates and add the drop + a closedness checker (test-only export):
```elixir
  defp candidates(%Challenge{payload: p} = ch) do
    ctx_candidates(ch) ++ field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
  end

  # rule 3: drop each unreferenced absolute ctx position d (index 0 = innermost/list head)
  #
  # NOTE the explicit `//1` step: `0..(n - 1)` WITHOUT a step is an Elixir
  # footgun — when n=0 this is `0..-1`, and Elixir's *implicit* step defaults
  # to -1 whenever last < first, so the "empty" range actually enumerates
  # `[0, -1]` (two elements), not `[]`. Confirmed live: `elixir -e
  # 'IO.inspect(Enum.to_list(0..(0-1)))'` prints `[0, -1]` with a compiler
  # warning. For an empty ctx (the DEFAULT in every test fixture's `art/2`
  # helper) that bug would make `drop_candidate` fabricate two phantom
  # "drop position 0 / -1" candidates whose payload is byte-identical to the
  # input for any var-free term/type (both shifts degrade to no-ops) — and
  # since ctx-candidates are enumerated FIRST, `first_accepted` would accept
  # that no-op every sweep (it trivially passes `well_formed?` and `pred`,
  # nothing changed), burning the whole budget on phantom edits and returning
  # the unmodified input. `//1` makes `n=0` correctly yield an empty range.
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
          {e, pos} when pos < d -> Term.shift(e, -1, d - pos)   # local k>=d-pos shift down
          {e, _pos} -> e                                         # pos>d: content unchanged
        end)

      %{ch | payload: %{p | ctx: new_ctx,
                            term: Term.shift(p.term, -1, d + 1),
                            type: Term.shift(p.type, -1, d + 1)}}
    end
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
  defp max_index_below({:lam, d, b}, depth), do: max(max_index_below(d, depth), max_index_below(b, depth + 1))
  defp max_index_below({:pi, d, c}, depth), do: max(max_index_below(d, depth), max_index_below(c, depth + 1))
  defp max_index_below({:sigma, a, b}, depth), do: max(max_index_below(a, depth), max_index_below(b, depth + 1))
  defp max_index_below({:case, s, m, brs}, depth) do
    [max_index_below(s, depth), max_index_below(m, depth) |
     Enum.map(brs, fn {_c, ar, body} -> max_index_below(body, depth + ar) end)] |> Enum.max()
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
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/shrink.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Shrink rule 3 — context drop with de Bruijn shift"
```

---

## Task 3: synthetic full-machinery test (spec §7.4)

**Files:** Modify `test/antigen/shrink_test.exs`.

**Interfaces:** Consumes only public `Shrink.minimize/3`; asserts end-to-end minimization of a real generated deep term under a composite predicate (infer-ok ∧ contains vcons).

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/shrink_test.exs (add aliases at top: Antigen.Generators.{Term, SigMenu}, Antigen.Backend.StreamData as B, Cure.Core.{Context, Kernel})
  test "shrinks a deep well-typed term to a minimal vcons-containing witness (§7.4)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    infer_ok? = fn ch ->
      c = SigMenu.rebuild_context(env, ch.payload.ctx)
      match?({:ok, _}, Kernel.infer(c, ch.payload.term))
    end
    pred = fn ch -> infer_ok?.(ch) and contains_vcons?(ch.payload.term) end

    # find a generated well-typed term containing a vcons, wrap it deeper, then shrink
    seed =
      B.interp(Term.gen_term(ctx, {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}))
      |> Enum.take(50)
      |> Enum.find(&contains_vcons?/1)

    # Load-bearing, not vacuous: `assert seed` fails loudly (not silently skips)
    # if no vcons-containing term is sampled — mirrors Task 4's `assert deep, "..."`
    # guard rather than an `if seed do ... end` that would pass with zero
    # assertions run on a bad draw (recursive-skeptical-review finding).
    assert seed, "no vcons-containing term sampled in 50 draws"
    a = art(seed)
    assert pred.(a)
    out = Shrink.minimize(a, pred, 5000)
    assert pred.(out)
    assert Shrink.size(out) <= Shrink.size(a)
    # minimal witness: a lone vcons whose args are minimal atoms
    assert match?({:ctor, :vcons, [_, _, _]}, out.payload.term)
    assert Shrink.size(out) <= 8
  end
```

- [ ] **Step 2: Run — expect FAIL** (if the assertion bounds are not yet met by the implementation, or the composite pred surfaces a rule gap). If it passes immediately, tighten the `size(out) <= 8` bound to the observed minimum so the test is load-bearing, and note why in the commit.

- [ ] **Step 3: Implement** — only if a real rule gap surfaces (e.g. a former lacking a `child_slots` clause). Otherwise no production change — this task validates Tasks 1–2 against generated input. Record the observed minimal size.

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add test/antigen/shrink_test.exs lib/antigen/shrink.ex
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): Shrink minimizes a generated deep term to a minimal witness"
```

---

## Task 4: Runner integration — same-shape pred + shrink-before-bank (§6, §7.5)

**Files:** Modify `lib/antigen/runner.ex`, `test/antigen/shrink_test.exs`.

**Interfaces:** Produces: `Runner.explore/1` accepts an `opts[:challenges]` override (falls back to the existing generator path) and minimizes any `:typed_term`/`:mutant_term` infection before banking (other kinds bank unminimized, unchanged from today); `same_shape?/2` (tag comparator), `@shrink_budget`/`shrink_budget/1`. Consumes: `Shrink.minimize/3`.

- [ ] **Step 1: Write the failing test** (buggy-infer end-to-end via `opts[:assay]`)
```elixir
# append to test/antigen/shrink_test.exs
  defmodule BuggyMutationAssay do
    # wraps Assays.Mutation with an infer that WRONGLY ACCEPTS :head_swap mutants
    alias Cure.Core.Kernel
    def run(%{payload: %{fault: %{kind: :head_swap}}} = c) do
      Antigen.Assays.Mutation.run(c, fn ctx, t ->
        case Kernel.infer(ctx, t) do
          {:error, _} -> {:ok, {:type, 0}}   # pretend it type-checks ⇒ wrongly accepted
          ok -> ok
        end
      end)
    end
    def run(c), do: Antigen.Assays.Mutation.run(c)
  end

  test "Runner shrinks a deep head_swap survivor to the bare minimal witness before banking (§7.5)" do
    alias Antigen.Generators.{Mutation, SigMenu}
    alias Antigen.Backend.StreamData, as: B
    tmp = System.tmp_dir!()
    corpus = Path.join(tmp, "shrink_ab_#{:erlang.unique_integer([:positive])}.sexp")
    File.rm(corpus)

    # a deep head_swap mutant (grown by deepen), in a padded context
    deep =
      B.interp(Mutation.mutant())
      |> Enum.take(400)
      |> Enum.find(fn c -> c.payload.fault.kind == :head_swap and c.payload.fault.depth >= 3 end)

    assert deep, "no deep head_swap mutant sampled"

    Antigen.Runner.explore(
      challenges: [deep], count: 1, assay: BuggyMutationAssay,
      corpus_path: corpus, seeds_path: Path.join(tmp, "seeds_ignore.sexp"),
      report_dir: tmp
    )

    banked = Antigen.Corpus.stream(corpus) |> Enum.flat_map(fn {:ok, c} -> [c]; _ -> [] end)
    assert [ab] = banked
    # NOTE on what this does/doesn't prove: `Antigen.Assays.Mutation.run/2`
    # (unmodified, existing module) treats ANY `{:ok, _}` from `infer_fun` as
    # a violation, regardless of why inference succeeded — and this wrapper's
    # `{:error, _} -> {:ok, ...}; ok -> ok` makes `infer_fun` return `{:ok,_}`
    # unconditionally, for ANY term (including one that's genuinely
    # well-typed on its own merits, e.g. bare `Z`). So `pred` here is
    # unconditionally true for any well-formed candidate — rule 1
    # (subterm->minimal-atom, tried before rule 4) will very likely collapse
    # `deep` straight to an unrelated minimal atom (e.g. `{:ctor,:Z,[]}`) on
    # the first accepted edit, not progressively peel the `deepen` wrappers
    # down to a `head_swap`-specific witness. That's expected, not a bug in
    # this plan: spec §2 already flags that a same-shape `pred` is
    # "automatically as strict as a bare `{:violation, _}` match" for
    # `Assays.Mutation`, i.e. no additional protection for this assay. What
    # this test actually proves is narrower than "the minimal head_swap
    # witness": that `explore/1` wires minimize-before-bank correctly, that
    # `minimize` makes real progress, and that the banked artifact still
    # trips whatever assay is configured — not that shrink preserves the
    # ORIGINAL fault's specific shape for `:mutant_term` challenges.
    assert Antigen.Shrink.size(ab) < Antigen.Shrink.size(deep)
    assert match?({:violation, {:accepted_ill_typed, _, _}}, BuggyMutationAssay.run(ab))
  end
```
**Confirmed (probed against `lib/antigen/runner.ex:12-14`), not conditional:** `explore/1` does **not** accept `challenges:` today — it unconditionally runs `challenges = draw(opts[:gen], count)`. `draw(nil, count)` calls `Antigen.Backend.StreamData.interp(nil)`, which has no matching clause (`lib/antigen/backend/stream_data.ex`) and raises `FunctionClauseError`. So on the *unmodified* Runner, the Step 1 test above fails with that crash, not with the "banks the raw `deep`" story below — Step 3 below adds the `challenges:` opt as a required, not optional, part of this task.

- [ ] **Step 2: Run — expect FAIL** — `FunctionClauseError` in `Antigen.Backend.StreamData.interp/1` (from `draw(opts[:gen] = nil, count)`), because `explore/1` has no `challenges:` opt yet. This is the correct red state for this test — it fails because the seam doesn't exist, not yet because shrinking doesn't happen.

- [ ] **Step 3: Implement** — first add the `challenges:` seam at the top of `explore/1` (`lib/antigen/runner.ex:12-14`), keeping the existing generator path as the default:
```elixir
  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    challenges = opts[:challenges] || draw(opts[:gen], count)
```
Then edit the infection branch (§6). **Scope the shrink to the challenge kinds `Shrink` actually understands** — `Shrink.candidates/1`/`size/1` dereference `payload.type`/`payload.term`/`payload.ctx` directly (`p.type` etc. raise `KeyError` if absent, not `nil`), which only `:typed_term`/`:mutant_term` payloads have; every other kind this same branch also serves (`:stub`, `:family`, `:def_group`, `:forcing_pair`, `:indexed_case`, `:rewrite_eq` — see `Antigen.Coverage.terms_of/1`'s per-kind clauses) has a different payload shape and would crash `Shrink.minimize` outright. Without this guard, an infection on any non-typed_term/mutant_term assay (e.g. `Totality`, `Positivity`, `Reflexivity`, `Indexed`, `Rewrite`, `Universes`, `Stub`) turns a normal "report + bank" infection into a hard crash of the whole `explore/1` run — a regression versus current behavior, and not hypothetical (this branch has banked real antibodies for other verticals per the git history):
```elixir
            {:violation, orig_detail} = v ->
              assay = opts[:assay] || assay_module(c.assay)
              pred = fn ch ->
                case apply(assay, :run, [ch]) do
                  {:violation, detail} -> same_shape?(detail, orig_detail)
                  _ -> false
                end
              end

              c_min =
                if c.kind in [:typed_term, :mutant_term],
                  do: Antigen.Shrink.minimize(c, pred, shrink_budget(opts)),
                  else: c

              {:ok, path} = Report.write_infection(opts[:report_dir], c_min, v, summarize(acc, count))
              IO.puts(Report.breadcrumb(c_min, path))
              Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))
              %{acc | infections: acc.infections + 1}
```
Add near the other private helpers:
```elixir
  @shrink_budget 2000
  defp shrink_budget(opts), do: opts[:shrink_budget] || @shrink_budget

  defp same_shape?(d1, d2) when is_tuple(d1) and is_tuple(d2), do: elem(d1, 0) == elem(d2, 0)
  defp same_shape?(d1, d2), do: d1 == d2
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Runner shrinks infections (same-shape pred) before banking"
```

---

## Task 5: Acceptance — quarantine + full suite

**Files:** none (verification only).

- [ ] **Step 1: Quarantine** — `mix test test/antigen/architecture_test.exs`. PASS (Shrink is outside generators/assays; no `StreamData` literal).
- [ ] **Step 2: Full suite ONCE** — `mix test`. All green (§7.7: with 0 organic infections the Runner change is inert on existing corpora; banked seeds unchanged).
- [ ] **Step 3: Sanity explore** — `MIX_ENV=test mix antigen --count 300`. Expect unchanged health lines and **0 infections** (the shrink path stays dormant). Record it.
- [ ] **Step 4:** No commit.

---

## Self-Review

**Spec coverage:** §2 predicate-only-gate → Task 4's `same_shape?` + Task 1's `well_formed?`+`safe_pred`. §3 interface/seed-recompute → Task 1 `minimize/3`+`reseed`. §4 rules 1/2/4 → Task 1; rule 3 → Task 2; search discipline (ctx→type→term, pre-order, rules 1→2→4, greedy restart, budget) → Task 1 `candidates`/`term_candidates`/`sweep` + Task 2 `ctx_candidates` prepend. §5 size/monotone/idempotent/deterministic → Task 1 tests + `size/1`. §6 Runner integration → Task 4. §7 tests 1–2 Task 1; 3 Tasks 1/2 (`closed?`); 4 Task 3; 5 Task 4; 6 Task 1 budget test; 7 Task 5. §8 files/occurs?/well_formed? reimpl → Tasks 1/4. §9 non-goals respected (fault kept verbatim; no ChoiceSeq; no provenance path).

**Placeholder scan:** none. Task 3's rule-gap fallback stays conditional (implement only if a real gap surfaces); Task 4's `challenges:` seam is now a committed, non-conditional part of Step 3 (see Deviations below) — not a placeholder either way.

**Type consistency:** `minimize/3`, `size/1`, `occurs?/2`, `closed?/1`, `candidates_for_test/1` defined Task 1/2, used in later tasks. `same_shape?/2`, `shrink_budget/1`, `@shrink_budget` Task 4. `child_slots`/`term_candidates`/`drop_candidate` internal, consistent across Tasks 1–2.

**Deviations recorded (recursive-skeptical-review pass):**
- `well_formed?` is reimplemented in `Shrink` (not exposed from Runner) to avoid a Runner↔Shrink cycle — equivalent one-liner over the same primitives (Global Constraints).
- Task 2's `ctx_candidates` originally used `0..(n - 1)` (no explicit step). Elixir's implicit-step range defaults to step `-1` whenever `last < first`, so at `n=0` (the default ctx in every test fixture's `art/2` helper) this enumerated `[0, -1]` instead of `[]` — verified live (`elixir -e 'IO.inspect(Enum.to_list(0..(0-1)))'` prints `[0, -1]` with a compiler warning). Traced through `drop_candidate`, this fabricated a phantom no-op "drop" candidate that `first_accepted` would greedily accept every sweep (content-identical to the input, so it trivially passes `well_formed?`/`pred`), burning the entire budget on no-op edits and returning the artifact unshrunk — breaking essentially every Task 1/2/3 test that relies on the default empty ctx. Fixed to `0..(n - 1)//1`.
- Task 4's Runner integration originally applied `Shrink.minimize` unconditionally in the shared infection branch. Since that branch serves every `Challenge` kind (via the assay registry) but `Shrink` only understands the `:typed_term`/`:mutant_term` payload shape, an infection on any other assay (`Totality`/`Positivity`/`Reflexivity`/`Indexed`/`Rewrite`/`Universes`/`Stub`) would have crashed the whole `explore/1` run instead of reporting+banking it. Fixed by gating the `minimize` call on `c.kind in [:typed_term, :mutant_term]`.
- Task 4's `challenges:` opt was originally described as possibly-already-present ("confirm... or add a thin seam"), and its red test's expected failure was described as a size mismatch. Probed and confirmed `explore/1` has no `challenges:` opt today and would instead crash with `FunctionClauseError` (`draw(nil, count)` → `Backend.StreamData.interp(nil)`, no matching clause). Fixed by making the `challenges:` opt a required, explicit part of Step 3, and correcting Step 2's expected-failure description to match.
- Task 3's `if seed do ... end` could pass with zero assertions run if no vcons-containing term were sampled in 50 draws. Fixed to `assert seed, "..."` (unconditional body after), matching Task 4's own `assert deep, "..."` pattern for the same class of risk.
- Task 1's `child_slots/1` had no clause for the `:rewrite`/`:prim` Core formers (present in `Cure.Core.Term`'s node taxonomy), so `term_candidates` would silently stop descending into either if they ever appeared. Confirmed currently unreachable (`Term.gen_term`/`Antigen.Generators.Mutation` never construct either node), but added the two clauses for structural completeness against the full Core taxonomy.
- Task 4's `BuggyMutationAssay` wrapper, combined with `Antigen.Assays.Mutation.run/2`'s existing (unmodified) "any `{:ok,_}` on a `:mutant_term` payload is a violation" contract, makes `infer_fun` return `{:ok,_}` unconditionally for every term — so the test's `pred` is effectively permissive for any well-formed candidate, and rule 1 will very likely collapse `deep` to an unrelated minimal atom rather than a `head_swap`-specific witness. Confirmed by direct code inspection, not a plan bug (spec §2 already flags this exact weak-guard characteristic for `Assays.Mutation`), but the test's inline comment overclaimed what's demonstrated. Added a comment clarifying the narrower, accurate claim (pipeline wiring + progress + still-trips-the-assay) without changing the assertions or the underlying (spec-locked) behavior.
- Task 2's §7.3 regression-guard test used a ctx of three bare `Nat` entries — none reference each other, so every sibling-entry shift in that test degrades to a no-op and the test could pass even if `Term.shift(e, -1, d - pos)`'s cutoff were wrong, contrary to spec §7.3's explicit requirement to test "the asymmetric before/after-drop-position handling". Added a second test with a genuinely dependent ctx (one entry referencing two different sibling positions straddling the sole droppable one) and exact expected post-drop ctx values, hand-derived and mechanically probe-verified against a standalone reimplementation of `Term.shift`/`occurs?`/`drop_candidate` before writing the assertion — confirms the plan's rule-3 arithmetic is correct, and gives the regression guard a case it can actually fail on.
- Global Constraints locks "`pred` crashes are rescued → reject" (implemented by `safe_pred/2`), but no test anywhere exercised a raising predicate. Real gap, not cosmetic: `well_formed?` is shape-only and doesn't check de-Bruijn closedness, so a real assay's `pred` could plausibly raise on an out-of-scope candidate. Added a Task 1 test with a predicate that raises on a specific reachable term, asserting `minimize` doesn't crash and settles at the last non-raising accepted state.
- Task 1's "lam-body unwrap" and "budget bounds the number of accepted edits" tests both originally used a fully permissive predicate (`fn _ -> true end`/`keep`). Hand-traced (and mechanically double-checked with a probe reusing the plan's own `node_count`/`numeral_magnitude`/`size` definitions) against the plan's own rule-priority order (`here = rule1 ++ rule2 ++ rule4`, first accepted candidate wins): rule 1 (subterm→minimal-atom) fires on *any* node with `node_count > 1` and, under a permissive predicate, always wins immediately over rule 4/rule 2 since it's tried first and offers the largest single jump ("cheapest/highest-impact first" per spec §4). Concretely: the lam test's `node_count(lam) = 3 > 1`, so a permissive predicate would let rule 1 collapse the whole lambda straight to `{:ctor,:Z,[]}` in one accepted edit, never reaching rule 4's lam-unwrap — the test's asserted `{:var, 0}` would not be observed. Similarly the budget test's `num(5)` (`size = 11`) would collapse to `{:ctor,:Z,[]}` (`size = 1`) in the single accepted edit, not `size(a) - 1 = 10`. Fixed the lam test's predicate to `match?({:var,_},...) or match?({:lam,_,_},...)` (excludes the minimal atoms, isolating rule 4's behavior) and rewrote the budget test to pin the predicate to `:S`-headed terms and assert bounded-progress behaviorally (`size(out1) < size(a)` and `size(out1) > size(out_full)`) rather than a hardcoded `size(a) - 1`, since a single accepted rule-2 edit changes `size` by 2 (both `node_count` and `numeral_magnitude` drop by 1), not 1.
