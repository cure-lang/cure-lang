# Antigen value-level post-shrink — design

**Status:** scheduled (Tier-1 of the shrinking work). This is the cheaper minimizer
the `ChoiceSeq` reference spec (`2026-07-02-antigen-choiceseq-backend-design.md` §9)
gates itself behind: build `ChoiceSeq` **only if** this proves insufficient on real
deep counterexamples. Expectation stands that `ChoiceSeq` stays shelved for terms.

**Parity ledger:** Tier-B report §"Reach left open" → the value-level post-shrink
bundled-with-shrinking item. Closes the "banked antibody is a depth-12 monster"
problem for the antibodies we can actually produce.

**One-liner:** when an assay fires, greedily rewrite the reified `Challenge`
artifact into a *minimal* witness before banking it — so antibodies are minimal by
construction. The rewriter is **purely structural (untyped)**; the caller's
predicate ("same assay still violates") is the sole validity gate.

---

## 1. Problem

`Antigen.Runner.explore/1` banks the **raw** artifact on an infection
(`runner.ex:31`: `Corpus.append(corpus_path, c, dedup_key(c, :antibody))`) with zero
minimization. The generator is now lazy (`@max_size` 3→12), so a real infection
would bank a deep, mostly-irrelevant term. A banked antibody should be the *smallest*
term that still trips the bug — easier to read, to regression-test, and to dedupe.

**Reality check (why this is Tier-1, not `ChoiceSeq`).** The generator finds **0
organic infections** today (A and B both closed at `survivors=0`; banked mutation/
conversion seeds are hand-built minimal). So shrinking has no organic input yet.
This is infrastructure: it makes future organic counterexamples minimal, and it is
validated now against *manufactured* violations (§6). It is the cheap tier; the
expensive internal shrinker (`ChoiceSeq`) stays gated behind it.

---

## 2. Core insight — the predicate is the only validity gate

The rewriter performs **purely structural, untyped edits** on the artifact. A
candidate edit is accepted iff a caller-supplied predicate `pred.(candidate)` still
holds, where `pred` = "the same assay still returns a violation **of the same
shape** as the original" — see the precise definition and its rationale below;
`{:violation, _}` alone (matching *any* violation) is **not** sufficient, and using
it naively is a real bug, not a simplification (§6 spells out the fix).

- For a `:typed_term` artifact the assay runs `Kernel.infer`/`check`, so most edits
  that break well-typedness make the assay stop firing the *original* bug's
  violation shape → the candidate is rejected on a same-shape `pred`.
  **Caution:** `Antigen.Assays.Term.run/1` (`lib/antigen/assays/term.ex:21-29`)
  itself returns `{:violation, {:infer_failed, e}}` when `Kernel.infer` fails —
  i.e. "became ill-typed" is *itself* one of this assay's violation shapes, not an
  assay-silencing outcome. A predicate as loose as `match?({:violation, _}, ...)`
  would happily accept a shrink step that turns e.g. an original
  `{:not_idempotent, _, _}` infection into an unrelated ill-typed nonsense term —
  destroying the very bug being minimized. Well-typedness is preserved only if
  `pred` pins the violation **tag** (the discriminating atom/shape of the second
  tuple element, e.g. `:not_idempotent` vs `:infer_failed`), not merely the
  `{:violation, _}` wrapper.
- For a `:mutant_term` artifact the predicate is "the (possibly buggy) `infer`
  still wrongly accepts this ill-typed term" — `Antigen.Assays.Mutation.run/1,2`
  has exactly one violation shape (`{:accepted_ill_typed, term, fault}`), so a
  same-shape `pred` is automatically as strict as a bare `{:violation, _}` match
  for this assay — but the general mechanism (§6) must not assume that holds for
  every assay.

Thus the rewriter needs **no type inference, no bidirectional walk, no per-rule
re-typecheck**. This is the `ChoiceSeq` spec's "validity is free" property, obtained
here through the predicate rather than through interleaved generation. The rewriter
is a dumb structural search; all semantics live in `pred`.

The only structural obligation (so `pred` doesn't crash on garbage): a candidate
must be a well-formed Core term (arities, universe levels, non-negative indices).
The Runner's `well_formed?/1` (`runner.ex:328-332`) already provides exactly this —
but **only this**: it delegates to `Cure.Core.Term.term?/1`, whose own moduledoc
states it is "a shape check only" — for `{:var, k}` it checks `k >= 0` and nothing
else, so it does **not** verify de-Bruijn-closedness (that every `{:var, k}` is
`k < ctx length` at its binding depth). The shrinker reuses `well_formed?/1` as a
pre-gate for exactly what it *does* check (structural shape), and additionally
rescues any exception from `pred` (→ reject candidate) as the backstop for
anything shape-valid but semantically broken (e.g. an out-of-scope variable
`Eval`/`Kernel` chokes on). Because there is no real closedness gate, **every rule
that could introduce an out-of-scope or mis-scoped variable must be correct by
construction** — this is why rule 3 (§4) and the binder-crossing case in rule 4
(§4) get the detailed de-Bruijn treatment below; there is no safety net to catch a
mistake there short of a runtime crash rescued by `pred`.

---

## 3. Module & interface

New module `Antigen.Shrink` at `lib/antigen/shrink.ex`. It is **not** under
`generators/` or `assays/`, so it may call the kernel freely and is unaffected by
the StreamData quarantine (it uses neither StreamData nor `ChoiceSeq`).

```elixir
@type pred :: (Challenge.t() -> boolean())
@spec minimize(Challenge.t(), pred(), non_neg_integer()) :: Challenge.t()
def minimize(challenge, pred, budget)
```

- Returns a `Challenge` with the **same** `kind`/`assay`/`label`/`fault`/`sig`, a
  minimized `payload` (`ctx`/`type`/`term`), and `seed` **recomputed
  unconditionally** as `:erlang.phash2({challenge.kind, minimized_payload})` — NOT
  by reusing `Runner.seed_of/1` (`runner.ex:315`, `defp` — not callable from this
  module anyway). `seed_of/1`'s `c.seed || :erlang.phash2(...)` short-circuits to
  the existing seed whenever one is already set, which it always is by the time
  `minimize` runs (`runner.ex:18` sets it before dispatching to the assay) — so
  naively reusing it on `c_min` (inherited via struct copy from `c`) would leave
  `c_min.seed == c.seed` unchanged, silently defeating "recomputed." The seed must
  identify the *minimized* content (so report filenames/breadcrumbs, which key off
  `c.seed`, uniquely identify the shrunk artifact rather than colliding with the
  pre-shrink one).
- `budget` is a **step budget** (max candidate evaluations, i.e. `pred` calls). No
  wall-clock — the shrink must be deterministic and reproducible. On exhaustion,
  return the best (smallest accepted) artifact so far.
- **Precondition:** `pred.(challenge)` is already true (the Runner only calls
  `minimize` on a confirmed infection). `minimize` never returns an artifact for
  which `pred` is false; if no edit is accepted it returns the input unchanged.

---

## 4. Rewrite rules

Each rule is a **candidate generator**: `(artifact) -> [artifact]`, producing
strictly-smaller structural variants. All edits are untyped; `pred` filters. Rules,
cheapest/highest-impact first:

1. **subterm → minimal-atom.** For each subterm position **whose own
   `term_node_count` is `> 1`** (i.e. a compound, not already a leaf — this guard
   is required, not optional: every menu item below is itself a 1-node,
   0-numeral-magnitude term, so applying this rule to an already-1-node position
   like `{:var, k}` or `{:global, g}` would produce a same-size candidate,
   violating §5's strict-decrease guarantee), replace the subtree with a minimal
   closed inhabitant from the fixed menu set, tried in this fixed order:
   `[{:ctor,:Z,[]}, {:ctor,:vnil,[]}, {:ctor,:T,[]}, {:type,0}]`. Collapses deep
   filler to a leaf. (No type inference — `pred` rejects the type-wrong ones.) Given
   the `> 1`-node guard above, a compound subtree can never literally equal a
   1-node menu item, so every menu item is a legitimate, strictly-smaller
   candidate for a guarded position — no additional "already equal" check is
   needed.
2. **numeral shrink.** For each `Sᵏ Z` (k≥1), try `Sᵏ⁻¹ Z` … toward `Z`. Lowers Vec
   indices, `conv_depth`, and any Nat magnitude.
3. **context drop.** `ctx` is a kernel-order list, index `0` = innermost (matches
   `Antigen.Generators.SigMenu.rebuild_context/2`'s doc convention). `term`/`type`
   reference ctx with **absolute** indices (`{:var, k}` = ctx position `k`
   directly). But each ctx entry's own stored type term uses **local, per-entry**
   indices: entry at position `p`'s term has `{:var, k}` meaning absolute position
   `p+1+k` (confirmed against `Antigen.Generators.Context.nat_var_indices/1`,
   `lib/antigen/generators/context.ex:49-59`, which builds exactly this
   convention when generating a new entry's type from what's already in `acc`).
   This asymmetry means dropping absolute position `d` requires:
   - **Reject the drop** if `{:var, d}` occurs in `term`/`type` (absolute
     indexing), OR if any ctx entry at position `p < d` contains local index
     `d - p - 1` (which denotes absolute position `d`) in its own stored term.
   - **`term`/`type`:** shift every `{:var, j}` with `j > d` down by one — i.e.
     `Cure.Core.Term.shift(term_or_type, -1, d + 1)` (the real
     `Term.shift/3`, `lib/cure/core/term.ex:97-134`, takes `cutoff` as a
     **positional** third argument, not a keyword — `shift(term, amount, cutoff
     \\ 0)`).
   - **Ctx entries at position `p < d`** (the only ones that can reference `d`,
     since local indices only ever point *outward*, to higher absolute
     positions): shift every local index `k >= d - p` down by one — i.e.
     `Cure.Core.Term.shift(entry_p_term, -1, d - p)` — since local `k` there maps
     to absolute `p+1+k > d`. Absolute references `< d` (local `k < d-p-1`) are
     untouched.
   - **Ctx entries at position `p > d`:** **no term edit at all.** Every index
     `d` could reference lies at absolute position `> p > d` in this entry's own
     scope (local indexing only reaches outward), so `d` itself is never
     reachable from here; and because this entry's own position *and* every
     position it could reference both shift down by exactly one, its local
     indices are already correct relative to their new positions. Only its slot
     in the list changes (its new position is `p-1`), never its content.
   - This is the trickiest of the two rules that manipulate de Bruijn indices
     (rule 4's `:lam`-body case is the other, §4 below) and the only one that can
     affect terms *other than the one being edited* (sibling ctx entries) — get
     the three bullets above exactly right; there is no closedness re-check to
     catch a mistake here (§2), and §7.3's per-rule closedness test exists
     specifically to catch a regression.
4. **structural unwrap.** Replace a compound with one of its immediate
   sub-terms, where "immediate sub-term" means a sub-term *at the same binder
   depth* — never reach under a binder the compound itself introduces without
   handling the crossing explicitly:
   - `{:app, f, a}` → `f` or `a`. `{:ctor, _, args}` → any element of `args`.
     `{:fst, p}`/`{:snd, p}` → `p`. `{:pair, a, b}` → `a` or `b`. None of these
     introduce a binder, so no index adjustment is needed.
   - `{:case, scrut, motive, branches}` → `scrut` (no adjustment: `:case` does not
     bind in `scrut`), **or** the body of a branch `{ctor, 0, body}` **whose arity
     is exactly 0** (no adjustment needed either, since a 0-arity branch binds
     nothing — `Term.shift`'s own branch case confirms this: `cutoff + ar` with
     `ar = 0` is a no-op). A branch with `arity > 0` is **not** a valid unwrap
     target under this rule (its body is one or more binders deeper than the
     `:case` node) — recovering one would need the same shift-and-reject
     machinery as `:lam` below, which v1 does not implement; skip it. This
     restriction is not cosmetic: it is exactly what recovers a
     `Mutation.deepen/3` `:case_branch`-wrapped fault (the wrapped term always
     sits in the arity-0 `:Z` branch, `nat_branches/1` in
     `lib/antigen/generators/mutation.ex:105`), which is what makes the §7.5
     end-to-end shrink able to strip that wrapper at all.
   - `{:lam, dom, body}` → `body` **only if `body` does not contain `{:var, 0}`**
     (a reference to the lambda's own parameter, which would become dangling/
     silently-wrong once hoisted above the binder); when eligible, the candidate
     is `Cure.Core.Term.shift(body, -1, 0)` (positional `cutoff` argument — see
     rule 3's note on `Term.shift/3`'s actual signature; renumbering every
     reference to an outer-context variable down by one, since one enclosing
     binder is gone), not `body` verbatim. Splicing `body` in unshifted — as a
     literal "replace with an immediate sub-term" reading would do — is a de
     Bruijn bug: it would silently make `{:var, k}` (`k >= 1`) in `body` refer to
     the *wrong* outer variable (one position closer than intended) rather than
     either failing loudly or preserving meaning. This shift-then-splice is
     always safe once the `{:var, 0}`-guard passes (every remaining free index is
     `>= 1`, so shifting by `-1` with cutoff `0` never produces a negative index)
     — unlike rule 3, this candidate can never affect anything outside the
     subtree being replaced. `dom` (the domain type) is never offered as a
     replacement for the whole `:lam` (a type is not a term of the lambda's own
     type, so `pred` would reject it anyway, but it's excluded from the candidate
     set for clarity).
   The generic, provenance-free form of "peel a wrapper" — it undoes A's `deepen`
   layers and B's carriers without knowing they exist.

**Search discipline.** Deterministic enumeration, fully pinned down (needed for the
determinism guarantee in §5 and the §7.1 test): a **sweep** walks payload fields in
the fixed order **`ctx` (index `0..length-1`, outermost-in-the-list-sense i.e.
literal list order) → `type` → `term`**; within each field, positions are visited
pre-order (a node before its children, left-to-right among children); at each
position, rules are tried in the order given above (1 → 2 → 3 → 4), and rule 1's
menu items are tried in the fixed order listed in rule 1. Greedy: apply the
**first** accepted candidate found by this walk, then restart the sweep from the
top of `ctx[0]`. **Fixpoint** when a full sweep accepts nothing, or the step budget
is hit. Each accepted step strictly decreases `size` (§5 — including rule 1, now
that it only fires on `> 1`-node positions), so termination is guaranteed
independent of the budget; the budget only caps *cost*.

**Acceptance gate for a candidate `k`:** `Runner.well_formed?(k)` AND (rescue
`pred.(k)` → `false` on exception) AND `pred.(k)`. First candidate passing is taken.

---

## 5. Size measure & guarantees

`size(artifact) = term_node_count(term) + length(ctx) + sum_of_numeral_magnitudes(term)`.

- **Monotone:** every accepted edit strictly decreases `size` (rule 1, gated to
  `> 1`-node positions, strictly lowers `term_node_count`; rule 2 lowers a numeral
  magnitude by exactly one; rule 3 lowers `length(ctx)` by exactly one; rule 4
  replaces a compound with a strictly-smaller immediate sub-term). Asserted in
  tests.
- **Idempotent fixpoint:** re-`minimize`-ing an already-minimal artifact (same
  `pred`) is a no-op. Asserted.
- **Deterministic:** same `(artifact, pred, budget)` ⇒ same output (fixed
  enumeration; no clock, no RNG). Asserted — this is what makes minimized antibodies
  reproducible.

---

## 6. Runner integration

At the infection branch (`runner.ex:28`), before writing the report/banking, build
the predicate from the **same dispatch the Runner already uses** and minimize:

```elixir
{:violation, orig_detail} = v ->
  assay = opts[:assay] || assay_module(c.assay)
  # `same_shape?/2` compares only the VIOLATION TAG (the discriminating atom in
  # the second tuple element, e.g. `:not_idempotent`, `:infer_failed`,
  # `:accepted_ill_typed`) — never the payload (term/detail), which is expected
  # to change as the artifact shrinks. A bare `match?({:violation, _}, ...)`
  # would also accept an UNRELATED violation the edit stumbled into (e.g. an
  # ill-typed nonsense candidate for `Antigen.Assays.Term`, whose own
  # `{:violation, {:infer_failed, e}}` on infer-failure is itself a violation
  # shape — see §2) and silently destroy the original bug being minimized.
  pred = fn ch ->
    case apply(assay, :run, [ch]) do
      {:violation, detail} -> same_shape?(detail, orig_detail)
      _ -> false
    end
  end
  c_min = Antigen.Shrink.minimize(c, pred, shrink_budget(opts))
  {:ok, path} = Report.write_infection(opts[:report_dir], c_min, v, summarize(acc, count))
  IO.puts(Report.breadcrumb(c_min, path))
  Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))
  %{acc | infections: acc.infections + 1}
```

```elixir
defp same_shape?(d1, d2) when is_tuple(d1) and is_tuple(d2), do: elem(d1, 0) == elem(d2, 0)
defp same_shape?(d1, d2), do: d1 == d2
```

For a tuple detail, `same_shape?/2` compares only the leading tag (e.g.
`:not_idempotent`, `:infer_failed`, `:accepted_ill_typed`, `:wrongly_rejected`,
`:wrongly_accepted`) — never the full tuple, which embeds the term/fault/reason
and is expected to change every shrink step. Every assay in the registry
(`runner.ex:291-302`) except one returns a tagged tuple as its violation detail
(`assays/term.ex`, `assays/mutation.ex`, `assays/totality.ex`,
`assays/positivity.ex`, `assays/reflexivity.ex`, `assays/indexed.ex`,
`assays/rewrite.ex`, `assays/universes.ex`); the exception is
`Antigen.Assays.Stub.run/1` (`assays/stub.ex:4`), whose sole violation detail is
the bare atom `:boom` — a plain `elem(detail, 0)` comparator would raise
`ArgumentError` on it (`elem/2` requires a tuple), so the fallback clause above
(plain equality) is required, not optional.

- Reusing `opts[:assay] || assay_module(c.assay)` means the predicate carries any
  **injected assay/infer override** verbatim — which is exactly the seam the
  end-to-end test (§7.5) uses to manufacture a buggy `infer`.
- `shrink_budget(opts)` reads `opts[:shrink_budget]`, default `@shrink_budget` (e.g.
  `2000` steps). Budget exhaustion banks best-so-far (still a valid antibody) — never
  a non-violating artifact (§3 precondition holds throughout).
- The report and the banked antibody both use `c_min`.
- **Cost in normal runs is ~zero** — the branch only runs on an infection, of which
  there are currently none.

---

## 7. Testing (TDD; artifact is executable code)

**Discipline (non-negotiable, applies to every test below):** write each test
first against the not-yet-existing behavior, watch it fail (red) for the reason
the test describes (not a compile error), then write only enough of `minimize/3`
/ the rule generators / `size/1` / the Runner change to make it pass (green), then
refactor with the suite staying green. Build in roughly the numbered order below
— each test's minimal implementation is a prerequisite for the next (1–2 need
only the sweep skeleton + `size/1`; 3 needs rule 3's/rule 4's de Bruijn handling;
4 needs the full rule set wired into `minimize/3`; 5 needs the Runner integration
of §6; 6–7 are regression/bound checks over the finished piece). Once a test
correctly encodes the intended behavior it is immutable: a red test goes green by
fixing `Antigen.Shrink`/`Antigen.Runner`, never by loosening or deleting the test
— the sole exception is discovering the test itself encodes the wrong behavior,
which must be argued explicitly before touching it. Every test asserts on
`minimize/3`'s or `Runner.explore/1`'s observable inputs/outputs (the returned
`Challenge`, the corpus/report files it writes) — never on which private rule
function fired or how many times, so the tests survive an internal refactor of
the rule set.

1. **Determinism** — same `(artifact, pred, budget)` ⇒ identical minimized output.
2. **Monotone + idempotent** — `size(minimize(a)) ≤ size(a)`; `minimize(minimize(a)) ==
   minimize(a)`.
3. **De-Bruijn closure (per-rule property)** — over sampled terms, every candidate a
   rule proposes is de-Bruijn-closed w.r.t. its ctx, with particular attention to
   rule 3's cross-ctx-entry shift (§4: the asymmetric before/after-drop-position
   handling) and rule 4's `:lam`-body shift-and-reject-on-`{:var,0}` guard (§4); no
   rule ever introduces an out-of-scope `{:var,_}`.
4. **Synthetic-predicate machinery** — take a deep well-typed term (from
   `Term.gen_term`) and shrink under `pred = fn ch -> infer_ok?(ch) and contains?(ch,
   :vcons) end`; assert the result is minimal (a single `vcons` at minimal-atom args,
   empty/relevant ctx) and still satisfies `pred`. Tests the rewriter + de Bruijn
   handling without any real assay.
5. **Buggy-infer end-to-end** — inject (via `opts[:assay]`) an assay wrapper that
   runs `Assays.Mutation.run(c, buggy_infer)` where `buggy_infer` wrongly ACCEPTS the
   `:head_swap` family. Grow a deep `:mutant_term` carrying a `head_swap` fault (wrap
   with `Mutation.deepen` + a padded ctx). Run the Runner infection→shrink→bank path;
   assert the banked antibody's **term/ctx** are structurally bare (no `deepen`
   wrappers, no dead ctx entries) and that it still trips the buggy assay. Assert on
   `payload.term`/`payload.ctx` only — NOT on `fault.depth`/`wrap_path`, which are
   kept verbatim as injection provenance (§9) and may not match the minimized term.
6. **Budget bound** — with `budget: 1`, `minimize` performs at most one accepted edit
   and returns a valid (still-violating) artifact; the run terminates.
7. **Backward compatibility** — full suite green; with 0 organic infections the
   Runner change is inert on every existing corpus; banked seeds unchanged.

---

## 8. Architecture & constraints

- `lib/antigen/shrink.ex` (`minimize/3`, the 4 rule generators, `size/1`, and a
  free-de-Bruijn-index occurs-check — `Cure.Core.Term` provides `shift/3` and
  `subst/3` but no "does `{:var, k}` occur free" predicate; rule 3's drop-
  rejection test and rule 4's `{:var, 0}`-in-`body` guard both need one.
  `Antigen.Runner` has a private, Runner-scoped `occurs?/2` (`runner.ex:240-256`)
  with exactly this crosses-binders-incrementing-`k` semantics — same shape,
  reimplement in `Shrink` rather than reaching into `Runner`'s private
  functions). Reuses `Runner.well_formed?/1` (expose if private), the real
  `Cure.Core.Term.shift/3` (§4 — positional `cutoff`, not keyword), and
  `Cure.Core` term structure generally; no new kernel code.
- `lib/antigen/runner.ex` — the infection-branch change + `@shrink_budget` +
  `shrink_budget/1` + `same_shape?/2` (the violation-tag comparator §6 requires;
  a small private helper, colocated with the infection branch it serves).
- `test/antigen/shrink_test.exs`.
- **Determinism/reproducibility non-negotiable:** no clock, no RNG in `minimize`
  (mirrors the banked-seed replay contract). Step-budget only.
- **Ghost-authored commits; one full build/test run at a time; StreamData
  quarantine** (Shrink is outside `generators/`/`assays/` and uses neither backend).
- No changes to `Gen`, the assays, the challenge model, or the corpus format.

---

## 9. Non-goals (YAGNI)

- **`ChoiceSeq` / internal buffer shrinking** — deferred; this spec is the Tier-1
  gate. Reassess `ChoiceSeq` only if a real deep antibody stays visibly non-minimal
  after this.
- **Provenance-guided peeling** — the generic rule 4 subsumes undoing `deepen`/conv
  carriers without fault metadata; no separate provenance path.
- **Shrinking the `fault` provenance map** — kept verbatim; it documents the original
  injection, not the minimized term. Consequence: a shrunk mutant's `fault.depth`/
  `wrap_path`/conv indices may no longer match its (smaller) term. Accepted: `fault`
  is human-facing provenance, and banked *antibodies* (`corpus_path`) are never scored
  by the depth/wrapper metrics. Precisely: `Runner.mutation_metrics/1`
  (`runner.ex:136-157`, computing `max_depth`/`wrap_diversity` off `fault.depth`/
  `fault.wrap_path`) reads only the freshly-drawn, in-memory `challenges` list from
  the current `explore/1` call (`runner.ex:13-14`) — it never reads any file at all
  (neither `corpus_path` nor the seeds file), so it structurally cannot see `c_min`
  or anything the shrinker writes. This path never writes to that in-memory list, so
  the shrink is invisible to the metric regardless of what `fault` ends up saying. If
  a future need arises, recompute the structural fault fields post-shrink; out of
  scope for v1.
- **Multi-objective / global-optimum minimization** — greedy local fixpoint is
  sufficient for the antibody-readability goal.
- **Shrinking type-check performance** — infections are rare; a step budget bounds
  worst case. No caching of kernel calls in v1.
