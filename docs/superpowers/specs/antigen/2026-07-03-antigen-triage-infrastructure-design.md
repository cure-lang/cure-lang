# Antigen Triage Infrastructure — Shrink-all-kinds + auto-bisect (Run D)

**Status:** design approved (single autopilot gate) · **Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03

## 1. Problem

When Antigen finds an **infection** (a kernel soundness violation), the operator
needs the *smallest* artifact that still triggers it — noise removed — to
diagnose the kernel bug. Today's triage is partial:

- `Antigen.Shrink.minimize/3` is a solid value-level greedy shrinker (term
  rewrites + de Bruijn ctx-drop), but `Runner.explore/1` wires it up **only** for
  `:typed_term` / `:mutant_term`. Every other infection kind (`:stub`, `:family`,
  `:indexed_case`, `:rewrite_eq`, `:forcing_pair`, `:stuck_elim`, `:def_group`,
  `:elab_program`) is banked **un-minimized** — the operator triages a bloated
  artifact by hand.
- There is **no structural delta-debugging** at all. An infection carried by a
  `:def_group` of four definitions, or a `:family` with three constructors, is
  banked whole even when a single definition or constructor is the culprit.

Run D closes both gaps with a single triage pass that runs for **every** kind.

## 2. Goal

Every banked infection is minimized to a joint fixpoint of two reductions,
under the **same** violation-shape predicate the runner already computes:

1. **Shrink-all-kinds** — the existing term-rewrite engine applied to the Term
   content of *every* challenge kind (not just the two hand-wired payloads).
2. **Auto-bisect** — ddmin-style removal of whole **name-referenced** list
   elements (definitions, constructors, families, focus entries) down to the
   minimal sub-structure that still triggers the same violation.

Both are orchestrated by a new `Antigen.Triage.minimize/3`, which `Runner`
calls for all kinds, and the infection report gains a triage summary line.

## 3. Non-goals

- **git-bisect over kernel commits.** The operator explicitly chose in-challenge
  ddmin over commit-history bisection. No TCB rebuilds, no git, no reproducer
  runner. (Documented as a possible future run, not this one.)
- **Elaborator string-level shrink.** `:elab_program` payloads carry only
  surface-program **strings** (no Core `Term` pieces, no list-structured
  scaffold to bisect). Triage is a **no-op** for `:elab_program` — it passes
  through unchanged. Shrinking surface source text is a documented follow-on.
- **The ddmin granularity ladder** (Zeller's halving schedule). Our list
  components are tiny (a handful of elements); greedy 1-minimal element removal
  to fixpoint is sufficient and matches the existing shrink sweep. The ladder is
  a documented follow-on for large inputs.
- **No `Cure.Core.*` (TCB) edits.** All kernel calls stay read-only via the
  assay `run/1` the predicate invokes.
- **No new dependency, no `:meck`.**

## 4. The pieces bridge (the enabling seam)

`Antigen.Challenge.to_pieces/1` already decomposes **every** kind into
`{scaffold, [{piece_id, Term}]}`, and `Challenge.from_pieces/7` rebuilds the
challenge losslessly (it is the corpus codec — round-trip is already relied on
by the seed/antibody banking). Run D rides this existing bridge instead of
reaching into kind-specific payload keys:

- **Shrink** enumerates candidates by rewriting each Term **piece** and calling
  `from_pieces/7` to rebuild — kind-agnostic by construction.
- **Bisect** removes whole elements from the **scaffold**'s list-structured,
  **name-referenced** components and rebuilds via `from_pieces/7`.

`from_pieces/7` signature (already public):
`from_pieces(kind, assay, label, seed, note, scaffold, pieces) :: Challenge.t()`.

The bridge is why "all kinds" costs almost no new per-kind code.

## 5. Component 1 — Shrink-all-kinds (`Antigen.Shrink`, generalized)

### 5.1 What changes

`Shrink`'s **rewrite engine** (`term_candidates/1` → `rule1`/`rule2`/`rule4` +
`child_slots/1`) is already kind-agnostic — it rewrites a bare Core `Term`. Only
`candidates/1` is kind-specific (it dereferences `payload.ctx/type/term`). We
re-seat candidate enumeration on the pieces bridge:

```
piece_candidates(ch):
  {scaffold, pieces} = Challenge.to_pieces(ch)
  for each {pid, term} in pieces, for each term' in term_candidates(term):
     rebuild ch with that one piece replaced by term', via from_pieces/7
```

The existing **de Bruijn ctx-drop** (`ctx_candidates/1` — the one
position-referenced/reindexing reduction, with `Term.shift`) is retained
**verbatim** and applies only to kinds that carry a de Bruijn `ctx` telescope
(`:typed_term`, `:mutant_term`). It is *not* generalized to other kinds:
def-groups/families reference their members by **name** (`{:global, …}`),
handled by bisect (Component 2), not by index shifting.

### 5.2 Order and invariants (unchanged from today)

- **Greedy, deterministic:** fixed enumeration order (ctx-drop → per-piece
  rewrites, pieces in `to_pieces` order, pre-order within a term). No RNG/clock.
- **Monotone:** a candidate is accepted only if it is well-formed **and** the
  predicate holds. Size never increases because every rewrite/drop is a
  reduction (`rule1` compound→atom, `rule2` `S^k→S^(k-1)`, `rule4` unwrap,
  ctx-drop removes a binder). See §7 for the generalized `size/1` gate.
- **Budget-bounded:** budget counts predicate calls; a shape-invalid candidate
  spends no budget (existing `well_formed?` pre-filter).
- **`safe_pred`:** a predicate that raises/throws is treated as `false`.

### 5.3 Kind coverage after generalization

| kind | shrink coverage |
|---|---|
| `:typed_term`, `:mutant_term` | term rewrites **+ ctx-drop** (as today) |
| `:family` | rewrites on param/index/ctor-arg/result-index/result-param Term pieces |
| `:indexed_case`, `:rewrite_eq` | rewrites on family pieces + `def_type` + `def_body` |
| `:forcing_pair`, `:stuck_elim` | rewrites on each def's type/body + `t` + `tprime` |
| `:def_group` | rewrites on each def's type/body |
| `:stub` | rewrites on the single `term` piece |
| `:elab_program` | **no-op** (no Term pieces — §3) |

## 6. Component 2 — Auto-bisect (`Antigen.Bisect`, new)

### 6.1 Targets: name-referenced list components

ddmin removes **whole elements** from list-structured scaffold components whose
members are referenced by **name**, so removal is a pure list edit (no de Bruijn
reindexing):

| kind | bisectable lists |
|---|---|
| `:def_group`, `:forcing_pair`, `:stuck_elim` | `defs` (each carries a `focus`-cleanup obligation, §6.3) |
| `:family` | `ctors` |
| `:indexed_case`, `:rewrite_eq` | `families` |
| `:typed_term`, `:mutant_term`, `:stub`, `:elab_program` | none (bisect no-op) |

`ctx` is **not** a bisect target — it is position-referenced and handled by
shrink's ctx-drop (§5.1).

### 6.2 Algorithm: greedy 1-minimal element removal

For each bisectable list, in a fixed order, attempt to drop each element (fixed
index order). A drop candidate:

1. removes element `i` from the list;
2. prunes any now-dangling **focus** entry naming a removed def (§6.3);
3. rebuilds the challenge via `from_pieces/7` (through a `drop_*` helper that
   edits the `{scaffold, pieces}` pair, so no kind-specific payload handling
   leaks in);
4. is **accepted** iff the rebuilt challenge is `well_formed?` **and** the
   predicate (called through the same `safe_pred` wrapper Shrink uses — a
   raise/throw counts as `false`) holds (same violation shape).

On acceptance, restart the sweep on the smaller challenge (greedy); on a full
pass with no acceptance, that list is 1-minimal. Budget counts predicate calls,
shared with shrink.

**Safety is the predicate, not static analysis.** Dropping a def that another
surviving def references by `{:global, name}` yields either a malformed
challenge (rejected by `well_formed?`), a crash in the assay itself (e.g. δ-unfolding
a now-missing global — caught by `safe_pred`, rejected), or a different violation
(rejected by the same-shape predicate). No dependency/reachability analysis is
written — the oracle decides. This mirrors how shrink already trusts the predicate.

### 6.3 Focus cleanup (the one structural obligation)

`:def_group` / `:forcing_pair` / `:stuck_elim` carry a `focus :: [atom]` naming
the certified-total members. Dropping def `d` MUST also drop `d`'s name from
`focus` in the same candidate — otherwise the assay/generator code that
consumes `focus` against the rebuilt `Env` (built only from `defs`) breaks:
`Antigen.Assays.Totality.certifies?/2`, `Antigen.Assays.StuckElimDelta.certified_env_of/1`,
and `Antigen.Generators.Forcing.certified_env_of/1` all call `Env.get_def(env, name)`
for each `focus` name, which returns `nil` for a name no longer in `defs` and
crashes on the following field access. (`from_pieces`'s `rebuild_defs` itself
does no such lookup — it decodes `focus` names independently of `defs` — so the
crash is not there; it is in the predicate's assay call, caught by `safe_pred`
and turned into a rejection. Without cleanup, every attempt to drop a focused
def would therefore be silently rejected as if unsafe, even when it is not.)
The drop helper removes the name from both `defs` and `focus` atomically.

### 6.4 What bisect does NOT reindex

Because targets are name-referenced, element removal never shifts de Bruijn
indices. (A def body referencing another def uses `{:global, :name}`, not
`{:var, k}`.) This is the invariant that keeps bisect a pure list edit and is
asserted by a test that a surviving def's body Term is byte-identical after an
unrelated sibling is dropped.

## 7. Component 3 — `Antigen.Triage` (orchestrator)

### 7.1 API

```elixir
@spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer())
      :: {Challenge.t(), stats}
@type stats :: %{orig_size: non_neg_integer(), min_size: non_neg_integer(),
                 bisect_drops: non_neg_integer(), shrink_rewrites: non_neg_integer()}
```

`minimize/3` interleaves the two reductions to a **combined fixpoint** under one
shared step-budget:

```
loop:
  bisect one accepted element-drop?  → count it, restart loop
  else shrink one accepted rewrite/ctx-drop? → count it, restart loop
  else → fixpoint; return {ch_min, stats}
budget (predicate calls) exhausted at any point → return current best + stats
```

Bisect is tried first each round (structural cuts shrink the term set that
shrink then walks). Determinism, monotonicity (§7.2), `safe_pred`, and
`well_formed?` are inherited unchanged.

**Interleaving is one accepted step at a time, not two nested fixpoints.**
`Shrink.minimize/3` runs shrink to its *own* local fixpoint before returning —
calling it wholesale from inside Triage's loop would let shrink fully converge
before bisect ever got a second try, breaking the "bisect first each round"
order above. `Triage.minimize/3` therefore does not call `Shrink.minimize/3`;
it drives a single shared `first_accepted`-style step over
`bisect_candidates(ch) ++ shrink_candidates(ch)` (bisect's candidates first,
matching Component 2 §6.2; shrink's candidates via the same enumeration
`Shrink.candidates/1` already produces), accepting the first well-formed,
`safe_pred`-guarded, predicate-satisfying candidate and restarting from the
top of the combined list on every acceptance. `Shrink`'s existing
reseed-after-accept convention (`seed: :erlang.phash2({kind, payload})`,
currently private to `Shrink.sweep/3`) is reused on every Triage-accepted step
too — bisect drops included — so `c_min.seed` reflects the minimized payload
the same way it does for today's `:typed_term`/`:mutant_term` shrink-only path.

### 7.2 Generalized `size/1` (the monotonicity gate)

`Shrink.size/1` today reads `payload.term`/`payload.ctx` — kind-specific. Triage
uses a kind-agnostic measure over the pieces bridge so **both** reductions share
one monotone yardstick:

```
size(ch) = Σ_pieces (node_count(term) + numeral_magnitude(term))
         + list_elements(ch)          # |ctx|+|defs|+|ctors|+|families|+|focus|
```

`node_count`/`numeral_magnitude` already exist in `Shrink`. `list_elements`
counts the scaffold's list-structured components **that exist for that kind**
— `ctx`/`defs`/`ctors`/`families`/`focus` are read defensively (absent ⇒ 0
contribution), since no kind carries all five (e.g. `:family` has `ctors` but
no `defs`/`focus`/`ctx`, and `:elab_program` has none of the five — its
`list_elements` is always 0, consistent with the shrink/bisect no-op). Every
shrink rewrite strictly
lowers the first sum; every bisect drop strictly lowers `list_elements`. A
candidate is accepted only if `size(candidate) < size(current)`, so the joint
process is monotone and terminates independent of the budget. The generalized
`size/1` is a **new** `Antigen.Triage.size/1`; the existing `Shrink.size/1` is
left **untouched** for the typed/mutant callers it already serves. The two are
deliberately *not* equal — `Triage.size` also counts `type` and ctx-entry nodes
(every piece), while `Shrink.size` scores only `term` + `|ctx|` + term-magnitude.
Each gates only its own module, so no cross-module parity is required. What is
required and tested: `Triage.size` **strictly decreases** on every accepted
reduction (a per-kind monotonicity row — one shrink rewrite and one bisect drop
each lower it by ≥1).

### 7.3 Runner wiring

`Runner.explore/1`'s infection branch (`runner.ex:66-72`) currently reads:

```elixir
c_min = if c.kind in [:typed_term, :mutant_term],
          do: Antigen.Shrink.minimize(c, pred, shrink_budget(opts)), else: c
```

It becomes, for **all** kinds:

```elixir
{c_min, triage} = Antigen.Triage.minimize(c, pred, shrink_budget(opts))
```

`triage` (the stats map) is merged into the health map passed to
`Report.write_infection` under a `:triage` key. `pred`, `shrink_budget/1`, and
`same_shape?/2` are reused verbatim.

### 7.4 Report line

`Report.render/3` gains a `triage:` line when the health map carries `:triage`:

```
triage:     size 27→9 · bisect −2 elems · shrink −11 rewrites
```

Absent `:triage` (e.g. legacy callers), the line is omitted — no signature
change to `write_infection/4` or `breadcrumb/2`.

## 8. Files

**New**
- `lib/antigen/triage.ex` — orchestrator + generalized `size/1`.
- `lib/antigen/bisect.ex` — name-referenced element ddmin + focus cleanup.

Both are siblings of `lib/antigen/shrink.ex`, **outside** the
`lib/antigen/{generators,assays}/**` StreamData-quarantine glob enforced by
`test/antigen/architecture_test.exs`. Neither references StreamData.

**Modified**
- `lib/antigen/shrink.ex` — `candidates/1` re-seated on `to_pieces`/`from_pieces`
  (per-piece rewrites); ctx-drop retained for de-Bruijn kinds; `term_candidates`
  and the rewrite rules unchanged. `candidates/1` and `reseed/1` (currently
  `defp`) become module-visible (`@doc false` or similar, not part of the
  public step-fixpoint API) so `Antigen.Triage` can drive its own one-step-at-a-time
  loop over them per §7.1, instead of calling the fixpoint-running `minimize/3`.
- `lib/antigen/runner.ex` — infection branch calls `Triage.minimize/3` for all
  kinds; merges `:triage` stats into the health map.
- `lib/antigen/report.ex` — `render/3` emits the optional `triage:` line.

**Tests**
- `test/antigen/bisect_test.exs` — element removal, focus cleanup, name-ref
  no-reindex invariant, predicate-guarded unsafe-drop rejection.
- `test/antigen/triage_test.exs` — combined fixpoint, budget bound, determinism,
  monotonicity, `safe_pred`, elab no-op, generalized `size/1`.
- `test/antigen/shrink_test.exs` — extended with per-kind minimization rows
  (family/indexed_case/forcing_pair/def_group). The `Triage.size/1`
  strict-monotonicity rows live in `triage_test.exs` (§7.2).

## 9. Testing strategy (TDD, red→green per task)

Each behavior gets a failing test first. Predicates in tests are **synthetic**
same-violation-shape closures (a small property the bloated artifact satisfies
and the minimal one still satisfies), so tests exercise the reduction machinery
deterministically without needing a real kernel bug. Tests are **immutable**
once written: green is reached by changing `Triage`/`Bisect`/`Shrink` code,
never by weakening, skipping, or deleting a test — the sole exception is a
test proven to encode incorrect behavior, and that must be argued explicitly
before the test itself is touched. Representative rows:

- **Shrink-all-kinds:** a `:family` whose infection is carried by one bloated
  ctor arg minimizes (arg rewritten to a minimal atom) while the family stays
  well-formed and the synthetic predicate still holds.
- **Bisect def_group:** `{f,g,h,k}`, `focus=[f]`, predicate = "an `f`-def whose
  body mentions `h` exists" → drops `g`,`k`, keeps `{f,h}`, `focus=[f]`; a
  predicate depending on `g` blocks `g`'s drop.
- **Focus cleanup:** dropping a focused def removes it from `focus`; the rebuilt
  challenge round-trips through `from_pieces`.
- **No-reindex invariant:** a surviving def's body Term is `==` before/after an
  unrelated sibling drop.
- **Triage fixpoint:** a challenge bloated in *both* dimensions minimizes in
  bisect **and** shrink; `stats` reports both counts; `orig_size > min_size`.
- **Budget / determinism / monotonicity / safe_pred / elab no-op:** as §5.2/§7.
- **Runner integration:** an injected non-`typed_term` infection is banked
  minimized end-to-end (guard removal exercised); health map carries `:triage`.

## 10. Invariants (summary — every reduction preserves these)

1. **Sound:** the minimized artifact still triggers the *same-shape* violation
   (predicate-checked every step).
2. **Well-formed:** every accepted candidate passes `well_formed?`.
3. **Monotone:** `size(min) ≤ size(orig)`; strictly decreases on each accepted
   step (§7.2).
4. **Deterministic:** fixed enumeration, no RNG/clock; same input → same output.
5. **Budget-bounded:** predicate calls ≤ budget; partial progress is safe to
   return.
6. **TCB-inert:** no `Cure.Core.*` edits; kernel reached only read-only through
   the assay the predicate calls.

## 11. Follow-ons (documented, out of scope)

- git-bisect over kernel commits (the declined fork).
- Elaborator surface-string shrink (`:elab_program`).
- ddmin granularity ladder for large list components.
- A `mix antigen.triage <corpus-entry>` re-minimizer for already-banked records.
