# Weak-Head Normalization Before Unification (#11, pivoted) — Design Spec

**Date:** 2026-07-03
**Roadmap row:** #11 (Inference unification). **Pivoted** from "postponed/suspended
constraints" to "whnf-before-compare" after the Task-1 risk gate + a second
language cross-read proved postponement is (a) not the reachable gap and (b) not
what Idris/Agda/Lean rely on. See §7 for the empirical basis and §8 for the
supersession record.
**Layer:** E (untrusted elaborator) — `lib/cure/elab/unify.ex`. Reuses the
existing **trusted** `Cure.Core.Normalise.whnf` unchanged. **No `lib/cure/core/*`
change; no TCB.**
**References:** Idris2 `Core/Unify.idr:1300-1302` (`nf` both sides before unify);
Agda `TypeChecking/Conversion.hs:586-587` (`reduceB` both sides in `compareAtom`);
Lean4 `Meta/ExprDefEq.lean:2327-2330` (`whnfCoreAtDefEq` both sides at
`isExprDefEqAuxImpl` entry).

---

## 1. Problem & goal

Cure's unifier (`Cure.Elab.Unify`) compares **un-normalized** Core terms
structurally. When one side is a *reducible redex* — e.g. `plus(Z, ?m)`, which
δι-reduces to `?m` because `plus`'s first argument `Z` is a concrete
constructor — the unifier sees `{:app, {:app, {:global, :plus}, Z}, ?m}` versus
`{:ctor, :S, [Z]}`, finds no structural match, and **fails** with
`{:cannot_unify, …}`. Its only definitional escape, `delta_convertible?`
(unify.ex:282-299), requires **both sides metavariable-free**, so it never helps
while an unsolved `?m` is present.

Idris, Agda, and Lean all **reduce both sides to weak-head normal form *before*
structural comparison** — reduction is intrinsic to unification, not a fallback.
`plus Z m =? S Z` is solved *by reduction* in all three: `plus Z m` → `m`, then
`m := S Z`. (Postponement in those systems is a *separate* mechanism, used only
for terms genuinely stuck on an unsolved metavariable, e.g. `plus m Z`.)

**Goal.** Add weak-head normalization of both sides at the start of Cure's
unification step, so a reducible redex (even one containing an unsolved
metavariable in a non-blocking position) is reduced before structural
comparison. This reaches the dependent-inference inputs Idris accepts (computed
indices like `Vec(plus(Z, m))`).

**Non-goal for soundness.** E-layer only. The kernel re-checks every elaborated
term (`Unify.zonk/2` must yield a `{:meta,_}`-free term before handoff), so a
wrong reduction/solve is caught downstream. This mirrors the
conservative-fallthrough stance of the landed Miller solver (#10). The whnf used
is the **trusted** `Normalise.whnf`; correctness of reduction itself is already
the kernel's, unchanged.

---

## 2. Success criterion & risk gate (ALREADY PASSED)

Unlike the superseded design, the reachability gate is **already satisfied** —
two confound-free probes were constructed and verified during the pivot
(`test/oracle/postpone/` scratch, uncommitted; §5 relocates them):

- **`whnf01_computed_index`** (was candA): a monomorphic indexed family `Vec`,
  `needlen({m}, v: Vec(plus(Z,m)), r: Nat) = r`, applied to a fully-concrete
  `vs(vz()) : Vec(S(Z))`. **Verified today**: `cure=reject` with reason
  `{:index_mismatch, {:cannot_unify, plus(Z, ?0), S(Z)}}`; `idris=accept`. This
  is the primary verdict-flip probe. Confound-free: no erased-binder use (body
  returns the relevant `r`, not `m`), no polymorphic element-type metavariable
  (monomorphic family), reason is exactly the target unification failure.
- **`whnf02_two_arg_shared_index`** (was candP01): same shape with a second
  argument `v: Vec(m)` that also mentions `m`. **Verified today**:
  `cure=reject` / `idris=accept`, same `cannot_unify` reason. A second flip probe
  that also exercises cross-argument inference within one telescope.

The confound history (the reason the gate is load-bearing): the first drafts were
rejected by Cure's **erasure relevance check** (`{:erased_used_relevantly}` — a
returned implicit) and then by a stray **polymorphic-family metavariable**
(`{:unsolved_metavariables, :vnil}`). Both were eliminated before the reason
resolved to the genuine `cannot_unify`. Any future probe edit MUST re-verify the
Cure rejection reason via the throwaway-test pattern (`mix run` is unavailable —
throws `unknown registry: Cure.Pipeline.Events.Registry`) before trusting it.

---

## 3. Architecture — whnf both sides at the unify step

### 3.1 Where

`Cure.Elab.Unify.do_unify/5` (unify.ex:136) is the structural dispatch, called by
`unify_d/5` (unify.ex:101) as `do_unify(force_d(t1,…), force_d(t2,…), …)`.
`force_d` only resolves a solved-metavariable *head*; it does NOT δ-reduce. Insert
whnf **between `force_d` and structural dispatch**: reduce each side to whnf
first, and only if a side actually changed, re-enter `unify_d` on the reduced
terms (Lean's "if it reduced, recurse" loop — ExprDefEq.lean:2329-2330 — which
also gives termination: reduction is finite, and a fixpoint is reached when
neither side reduces further). If neither reduces, fall through to today's exact
structural clauses (so all current behavior is preserved on already-whnf terms).

### 3.2 Meta-aware whnf (the reuse trick)

The kernel evaluator is meta-free (`Eval.eval` has no `{:meta,_}` clause; a
meta-bearing term would crash it). To reduce a term that still contains unsolved
metavariables **without any kernel change**, reuse `Normalise`'s reduction
semantics directly through its public constituent functions — `Eval.eval/2`,
`Normalise.whnf_value/3`, `Quote.reify/2` — the same three functions `whnf/3`
itself composes (normalise.ex:26-33), rather than `whnf/3`'s own wrapper (see
§3.3 for why: `whnf/3` needs a `Core.Context.t()` the unifier cannot cleanly
build):

1. **Zonk-then-substitute-placeholders.** Zonk the term (apply known meta
   solutions). For each *remaining* unsolved `{:meta, id}`, substitute a reserved
   **opaque global** placeholder `{:global, meta_placeholder_name(id)}` where
   `meta_placeholder_name(id)` is a fresh reserved atom (e.g. `:"$meta$#{id}"`)
   guaranteed absent from the signature.
2. **Reduce.** Evaluate with `Eval.eval/2` under a hand-built env (mirroring
   `Context.env/1`'s recipe from just `depth`), then reduce to whnf with
   `Normalise.whnf_value(value, sig, delta: :certified, stuck_cases: :preserve)`,
   then read back with `Quote.reify(value, depth)` (§3.3 has the exact call
   sequence). An opaque global has no signature entry, so `unfold_head` returns
   `:stuck` (normalise.ex:59-62) and it stays a neutral — exactly how an unsolved
   metavariable behaves: it **blocks** a match/case whose scrutinee is the
   placeholder, and **passes through** in any non-scrutinee position. Thus
   `whnf(plus(Z, $meta$0))` → `$meta$0` (plus's Z-branch returns its second
   argument untouched), and `whnf(plus($meta$0, Z))` → stuck `plus($meta$0, Z)`
   (blocked on the placeholder scrutinee — the genuinely-stuck case, correctly
   left alone).
3. **Reverse-map.** Walk the reduced term mapping each `{:global,
   meta_placeholder_name(id)}` back to `{:meta, id}`.

The placeholder map is `id ⇆ name` (both directions); reserved names are
recognizable (a fixed prefix) so reverse-mapping is total and unambiguous. A
`{:global, "$meta$…"}` can never arise from real Cure source (the prefix is not a
legal identifier), so there is no collision with a user global.

**Fuel / failure.** Step 2's reduction, wrapped in `Normalise.with_fuel/2`
(normalise.ex:68-81 — the same fuel mechanism `whnf/3` uses internally, since
fuel is tracked via the process dictionary and consulted deep inside
`unfold_certified_head`/`reduce_unfolded` regardless of which entry point
drives the reduction), may report `:fuel_exhausted`. On that (or any placeholder
round-trip anomaly), the whnf step **falls back to the un-reduced term** (i.e.
behaves exactly as today — structural comparison on the original), never
crashing and never fabricating a reduction. So the change is strictly additive:
it can only turn some current `cannot_unify` failures into successes, never the
reverse (a fallback preserves the old path).

### 3.3 Interaction with the Core `Context` the reuse needs

`Normalise.whnf/3` takes a `Cure.Core.Context.t()` (for signature + de Bruijn
length + env), while `Unify.unify/4` currently threads only a `sig` (passed to
`Conv.conv?` in `delta_convertible?`) and a de Bruijn `depth`. `Context.t()`
also carries a `types :: [Value.t()]` field (one semantic type value per bound
variable) that the unifier simply does not have — its `depth` is a bare
counter, not a typed telescope. Every existing `Normalise.whnf`/`nf` call site
in the codebase (`lib/cure/core/kernel.ex`, `lib/antigen/*`, `test/cure/core/*`)
builds its `Context` via `Context.empty(env) |> Context.extend(real_type_value)`
using genuine type values from an active typechecking context — there is no
call site, and no public `Context` constructor, for "a context of a given
length with unknown types." Fabricating one from the unifier (a `Context.extend`
loop with placeholder type values, or a direct `%Context{}` struct literal) is
therefore either impossible via the public API or a bypass of it.

The resolving fact: `types` is **read by nothing** on the `whnf` path.
`Normalise.whnf/3`'s body (normalise.ex:26-33) calls `Context.signature/1`
directly, `Context.length/1` directly (passed to `Quote.reify`), and
`Context.env/1` indirectly (via its own private `eval_in/2`, which is just
`Eval.eval(term, Context.env(ctx))`) — never `Context.lookup/2`, the only
consumer of `.types`. So the unifier does **not** need to construct a
`Context.t()` at all: it calls the same public functions `whnf/3`'s body calls,
directly, with a hand-built env in place of `Context.env(ctx)`:

1. `env = for level <- (depth - 1)..0//-1, do: {:vneutral, {:nvar, level}}`
   (exactly `Context.env/1`'s recipe, needing only `depth`, not a `Context`).
2. `value = Eval.eval(subst_term, env)` (the public function `Normalise`'s
   private `eval_in/2` merely wraps — `eval_in` is `defp` and NOT reachable
   from `Unify`).
3. `reduced_value = Normalise.whnf_value(value, sig, delta: :certified,
   stuck_cases: :preserve)`.
4. `reduced_term = Quote.reify(reduced_value, depth)`.

This is the ONLY path the plan should pin: it needs no `Context.t()`, uses only
public functions, and runs at the **same de Bruijn depth** the two terms were
forced at (the `depth` argument already threaded through `unify_d`), so
bound-variable levels line up.

### 3.4 What this fixes and does not

- **Fixes:** any unification where a reducible redex (concrete-enough to reduce,
  possibly carrying an unsolved meta in a passed-through position) was compared
  un-reduced — `whnf01`, `whnf02`, and the general computed-index inference class.
- **Does NOT fix (correctly rejects):** a term genuinely **stuck** on an unsolved
  metavariable in a *scrutinee/blocking* position (`plus(?m, Z) =? S(Z)` — cannot
  reduce until `?m` is known, and nothing here determines `?m`). Both Cure and
  Idris reject this (Idris: unsolved metas; Cure: `cannot_unify` on the stuck
  neutral). This is the `whnf03` negative (§5). Handling it would need the
  *separate, deferred* postponement mechanism (§6).

---

## 4. Data & control-flow summary

- `unify/4` public contract **unchanged**: `{:ok, ctx} | {:error, reason}`.
- New internal surface in `Cure.Elab.Unify`: `whnf_meta_aware(term, meta_ctx,
  sig, depth \\ 0, opts \\ [])` (`@doc false`/public, not `defp` — see §3.3; the
  placeholder wrap around `Eval.eval`/`Normalise.whnf_value`/`Quote.reify`, the
  same reduction semantics `Normalise.whnf/3` composes) and a reduction step in
  `unify_d` (or a new `reduce_then_unify`) that whnfs both sides and recurses on
  change.
- No new `MetaCtx` field, no constraint queue, no `occurs?` change. `occurs?`
  stays exactly as today (the occurs cases are not reachable-to-flip — §7).
- No elaborator call-site change beyond `unify.ex` internals (the fix is entirely
  inside the unification step; `finish_ctor_app`/`finish_global_app` are
  untouched).

---

## 5. Oracle probes (`test/oracle/whnf/`)

Relocated + finalized from the pivot scratch. Faithful paired transliterations
(`.cure` + `.idr` with `%default total`, no `module` line); verdicts from
`mix cure.oracle whnf`, never hand-written; frozen into `verdicts.json`; replayed
by `test/oracle_replay_test.exs` (which auto-discovers the dir).

1. **`whnf01_computed_index`** — (accept/accept after fix; pre-fix reject/accept).
   *Primary verdict-flip.* `needlen({m}, v: Vec(plus(Z,m)), r) = r`, `use =
   needlen(vs(vz()), Z())`. Cure must reduce `plus(Z,?m)` → `?m` to solve
   `?m := S(Z)`.
2. **`whnf02_two_arg_shared_index`** — (accept/accept after fix; pre-fix
   reject/accept). Adds `v: Vec(m)`; exercises the same reduction plus
   cross-argument index sharing in one telescope.
3. **`whnf03_stuck_meta_neg`** — (reject/reject, before AND after fix).
   `stuck({m}, v: Vec(plus(m, Z)), r) = r`, `use = stuck(vs(vz()), Z())`.
   `plus(m, Z)` is stuck on `?m` (first arg is the meta) — irreducible; nothing
   determines `?m`. Both reject. Guards that the whnf change does **not**
   over-accept a genuinely-stuck term (it must not "reduce" `plus(?m,Z)` to
   anything, and must not fabricate a solution). Confirm the Cure reason is the
   stuck-`cannot_unify`/unsolved-meta, and the Idris reason is unsolved metas.
4. **`whnf04_concrete_mismatch_neg`** — (reject/reject). A genuinely unequal
   pair after reduction (`Vec(plus(Z, Z)) =? Vec(S(Z))`, i.e. `Z =? S(Z)`). Both
   reject. Guards that whnf-then-compare still **rejects real mismatches** (the
   reduction succeeds but the reduced forms genuinely differ) — i.e. the change
   didn't weaken disequality.

Each probe's pre-fix Cure verdict + reason is verified via the throwaway test
before freezing; if a probe's intended pre-fix divergence cannot be reproduced,
it is not frozen and the discrepancy is investigated first (triage contract).

---

## 6. Deferred: postponement (the superseded design, now secondary)

The postponement queue is the *correct* mechanism for the genuinely-stuck case
(`whnf03`: `plus(?m, Z)` becomes solvable if some *other* constraint later pins
`?m`). But: (a) no surface-Cure probe reaches a *verdict flip* through it that
whnf doesn't already handle — the stuck cases stay unsolved either way at the
telescope granularity available today; and (b) all three reference systems treat
it as strictly secondary to reduction. It is therefore **deferred**, kept as a
roadmap follow-up, to be revived only when a probe genuinely needs it (a
cross-constraint stuck-then-pinned case reachable from surface syntax).

## 7. Empirical basis (why whnf, not postponement)

- **Risk-gate finding.** The reachable, confound-free divergence (`whnf01`) is
  `plus(Z, ?m) =? S(Z)` failing for lack of reduction — no metavariable occurs on
  both sides (not occurs), neither side is metavariable-headed (not flex-flex).
  The superseded design's two triggers (flex-flex, weak-rigid occurs) flip
  **nothing**: bare `?a =? ?b` already solves eagerly (unify.ex:240), and surface
  weak-rigid occurs (`?m =? plus(Z,?m)`) is only fixable by *reducing* the
  eliminable away — postponing it just re-fails on retry.
- **Language cross-read (unanimous).** Idris `nf` both sides before `unify`
  (Unify.idr:1300-1302); Agda `reduceB` both sides in `compareAtom`
  (Conversion.hs:586-587); Lean `whnfCoreAtDefEq` both sides at `isDefEq` entry
  (ExprDefEq.lean:2327-2330). All three: reduction is the intrinsic primary
  mechanism; `plus Z m` is handled by reduction; postponement is separate and
  secondary (Idris `postpone`/`retry` Unify.idr:211-234/1373-1402; Agda
  `catchConstraint`/`Blocker` Constraints.hs:283-284; Lean `unstuckMVar`/
  `getStuckMVar?` ExprDefEq.lean:1983-2018).

## 8. Supersession record

This spec supersedes `2026-07-03-postponed-constraints-design.md` (committed
`dfc680c`) and its plan `2026-07-03-postponed-constraints-plan.md` (`2841d6a`).
Those remain in history as the postponement design; a one-line superseded banner
is added to each pointing here. The pivot was operator-approved after the Task-1
gate + language research (this session).

## 9. Definition of done

- All four `whnf` oracle probes at intended verdicts; frozen; replay green.
- `whnf01`/`whnf02` flip reject→accept; `whnf03`/`whnf04` stay reject/reject
  (no over-acceptance).
- Unit tests for the meta-aware whnf helper (placeholder round-trip; reduces
  `plus(Z,?m)`→`?m`; leaves `plus(?m,Z)` stuck; falls back on `:fuel_exhausted`).
- Full `mix test` green (run once, alone).
- Roadmap §2 row #11 updated: whnf-before-compare landed (probes named,
  postponement deferred), no-TCB / kernel-backstop note.
- No `lib/cure/core/*` diff (`git diff --stat` touches only `lib/cure/elab/*`,
  `test/**`, `docs/**`).
