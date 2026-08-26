# Core soundness sweep complete — Eq cluster now settled; remaining items need a direction call

**Date:** 2026-07-08 (updated) · **Branch:** `feature/idris-parity` · **Gate:** `mix test` green (3083 passed)

> **RECONCILIATION NOTE (2026-07-08, later).** The "Decision needed" section near the
> end of this doc floated three options and defaulted to **option 1 — proceed with the
> representation reshapes (grade wave, K6→Eq Phase B/C, K7, K12-Sym) as non-design-gated
> Core cleanup.** That default was **NOT executed and is superseded.** On per-item
> analysis (the cron's analysis discipline) each reshape's *soundness* content was
> landed while its *representation/cleanliness* content was **declined with recorded
> proof** — because the soundness those reshapes would nominally buy is already
> delivered elsewhere: K12-Sym collision-freeness by the E-layer Resolution (LOCKED
> Approach B; audit K12 slice 4), universe soundness by predicative stratification
> (K7), {0,ω} erasure by the relevance check (grade wave). Eq Phase B was likewise
> declined (empirical parity regressions). The authoritative terminal state is now
> **spec §J.1** (per-clause table) and **GAP-DESIGN-GATE.md** (deferred features). Read
> those, not the option list below, for current status.

The unattended Core-cleanup cron has assessed **every** audit K-item AND, since the
first sweep, landed the previously-blocked Eq/identity cluster. This is the updated
consolidated status and the one direction call that needs you.

## Bottom line

**The Core is soundness-clean and the Eq/identity cluster is now resolved.** Every
genuine soundness/boundary tightening the audit called for is landed and gated.
Nothing landable-unattended remains: every open item is either **out of scope**
(QTT multiplicities/linear), an **expressiveness feature** (needs design approval),
or a **resolution-strategy design decision** you've reserved.

## What landed since the first sweep (the Eq/identity cluster — was the main open item)

| Item | Commit | What |
|------|--------|------|
| K6 545/599 | `b355753` | `infer({:ctor})` reads params riding the spine (§E.1) — param-bearing ctors inferable; additive, no fixture churn |
| Eq bridge | `f3b0e73` | `bridge_step` builds inductive `refl` via param-in-spine — **last** primitive `{:refl}` producer retired |
| K1a ratchet | `0e75a13` | split `no_eq_node`; primitive `{:eq}`/`{:refl}` → `:reject` in `release_config`, enforced on every program's final Core |
| K1 Phase B | `07f36f6` | **declined with empirical proof** — retiring the sound `{:rewrite}` node for `:case` buys no soundness and *risks* parity (frp01 computed-endpoint drift; rw03 no-occurrence more-permissive; std/proof bridge regression). Surface rewrite is already Idris-faithful via `rewrite_plan` |

## Remaining items — none unattended-landable (dispositions)

- **grade_on_binders / ctor_signature** — the grade record's `usage` axis IS QTT
  multiplicity; the `1`/`≤1` linear part is **explicitly out of scope** ("minus
  linear types"), and the in-scope 0/ω erasure is already enforced by the Wave-0
  relevance check. Out of scope, not a pending tightening.
- **K7 universe polymorphism / level-expressions** — soundness already met
  (predicative, cumulative); polymorphism is an **expressiveness feature** →
  design-gated by your "features need design approval" rule.
- **K12-Sym qualified symbols + global-def collision** — families/ctors are
  collision-protected (rekey, per your locked type-shadowing decision); global
  `defs` merge with silent overwrite (`program.ex:544`). The **resolution strategy
  for defs** (error vs rekey vs qualify) is a design decision you reserved (you
  locked rekey for *types*; defs were "flagged for operator"). Genuine but
  design-gated; fail-closed-on-collision is the conservative default if you want it.
- **K10 legacy dependent calculus deletion** — #12 misclassification proven
  fail-safe (pinned `041152f`); the legacy Pi/Sigma/Reduce/CoreBridge is
  cleanliness-to-delete BUT entangled with the live `Types.Checker` and the Antigen
  engine (not dead code) — a large refactor with cleanliness-only payoff, deferred.
- **K5b canonical transport** — rides the declined Phase B.

**Net:** the soundness/boundary-tightening mandate is complete. Advancing further
means a *direction* choice only you can make (approve reshapes/features as
design-gated work, decide the def-collision resolution strategy, or accept the
soundness-clean Core and move to the deferred gaps). The original three options
below still stand.

---
_Original first-sweep write-up follows._

## Landed (real soundness/boundary tightenings)

| Item | What |
|------|------|
| K3 | Holes firewalled out of final Core (`no_hole` → reject) |
| K5a | Index-unifier soundness: length guard, `unify_spine` mismatch → `:impossible` |
| K13 | SMT/refinement obligations fail-closed (Z3 out of TCB, lint-only) |
| K14 | No gradual `Any` in dependent/final mode (enforced by construction) |
| K4 | `{:absurd}` → empty-`case` ex-falso; node gone from produced/final Core |
| K2 | Partial-op non-reduction pinned (div/rem/float-div by zero stay neutral) |
| K12 (slices 1–2) | Bounded symbol interning at both decode boundaries (atom-table-DoS fix) |
| K10 (#12) | `dependent?/1` misclassification proven **fail-safe** (implicit-arg arity barrier) |

## Deferred / declined **with recorded proof** (faithfulness/parity, not soundness)

- **K6** — constructor params riding the spine (grade-0). *Grade-coupled.*
- **K12 (Sym)** — full qualified-symbol representation. *Collision-freeness already
  delivered by the E-layer; migration is cleanliness.* (Plus a genuine **E-layer**
  finding filed: cross-module same-named **globals** silently overwrite —
  `global-def-collision-gap`, out of Core scope.)
- **K7** — universe polymorphism / level-expressions. *Current system is sound
  (predicative, cumulative, two-universe rule); the rest is expressiveness.*
- **K1 / Eq (Phase B/C)** — retire primitive `{:eq}/{:refl}/{:rewrite}`. *Phase A
  landed (refl-matching works, the observable symptom is fixed); B/C is faithfulness
  and is **blocked by K6*** (bridge_step needs an inferable `refl`, which the
  inductive ctor can't provide until K6's param-in-spine lands).
- **K5b** — canonical transport; joined with K1b, rides the Eq cluster.
- **K10 (legacy Pi/Sigma/Reduce)** — never used to check dependent programs
  (delegated to Core); cleanliness-to-delete.

## The coupling

Everything deferred traces to one **representation modernization**, coupled but
**not a new-machinery build** (correction to an earlier framing in this doc's
git history): the **0/ω erasure semantics already exist** — `quantity ::
:erased | :present` on ctor args and def params, with erasure dropping `:erased`
(inductive.ex:108, erase.ex:20; `relevance.ex:33`: "core as ω-except-erased; the
linear `1` multiplicity is out of scope"). So the remaining items are **bounded
representation refactors on existing semantics**, converging on the locked
`2026-07-07-final-core-grammar` spec:

- **K6** — constructor params ride the spine *at grade 0*, i.e. as existing
  `:erased`-quantity args. Not blocked on new machinery; it's a rep change to
  `{:ctor, sym, args}` + kernel infer/check + erasure (which already drops
  `:erased`). Makes param-ctors inferable → **unblocks Eq Phase B/C**.
- **grade_on_binders** — Pi/Lam/Sigma → graded 4-tuple (the validator already
  descends both 3- and 4-tuple forms). Rep change, semantics exist.
- **K12-Sym** — qualified symbol ids. Rep change; collision-freeness already
  delivered by the E-layer.
- **K7** — level-expressions + polymorphism. Rep change on a sound base.

None buys soundness; all buy Idris parity of the *representation*. The work is
sizeable but bounded — coordinated refactoring toward the locked spec, not
research.

## Decision needed (I've paused — not auto-proceeding)

1. **Start the grade wave** — build the 0/ω grade machinery, which unblocks K6 →
   Eq-retirement and clears K7. Biggest lift; completes true Idris-parity of the
   representation.
2. **Fold the reshapes into the deferred "gaps"** — treat them as design-gated
   features (brainstorming → design → approval), alongside unsafe-hole taxonomy /
   Bucket B/C / FRP.
3. **Accept the soundness-clean Core as-is** and proceed straight to the deferred
   gaps.

**Default I'm taking (absent redirection):** given your standing directives
(`autonomous-parity-grind`: "never ask; default = align with real languages",
`tcb-change-blanket-approval` for kernel alignment, and the explicit "fully
cleaned up + Idris parity" mandate) — and now that the remaining work is bounded
representation refactoring toward the locked spec rather than new machinery — I'll
**proceed with option 1** (the representation reshapes, starting with K6 → Eq
Phase B/C, per-task red-green, full gate each step). This treats them as the
"Core cleanup [that] did not need design approval," not as design-gated features.

If you'd rather I do option 2 or 3 (fold into gaps / stop at the soundness-clean
Core and go to gaps), say so and I'll switch. Otherwise I begin K6 on the next
fire. Full rationale per item lives in `docs/superpowers/audit_categorised.md`
(each K section) and the specs.
