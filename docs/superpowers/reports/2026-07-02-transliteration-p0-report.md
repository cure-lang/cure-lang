# Transliteration Program P0 — Closing Report

**Branch:** `autopilot/transliteration-p0`
**Date:** 2026-07-02
**Charter:** [`2026-07-02-idris-transliteration-program-design.md`](../specs/roadmap/2026-07-02-idris-transliteration-program-design.md) §6 (P0: audit + program setup)
**Plan:** [`2026-07-02-transliteration-p0-plan.md`](../plans/2026-07-02-transliteration-p0-plan.md)

## Outcome

P0 is complete. The differential oracle is standing, the `rewrite_plan/5`
audit is done (one real delta fixed, one documented reach residual), a general
elaborator bug the oracle surfaced was fixed, and the parity ledger §2 now
matches the tree. Full suite green: **2201 passed (2198 tests + 3 doctests), 0
failures** (pre-P0 baseline 2185; +16 P0 tests).

## Task-by-task

| Task | Outcome | Commit(s) |
|---|---|---|
| 1. Snapshot refresh | 3 gap files vendored (`WithClause.idr`, `Elab/Case.idr`, Agda `With.hs`); MANIFEST §E + refresh log. Pins verified (Idris2 `fd405085b`, Agda `7273757e5e`). **esp32-beam repo.** | `ada483b` (esp32-beam) |
| 2. Build idris2 | `idris2 0.8.0-fd405085b` built from the pinned clone (Chez backend; `CPATH`/`LIBRARY_PATH` for Homebrew gmp). No repo change. | — |
| 3. Oracle harness | `Cure.Oracle` (discovery, `cure_verdict/1`, `idris_verdict/2` via tmp-cwd + `IDRIS2_PATH`, fixture I/O, `consistent/1` relation contract) + `mix cure.oracle` + unit tests. Red→green, 6/6. | `a502e6e` |
| 4. Rewrite corpus | 7 paired `.cure`/`.idr` probes + offline replay test + committed `verdicts.json`. Live regen ran the real idris2. | `6f86b16` |
| 5. `rewrite_plan/5` audit | Candidate 1 (error vocab): **no delta** (parity). Candidate 3 (motive under `:case` binder): **real bug, fixed**. Candidate 2 (conversion occurrence, rw07): sound incompleteness → documented `cure_stricter` reach. | `e95b874` |
| (added) Ctor-arg fix | Oracle surfaced a general bug: non-nullary constructor application as a function-call argument → `:ctor_arity`. Fixed red-green (untyped `elaborate_expr` now constructor-aware). | `f8cb7a0` |
| 6. Ledger §2 | #2/#7/#8/#16 → ✅, #13 hole-closed → reach (Layer E→K,E). Recount: 11 at parity, 14 remain, 0 live holes. §3 left to the banking plan. | `357a494` |
| 7. Final gate + report | Full suite + oracle replay green; this report. | (this commit) |

## Oracle corpus — final verdict relations

| Probe | cure | idris | relation |
|---|---|---|---|
| rw01 plus_zero_right | accept | accept | same |
| rw02 symmetry_goal | reject | reject | same |
| rw03 no_occurrence | reject | reject | same |
| rw04 plus_comm (double-rewrite) | accept | accept | same |
| rw05 non_eq_proof | reject | reject | same |
| rw06 restated_zero_right | accept | accept | same |
| rw07 conv_occurrence | reject | accept | **cure_stricter** |

rw04 flipped reject→accept after the `abstract_term` `:case`-binder fix + the
ctor-arg fix + correcting the probe's `refl` bodies (they had used pre-rewrite
LHS shapes). rw07 is the one documented divergence.

## Task-5 audit conclusion

Audited `Cure.Elab.Elaborator.rewrite_plan/5` (and `abstract_term/3`,
`eq_parts/1`) against vendored `TTImp/Elab/Rewrite.idr` (`elabRewrite`,
`getRewriteTerms`, the `RewriteNoChange` post-check).

- **Candidate 1 — error vocabulary: no delta.** Cure already distinguishes
  `:rewrite_proof_not_equality` (≈ `NotRewriteRule`) from `:rewrite_no_match`
  (≈ `RewriteNoChange`); confirmed via rw05/rw03 probes.
- **Candidate 3 — motive abstraction under binders: real, fixed.**
  `abstract_term/3`'s generic tuple clause recursed into `:case` branch bodies
  at the scrutinee depth, so branch-bound vars in `[depth, depth+arity)` were
  wrongly shifted by the `{:var,i} when i>=depth -> i+1` clause, corrupting the
  motive (kernel rejected it as `:rewrite_premise`). Fix: an explicit `:case`
  clause mirroring `Term.shift/3` (`term.ex:107-108`) — abstract scrutinee and
  motive at `depth`, each branch body at `depth + arity`. Kernel/Normalise/Term
  untouched; `rewrite_plan/5` arity unchanged.
- **Candidate 2 — occurrence up to conversion: sound incompleteness (reach).**
  The trusted normalizer preserves stuck `case` and leaves `plus(Z,n)`
  unreduced in scrutinee position, so the goal's stuck-`:case` occurrence is
  syntactically distinct from (though definitionally equal to) the proof
  endpoint. Cure's syntactic `contains_term?`/`replace_term` miss it where
  Idris' `replace'` matches up to conversion (`Core/Normalise.idr`). Documented
  as `cure_stricter` (rw07); conversion-aware matching is a P1 reach item.

## TCB diff

**None.** All fixes live in the untrusted elaborator (`lib/cure/elab/`). The
trusted kernel (`lib/cure/core/*`) was not touched.

## Pre-existing warnings

`mix test` emits `erl_lint`/`sys_core_fold` warnings from stdlib codegen
(unused vars/functions, shadowing) — pre-existing branch-hygiene debt, out of
P0 scope, not introduced here.

## P0 gate checklist (charter §8)

- [x] Audit-first before each edit (Task 1/5/6 verification steps)
- [x] Red-green for every code change (Tasks 3/4/5 + ctor-arg fix)
- [x] Kernel green + oracle replay green (Task 7)
- [x] Oracle fixtures banked (`verdicts.json` committed, replay offline)
- [x] Tests immutable once green; no verdict hand-editing (only relation/reason)

## Remaining (next clusters)

- **Antigen pre-port banking** — the parallel worktree (§3 of the roadmap;
  another agent). Note a cross-doc reconciliation: §2 now records #13's hole as
  closed, while §3's A1/`diverging` rows still read "🔴 live infection" — the
  banking run owns §3 and should reconcile those markers.
- **P1 reach** — conversion-aware `rewrite` occurrence matching (rw07; lift
  Idris `replace'`), Miller-pattern unification (#10), postponed constraints
  (#11), multi-arg/lexicographic descent (#13/#14).
- **P2 / P4** — expression-level `case` elaboration (vendored `Elab/Case.idr`)
  and `with`-abstraction (vendored `WithClause.idr` + Agda `With.hs`), the two
  largest still-liftable Idris algorithms.
- **Follow-up bug** — the ctor-arg fix's untyped path still does not infer
  erased ctor params/indices (noted limitation); a general constructor-argument
  elaboration pass is future work.
