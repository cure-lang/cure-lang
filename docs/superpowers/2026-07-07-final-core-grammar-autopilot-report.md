# Autopilot Completion Report — Final-Core Grammar (Wave 0 / K11a)

**Date:** 2026-07-07
**Branch:** `feature/idris-parity` (run on the working branch by operator override; no worktree)
**Outcome:** ✅ complete — full suite green (3047 passed, 6 skipped, 0 failures)

## Stage outcomes

| Stage | Outcome | Commits |
|---|---|---|
| 0 — Brainstorm + spec | design approved interactively; spec written (pre-chain) | (grammar spec `…0aa8897`) |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | converged 7 passes / 2 clean; 9 fixes incl. §H↔§E.2 ex-falso contradiction | `40dc6be` |
| 2 — Writing-plans (inline) | K11a plan written; a spec §J defect found + fixed during planning (grade_on_binders can't reject in Wave 0) | `85028fa`, `4b330b8` |
| 3 — Plan review (Sonnet, recursive-skeptical-review) | converged 5 passes / 2 clean; 6 fixes incl. validate the declared type too, `Context.length/signature`, `async: false`, `:kernel` stage | `51ba848` |
| 4 — Execute (inline, Opus, strict TDD) | 7 tasks, red→green each, per-task commit | `58de52d`, `5008875`, `8c09292`, `22d4b8f`, `b2c1ce3`, `ea893fd`, `9c3213f` |
| 5 — Verify + report | full `mix test` once: 3047 passed, 0 failures | (this report) |

## What landed (K11a — the Final-Core grammar boundary)

- **`Cure.Core.Validator`** (`lib/cure/core/validator.ex`, +161): the full 11-clause
  checklist encoding the entire Final-Core target grammar (spec §A/§J); a Wave-0
  config that is **pure instrumentation** (legacy-detectors `:warn`, not-yet-reshaped
  clauses `:off`, **no `:reject`**); a case-branch-safe node walker; active
  legacy-node predicates (`no_hole`/`no_eq_node`/`no_prim_node`/`no_absurd_node`);
  deferred predicates (`grade_on_binders`/`qualified_syms`/`level_expr`) that fire
  the moment their clause is flipped on.
- **Kernel wiring** (`lib/cure/core/kernel.ex`, +33): `check_def/2` runs the validator
  over **both the declared type and the body**, emits warnings via
  `Cure.Pipeline.Events`, and rejects only clauses config-overridden to `:reject`.
  Wave-0 default rejects nothing → non-breaking (241→245 core tests, whole suite green).
- **`Cure.Core.MetaCheck`** (`lib/cure/core/meta_check.ex`, +59): `type_preserved?/2`
  (subject reduction #638) and `progresses?/2` (progress #639), each with a working
  detection test and a passing seed corpus that later waves extend.
- **`:kernel` pipeline stage** registered in `lib/cure/pipeline/events.ex`.

## The executable checklist is now live

Each later wave flips its validator clause to `:reject` as the kernel stops
producing the legacy form; at any commit the validator names precisely which
constructs remain legacy. Next per the audit tackle order: Wave 1 — K3 (holes),
K1a (`{:eq}/{:refl}/{:rewrite}`), K5a (index-unifier soundness), K13, K14.

## Not done (out of scope, later waves)

Binder grade fields, node deletions, qualified `Sym` ids, level-expressions,
flipping any clause to `:reject` by default, and the K5 index-refinement typing
rule. This run built only the scaffold + harnesses.
