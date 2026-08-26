# Coverage-Guided Fuzzing — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-04 · **Status:** built, verified, **not merged**

A real libFuzzer-style code-coverage-guided fuzzer for the Cure kernel, built inside
Antigen on Erlang `:cover`. Delivered in two staged phases via the autopilot chain
(brainstorm → spec → Sonnet spec-review → plan → Sonnet plan-review → Opus TDD).

## What shipped

**Phase 1 — measurement (Tasks 1–5).** `Antigen.Cover` drives `:cover` around the
existing `Runner.explore` campaign; `Antigen.CoverReport` renders a deterministic
report (`:beam_lib` abstract-code line→function mapping). `mix antigen cover [--out]`
produces per-module + per-function cold-line coverage. This replaces the *semantic*
feature-vector coverage we had with genuine instrumented **line** coverage.

**Phase 2 — guided loop (Tasks 6–12).** `Cover.guided_loop/1`: per-round draws under
cover → per-input coverage delta → bank interesting inputs to an edge-minimal corpus
(`Triage`-shrunk, covered-line-set-deduped) → live-refresh the `SeedPool` so crossover
reuses banked edges mid-run → credit per-group edge yield → reweight the generator
toward high-yield groups → terminate on plateau or budget. Jackpots (new-edge + violation)
thread `:coverage_delta` into the single `write_infection` health map via a
`Runner.run_challenge` hook extracted **byte-identically** from `explore/1`.
`mix antigen cover --guided [--precise] [--edge-corpus] [--plateau] [--guided-round]`.

Batch (default) measures coverage once per round; `--precise` measures per challenge.
Neither uses `:cover.reset` — both are accumulating-set differences, so the loop's
baseline is never destroyed.

## Verification — the honest result

Full suite green (**2765**). StreamData quarantine intact on all new files. No TCB edits.

**Phase 1 baseline:** 427/881 kernel lines (48.5%) at 500 challenges; 429/881 (48.7%) at 2000.
Coldest modules: `Eval` 26% (`fold/2` recursor almost entirely cold), `Inductive` 26.6%.

**Guided vs unguided at equal budget (2000 challenges, isolated scratch seed pools):**

| Run | Lines covered | Edges banked | Rounds | Wall-clock |
|---|---:|---:|---:|---:|
| Unguided (one-shot) | **429** | — | — | 5.74s |
| Guided batch (plateau 2) | 411 | 4 | 7 (early plateau) | 3.53s |
| Guided precise (plateau 2) | 420 | 21 | 5 (early plateau) | 3.75s |
| Guided precise (full budget) | 424 | 23 | 20 | 7.95s |

**Finding (spec Risk #3, recorded not glossed): coverage-guided steering does NOT
improve kernel coverage over unguided fuzzing in this codebase.** All variants converge
to ~48–49% (424–429/881), and guided precise at full budget is ~38% *slower* for
slightly *less* coverage.

**Root cause:** the bottleneck is generator **reachability**, not generator **weighting**.
The cold code (`Eval.fold` recursor, `Inductive` eliminator) requires structurally
different inputs the current generators cannot produce; reweighting existing generators
by edge yield cannot create reachability that no generator has. Edge-novelty bias only
helps when *some* generator can already reach new code.

**Cost (Risk #2):** batch vs precise — precise adds per-challenge `:cover.analyse`
overhead; at full budget precise is ~38% over unguided wall-clock, batch less so. The
batch/precise split is real and behaves as designed.

## What this is good for

The **measurement** half (Phase 1) is immediately useful: `mix antigen cover` gives a
precise, deterministic map of which kernel lines the Antigen campaign never exercises —
a concrete backlog of cold branches to target. The **guided** half is mechanically
complete and correct, but its value is gated on future work that gives generators
reachability into the cold code (new structure-directed generators for the recursor /
eliminator paths), at which point edge-novelty bias can steer toward them.

## Per-stage commits

- Spec + Sonnet hardening: `30c35e3`
- Plan + Sonnet hardening: `cbf1f44` → `ccf99f3`
- Phase 1: `0f5867e` `6722205` `47ca63a` `64dbec0` `8f445a7` `365beeb`
- Phase 2: `9e60ca5` `b1c58d1` `204830d` `3e44aa7` `c9e84cb` `369eb2b` `a8795d8` `e815054` `d9e8444`

## Follow-ups (not done — for the operator)

1. Structure-directed generators for `Eval.fold` (recursor application) and `Inductive`
   eliminator paths — the actual lever for coverage, which the guided bias can then exploit.
2. Offline coverage-exact edge-corpus minimization post-pass (`:cover.reset`-based),
   deferred because it would destroy the live loop's accumulated baseline.
3. If pursued, re-run the guided-vs-unguided comparison after (1) to confirm the bias
   now pays off.

**No auto-merge.** Review and merge `autopilot/antigen-tier-b` when ready.
