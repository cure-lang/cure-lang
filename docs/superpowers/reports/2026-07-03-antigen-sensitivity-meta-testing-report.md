# Antigen Sensitivity Meta-Testing — Completion Report (Run C)

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot (design-approved gate → hands-off)

Proves Antigen's kernel-soundness assays are **sensitive** — that a green run is
load-bearing, not vacuous — by running the *real* assays against deliberately
weakened kernels (one rule made too-permissive) and characterizing, per
weakening, whether an assay fires an infection. Pure-Antigen, kernel public-API
only, **no TCB edits, no `:meck`, no new dependency**.

## What shipped

- `Antigen.Meta.WeakKernel` — `real/0` (identity map of the 7 kernel ops) +
  `weaken/1` (7 named one-rule permissive stubs). The real kernel is never
  modified; weakenings are injected only through each assay's `run/2` seam.
- **Additive `run/2` kernel seams** on five assays (`term`, `positivity`,
  `universes`, `reflexivity`, `stuck_elim_delta`), each with `run/1` delegating
  through a private `@real_kernel` map so existing behavior is byte-identical.
  `mutation` needed no change — its pre-existing bare-fn `run/2` carries row 1.
- `test/antigen/meta/sensitivity_test.exs` — the 8-row matrix, each row a
  **baseline** (real kernel → sound verdict) + **weakened** (→ catalog cell)
  assertion pair, plus a roster completeness test.

## The sensitivity matrix (all 8 rows green — baseline sound, weakened as predicted)

| # | weakening | target assay | baseline (real) | weakened outcome | cell |
|---|---|---|---|---|---|
| 1 | `infer_accepts_all` | `mutation/rejection` | `:ok` (rejected) | `{:accepted_ill_typed, …}` | **CAUGHT** |
| 2 | `infer_wrong_type` | `term/infer_check` | `:ok` | `{:check_disagrees, …}` | **CAUGHT** |
| 3 | `check_accepts_all` | `term/infer_check` | `:ok` | `:ok` | **SLIP — gap** |
| 4 | `positive_accepts_all` | `positivity` | `:ok` (rejected) | `{:wrongly_accepted, :Bad}` | **CAUGHT** |
| 5 | `universe_accepts_all` | `universes` | `:ok` (rejected) | `{:wrongly_accepted, :u}` | **CAUGHT** |
| 6 | `conv_always_true` | `stuck_elim_delta` | `:ok` | `{:unsound_verdict, %{expected: false, got: true}}` | **CAUGHT** |
| 7 | `conv_always_true` | `reflexivity` | `:ok` | `:ok` | **SLIP — by design** |
| 8 | `conv_exhausts_fuel` | `reflexivity` | `:ok` | `{:non_normalizing, …}` | **CAUGHT** |

**6 CAUGHT · 2 SLIP.** The two SLIP cells are reported openly, not hidden:

- **Row 3 (gap):** a consistency assay (`term/infer_check`) is structurally blind
  to an accept-all `check` — it only ever calls `check` on the correctly-inferred
  type, where `:ok` is the *right* answer. This motivates a follow-on negative-`check`
  assay. A genuine coverage gap the matrix surfaced.
- **Row 7 (by design):** `reflexivity` is a non-termination detector
  (`{:ok, _} -> :ok`), verdict-blind by construction — a wrong *verdict* is out of
  its contract. Rows 6 (stuck_elim_delta catches the same `conv_always_true`) and
  8 (reflexivity *does* catch `conv_exhausts_fuel`, its actual halting contract)
  together prove reflexivity's row is honest: insensitive to verdict corruption,
  sensitive to halting corruption.

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | design approved (per-fn boundary seam, no TCB/meck); spec written | `d3f958f` |
| 1 — Spec review (Sonnet subagent) | 5 passes; one fix (regression-coverage wording: stuck_elim has no dedicated assay test, uses corpus-replay) | `2b0b20c` |
| 2 — Plan | 7-task TDD plan | `8ee7388` |
| 3 — Plan review (Sonnet subagent) | 4 passes, **zero defects**; traced all 8 rows incl. the 3 risk areas (2/3/6) to exact kernel clauses; no edits needed | (no commit — clean) |
| 4 — Execute (Opus, TDD, one build at a time) | red → green per task, ghost-authored | `06126ea`, `39fe6f5`, `64ca615`, `0b38b6c`, `bc4aa48`, `ae7aacd`, `7b5ae45` |

### Per-task execution (Stage 4)

1. **`06126ea`** — `WeakKernel` (real/0 + 7 weakenings). Red: undefined. Green 4/4.
2. **`39fe6f5`** — `Term.run/2` seam + rows 2,3. Red: `run/2` undefined. Green (rows + term regression).
3. **`64ca615`** — `Positivity.run/2` seam + row 4. Red → green (row + positivity regression).
4. **`0b38b6c`** — `Universes.run/2` seam + row 5. Red → green (row + universes regression).
5. **`bc4aa48`** — `Reflexivity.run/2` seam + rows 7,8. Red → green (rows + reflexivity regression).
6. **`ae7aacd`** — `StuckElimDelta.run/2` seam + row 6. Red → green (row + corpus-replay regression). Empty-env `Z`/`S(Z)` baseline held exactly as the reviewer traced.
7. **`7b5ae45`** — row 1 (mutation, existing seam) + 8-row roster. Row 1 green immediately (seam pre-exists); roster a static assertion.

## Verification

- **Full suite (single authorized run):** `2590 passed` (3 doctests, 2587 tests), 0 failures — up exactly +13 from Run B's 2577 (4 WeakKernel + 9 sensitivity). No regressions: every additive seam keeps its `run/1` byte-identical.
- **StreamData quarantine:** clean; `test/antigen/architecture_test.exs` passes (`lib/antigen/meta/` is outside its glob).
- **Working tree:** clean (test-run seed side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Boundaries (honest framing)

This tests the *tests* — evidence the assays are sensitive, **not** a proof of
kernel soundness, and not exhaustive coverage. SLIP cells are surviving mutants
reported openly. Weakenings are simulated at **assay boundaries** (outside the
TCB); the real kernel is never modified.

## Deferred follow-ons (documented in spec §7)

- **Transitive-propagation matrix** via `:meck`: weaken a kernel-internal rule an
  assay never calls directly (e.g. `conv` inside `check_def`) and confirm an assay
  still catches it end-to-end — the one niche the boundary seam cannot reach.
- **Full-suite sensitivity**: extend to the remaining assays and to *incompleteness*
  weakenings (a too-strict rule caught by a positive-label assay) for a two-sided matrix.
- **`mix antigen.sensitivity`** printer rendering the matrix on demand.

## Next runs

- **Run D** (task #65): triage infrastructure (shrink-all-kinds + auto-bisect).

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
