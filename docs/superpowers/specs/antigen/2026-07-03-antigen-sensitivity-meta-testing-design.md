# Antigen Sensitivity Meta-Testing — Design (Run C)

**Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b` · **Status:** design-approved, autopilot chain

## 1. Motivation

Antigen's 12 assay families all pass. The skeptic's real objection is not "did
they pass" but **"would they have gone red if the kernel were actually broken?"**
A test suite that stays green against a *deliberately unsound* kernel is
worthless; a green run only carries weight if the assays are demonstrably
**sensitive** to the soundness holes they claim to guard.

Run C builds that demonstration: a **sensitivity coverage matrix** produced by
simulating soundness holes — a kernel with exactly one rule made too permissive —
running the *real* assays against it, and recording, per hole, whether an assay
fires an infection. This is mutation testing applied to the metatheory suite
itself ("who tests the testers"), with the assays as the system-under-test and
the kernel weakenings as the mutants.

## 2. Core mechanism (locked)

Each weakening is a **one-rule permissive corruption**: a single kernel judgement
short-circuited to a too-permissive constant (`:ok` / `{:ok, true}` / an
accept-all `infer`), while **every other kernel call remains the real, unmodified
`Cure.Core.*`**. The weakened function is supplied to the assay through a
**per-assay injectable seam** — the pattern already shipped in
`Antigen.Assays.Mutation.run/2` (`run(challenge, &Kernel.infer/2)`).

Three properties are non-negotiable and follow from the locked mechanism:

- **No TCB edits.** `Cure.Core.*` is never modified. The weakenings live entirely
  in Antigen. (Confirmed rationale: adding an injection point to the kernel would
  put an "unsoundness lever" *inside* the trusted core — exactly what Antigen
  exists to test from the outside.)
- **No `:meck`, no new dependency.** Weakenings are plain Elixir functions.
- **Seams are additive and behavior-preserving.** Each seamed assay keeps its
  existing `run/1` byte-identical (it delegates to the new `run/2` with the real
  kernel map); the seam only *adds* an arity. The full existing assay test suite
  passing unchanged is the regression guard.

### 2.1 Why a *permissive* weakening needs a *negative-expectation* assay

Making a rule too permissive means the kernel now **accepts something it should
reject**. Only an assay that **expects a rejection** (a negative-label case, a
negative control, or a differential disagreement) can notice extra acceptance. A
purely-positive assay — one that only ever asks the kernel to accept things it
*should* accept — is structurally blind to a permissive weakening. This is not a
defect to hide; it is the single most important fact the matrix teaches, and it
predicts exactly which cells are **CAUGHT** and which **SLIP**.

### 2.2 Boundary-only reach (and the one deferred case)

A per-assay seam can weaken only the kernel rules an assay **calls directly at its
own boundary**. Because the assay families were each built to target a specific
judgement, essentially every rule worth breaking is *some* assay's direct call, so
the boundary seam reaches the whole v1 catalog. The one thing it cannot do is
weaken a **kernel-internal** rule (e.g. break `conv` *as used inside*
`check_def`) and test whether a *different* rule's assay catches it transitively.
That single niche — intercepting a hardcoded intra-TCB call from outside the TCB —
is achievable only by editing the TCB (forbidden) or runtime-patching the module
(`:meck`). It is an explicit **non-goal**, documented as the meck follow-on (§7).

## 3. The weakening catalog (v1)

`Antigen.Meta.WeakKernel` supplies named weakenings. `WeakKernel.real/0` returns
the full map of real kernel operations; `WeakKernel.weaken/1` returns `real/0`
with exactly one key overridden by a permissive stub. Named weakenings:

| key | overrides | permissive behavior |
|---|---|---|
| `:infer_accepts_all` | `infer` | `fn _ctx, _t -> {:ok, <Nat value>} end` |
| `:infer_wrong_type` | `infer` | real infer, then return a *different* type value |
| `:check_accepts_all` | `check` | `fn _ctx, _t, _ty -> :ok end` |
| `:positive_accepts_all` | `positive?` | `fn _env, _fam -> :ok end` |
| `:universe_accepts_all` | `check_def`/`check_family`/`check_ctor` | each `-> :ok` |
| `:conv_always_true` | `conv_within?` | `fn _t, _t', _env, _d, _sig, _fuel -> {:ok, true} end` |
| `:conv_exhausts_fuel` | `conv_within?` | `fn … -> :fuel_exhausted end` |

The v1 matrix (curated — proves sensitivity at the soundness-critical assays
**and** demonstrates the matrix surfaces real gaps; not all-12 × all-rules):

| # | weakening | target assay | fixture (fixed, hand-built) | baseline (real kernel) | weakened outcome | cell |
|---|---|---|---|---|---|---|
| 1 | `:infer_accepts_all` | `mutation/rejection` (existing `run/2` seam) | a known **ill-typed** `:mutant_term` | `:ok` (rejected) | `{:violation, {:accepted_ill_typed, …}}` | **CAUGHT** |
| 2 | `:infer_wrong_type` | `term/infer_check` | a known **well-typed** `:typed_term` | `:ok` | `{:violation, {:check_disagrees, …}}` *or* `{:inferred_type_mismatch, …}` | **CAUGHT** |
| 3 | `:check_accepts_all` | `term/infer_check` | same well-typed term | `:ok` | `:ok` | **SLIP — gap** (a consistency assay is blind to an accept-all `check`: it only ever calls `check` on the correctly-inferred type, where `:ok` is the *right* answer; motivates a follow-on negative-`check` assay) |
| 4 | `:positive_accepts_all` | `positivity` | a known **negative**-label family (non-strictly-positive) | `:ok` (rejected) | `{:violation, {:wrongly_accepted, …}}` | **CAUGHT** |
| 5 | `:universe_accepts_all` | `universes` | a known **ill_typed** family/def (Type-in-Type) | `:ok` (rejected) | `{:violation, {:wrongly_accepted, …}}` | **CAUGHT** |
| 6 | `:conv_always_true` | `stuck_elim_delta` | a known **negative**-label `:stuck_elim` (distinct NFs) | `:ok` | `{:violation, {:unsound_verdict, …}}` | **CAUGHT** (negative control) |
| 7 | `:conv_always_true` | `reflexivity` | a known `:forcing_pair` | `:ok` | `:ok` | **SLIP — by design** (reflexivity is a *non-termination detector*: `{:ok, _} -> :ok`, verdict-blind by construction — a wrong *verdict* is out of its contract; this is precisely *why* `stuck_elim_delta` exists and catches row 6) |
| 8 | `:conv_exhausts_fuel` | `reflexivity` | same `:forcing_pair` | `:ok` | `{:violation, {:non_normalizing, …}}` | **CAUGHT** (this *is* reflexivity's contract — halting, not verdict) |

Net: 6 CAUGHT, 2 SLIP (one genuine gap, one by-design blind spot). Rows 7 and 8
together prove reflexivity's row is honest: insensitive to verdict corruption,
sensitive to halting corruption — exactly matching its stated contract.

## 4. Test discipline

Tests **characterize observed sensitivity** — the reach/pin (D2/D3)
characterization discipline already used elsewhere in this codebase: each row
asserts the *actual current* outcome, never a wished one.

Every row is a **pair of assertions**, and the baseline is load-bearing:

1. **Baseline** — the fixture under the **real** kernel yields the sound verdict
   (`:ok` for the well-typed/known-label fixtures above). Without this, a
   "violation under the weak kernel" could be an artifact of a bad fixture rather
   than the weakening. The baseline proves the assay flipped *because of* the
   weakening.
2. **Weakened** — the same fixture under `WeakKernel.weaken(key)` yields the
   catalog's expected cell: `{:violation, _}` for CAUGHT rows, `:ok` (with the
   documented reason in the matrix) for SLIP rows.

Fixtures are **fixed, hand-built** challenges (mirroring the kernel_law tests),
not random draws — determinism is required so the matrix replays identically.
SLIP cells are asserted as `:ok` on purpose: they are surviving mutants, reported
openly, not silently dropped.

## 5. Files

- **Create** `lib/antigen/meta/weak_kernel.ex` — `real/0` (full real-op map) and
  `weaken/1` (name → real map with one key overridden). Lives under
  `lib/antigen/meta/`, *not* under `generators/` or `assays/`, so it is outside
  the StreamData-quarantine grep surface (it contains no StreamData regardless).
- **Modify** (additive `run/2` seam, `run/1` delegates to it with `WeakKernel.real/0`;
  behavior byte-identical): `lib/antigen/assays/term.ex` (needs `infer` + `check`),
  `lib/antigen/assays/positivity.ex` (`positive?`),
  `lib/antigen/assays/universes.ex` (`check_def`/`check_family`/`check_ctor`),
  `lib/antigen/assays/stuck_elim_delta.ex` (`conv_within?`),
  `lib/antigen/assays/reflexivity.ex` (`conv_within?`).
  `lib/antigen/assays/mutation.ex` is **unchanged** — its existing bare-fn `run/2`
  is used directly for row 1 (and is the precedent the whole design generalizes).
- **Create** `test/antigen/meta/sensitivity_test.exs` — the 8-row matrix, each row
  a baseline + weakened assertion pair, plus a regression note that the existing
  test suite must still pass unchanged. Concretely: dedicated per-assay files
  (`test/antigen/assays/{term,positivity,universes,reflexivity,mutation}_test.exs`)
  for four of the five touched modules, plus `test/antigen/corpus_replay_test.exs`
  for `stuck_elim_delta.ex` — the fifth touched module has no dedicated
  `test/antigen/assays/stuck_elim_delta_test.exs`; its `run/1` regression coverage
  comes only from corpus replay of the banked `:stuck_elim` records (the file
  named similarly, `test/cure/core/stuck_elim_delta_test.exs`, tests the kernel's
  δ-unfold behavior directly, not `Antigen.Assays.StuckElimDelta`).
- **Report** the rendered matrix into the Stage-5 completion report
  `docs/superpowers/reports/2026-07-03-antigen-sensitivity-meta-testing-report.md`.

The seam shape is a **kernel-overrides map** (`%{infer: …, check: …, conv_within: …,
positive?: …, check_def: …, check_family: …, check_ctor: …}`) with a single shared
real default (`WeakKernel.real/0`); each assay reads only the keys it uses. This
keeps the meta-test uniform. (`mutation` keeps its pre-existing bare-fn seam; the
meta-test invokes it in its native shape — uniformity across test call-sites is
cosmetic, not required.)

## 6. Non-goals

- No TCB (`Cure.Core.*`) edits; no `:meck`; no new dependency.
- No change to any assay's `run/1` behavior (additive seam only).
- Not exhaustive: a curated catalog at the soundness-critical assays, not
  all 12 × every rule. Assays with no soundness-negative expectation that the
  catalog does not exercise (e.g. `totality`, `rewrite/eq`, `indexed/case`,
  `elab/*`, the `kernel/*` laws) are out of v1 scope; adding rows for them is a
  documented follow-on, not a gap in this deliverable.
- **Kernel-internal / transitive-propagation weakenings** (does a `check_def`-based
  assay catch a `conv` break routed *through* `check_def`) are the explicit meck
  follow-on (§2.2) — deferred, not attempted.

## 7. Follow-ons (documented, not scheduled)

- **Transitive-propagation matrix** via `:meck` runtime intercept: weaken a
  kernel-internal rule the assay never calls directly and confirm an assay still
  catches it end-to-end. Pays `:meck`'s async/global-patch cost only where the
  boundary seam cannot reach.
- **Full-suite sensitivity**: extend the catalog to the remaining assays and to
  *incompleteness* weakenings (a too-*strict* rule caught by a positive-label
  assay), for a complete two-sided matrix.
- **`mix antigen.sensitivity`** printer that renders the matrix on demand (v1
  ships the matrix via the test + report; a CLI is YAGNI until asked for).

## 8. Honesty line

This tests the *tests* — it is evidence the assays are **sensitive**, i.e. that a
green Antigen run is load-bearing rather than vacuous. It is **not** a proof of
kernel soundness, and it does not claim exhaustive coverage. SLIP cells are
surviving mutants reported openly. Weakenings are simulated at assay boundaries
(outside the TCB); the real kernel is never modified.
