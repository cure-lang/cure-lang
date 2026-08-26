# Antigen coverage manifest — shape/cell coverage gate

**Date:** 2026-07-10
**Status:** approved, implementing
**Branch:** feature/idris-parity

## Problem

Four kernel soundness findings (S8 positivity app/λ-headed negative, S9 coverage
param-in-result-index, family-level universe ceiling, termination premature
certification) slipped past Antigen even though each finding's *assay already
existed and fired constantly*. What never happened was the **specific shape**
reaching the vulnerable clause. The existing coverage machinery cannot see this:

- `Antigen.Cover` (`:cover`) measures **kernel line** execution. S8's fail-open
  catch-all line *was* executed (it returns `true` for many legitimately-positive
  shapes) — line coverage stayed green while the soundness-relevant negative input
  never reached it.
- `Antigen.Coverage.key` is a **plateauing** feature vector for seed dedup. It
  deliberately collapses distinctions, so `app_head_negative` and the pre-existing
  `sigma_negative` map to the same cell — it cannot express "the app/λ head shape
  was never generated."

So a plain "which assay-ids fired, how many times" counter would have stayed green
throughout. We need **intra-assay shape coverage**: each assay declares the set of
soundness-relevant shape *cells* it is responsible for, and a gate fails when a
declared cell is never produced-and-run.

## Design

### Cell identity

A **coverage cell** is a stable, generator-chosen atom naming one shape/path an
assay must exercise. A **coverage point** is `{assay_id, cell}` — the same
generator can feed several assay ids (totality feeds `totality/diverging` and
`totality/terminating`), so the assay id is part of the point.

`Challenge` gains a `:cover_tag` field (atom | nil), defaulting to nil in
`Challenge.new/1`. It is **run-time metadata, not semantic identity**: it is NOT
serialized to the corpus (encode/decode untouched; replayed records carry
`cover_tag: nil`). Generators stamp it at construction.

### Manifest (expected)

Each participating generator declares `cover_cells/0 :: [{assay_id, cell}]` — the
cells it is responsible for covering — and exposes a sampleable `gen/0` that
produces `cover_tag`-stamped challenges. `Universes` gains a `gen/0` (frequency
over its named constructors) so it matches the uniform contract.

`Antigen.CoverManifest`:
- `@participants` — the generator modules under manifest (initially `Totality`,
  `Positivity`, `BranchUnify`, `Universes` — the four the gap bit).
- `expected/0` — union of participants' `cover_cells/0` (a `MapSet` of points).

### Ledger + gate

`test/antigen/cover_manifest_gate_test.exs`:

1. **Cell completeness (the recurrence-preventing check).** For each participant,
   sample its `gen/0` heavily, collect every `{assay, cover_tag}` with a non-nil
   tag, and assert `cover_cells/0 ⊆ hit`. Failure lists the missing points — e.g.
   "positivity declares `:app_head_negative` but no draw produced it."

2. **Explorer wiring.** Assert each pool participant's generator is reachable from
   `Mix.Tasks.Antigen.default_gen/0` (so its cells fire in real campaigns, not
   only in the gate). `Universes` is curated/seed-only and exempt from this check
   (covered instead by its seed test + its own `gen/0` in check 1).

3. **Dead-assay detection (level 1, folded in).** `Runner.registered_assays/0`
   enumerates every id in the assay registry. Assert each is either produced when
   sampling `default_gen/0` or is in an explicit `@curated_assays` allowlist (the
   seed-test / dedicated-harness–fed verticals). A registered assay that is neither
   sampled nor allowlisted is genuinely unwired → fail.

### Scope (deliberate, non-faking)

- Cell-completeness is checked **only for assays that opt in** by declaring
  `cover_cells/0`. Firing is checked for **all** registered assays. This lets the
  manifest grow incrementally instead of a fake full retrofit — consistent with the
  "don't chase or fake coverage" ethos (`antigen-coverage-plateau`).
- The manifest cells per participant are a **focused, soundness-relevant** set
  (the four gap shapes + the primary polarity/verdict classes), not every trivial
  constructor.
- No kernel-clause→assay obligation map (option C) — too costly to maintain, and
  cell-completeness already captures the failure mode.

## Testing

- Red-green: a unit test of the gate's diff logic with a synthetic missing cell
  proves the gate discriminates (goes red) — without mutating real generators.
- The four gap cells (`:app_head_negative`, `:param_solved`, `:family_ceiling`,
  `:pending_sibling`) appear in the manifest; the gate would have failed while any
  of the four bugs' generators lacked the shape.
- Full `mix test` gate green.
