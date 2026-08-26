# Autopilot completion report — Antigen conversion-at-depth (sub-project B of "deep injection")

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — stayed on this branch per operator instruction (no separate worktree; see the `autopilot-worktree-preference` memory).
**Status:** complete. Full suite green — **2299 passed, 0 failures** (3 doctests, 2296 tests; +8 over the post-A 2291). **Not merged** — operator merges when ready.

With B landed, the **deep-injection arc is closed**: A (propagation) threads an intrinsic rejection up nested checked positions; B (conversion) forces the kernel to *compute* an expected type by reduction and compare it into a same-headed indexed family. Together they cover both "does the error get back up" and "is the comparison itself correct at depth."

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Design gate: operator chose **reject + accept-dual** scope. Probed all 4 carriers (2 × 2 polarities) + control against the live kernel; spec written + self-reviewed | `ed00655` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | Converged 4 passes (2 clean); 6 findings via a live-kernel probe harness — biggest: the draft's "`infer` returns a normalized `Value`" was **false** (`Eval.eval` never δ-unfolds globals; reduction happens in `Conv.conv_values?` during `check`, and again in the assay's `converges?`) | `77bc401` |
| 2 — Plan (writing-plans, inline) | 7-task TDD plan; **probed carriers at `conv_depth` 0–6 through the real assays** (reject→`Assays.Mutation` `:ok`, accept→all three `term/*` `:ok`) before writing | `9986963` |
| 3 — Plan review (Sonnet) | Converged 5 passes (2 clean); 3 findings (Task-4 `default_gen` visibility change missing from the code block; a dead `SigMenu.env_of` re-certifying the env for nothing; a `conv_carrier_of` file-attribution contradiction). Re-probed 0/1/3/6 both carriers both polarities + control | `17c6988` |
| 4 — Execute (Opus, strict TDD) | 6 tasks, red→green→commit each | `1e15569`…`4b1c640` |
| 5 — Verify + report | Full suite green; acceptance explore; this report | — |

## The load-bearing mechanism

The discriminating difference sits in a `Vec` **index behind a `plus` redex**, so the kernel must **reduce** `plus (S^a Z)(S^b Z) → S^{a+b} Z` before it can compare indices in a **same-headed** `Vec` family. A's mismatches are at the *head* (`Nat` vs `Vec`) or intrinsic — B is the first corpus to stress index comparison *within* a same-headed indexed family, after reduction, at drawn depth (`conv_depth 0..6`). Two carriers:
- **`:conv_index`** — the `vcons` telescope 3rd arg (`xs : Vec n`, `n = plus…`).
- **`:conv_motive`** — a dependent `case` motive application `(λ_:Bd. Vec (plus…)) T` (β + `plus`), arity-0 `Bd` branches (no binder over the hole → no `Term.shift`).

Two polarities, both **construction-guaranteed** (numerals compared in Elixir, never the kernel):
- **Reject** (`:mutant_term`) — filler index `S^{a+b+1}` ≠ reduced expected `S^{a+b}` → must `infer`-REJECT. Catches over-acceptance (a conversion hole comparing same-headed families without correctly reducing/recursing).
- **Accept** (`:typed_term`, the 3 existing `term/*` assays) — filler index `S^{a+b}` = reduced expected → must ACCEPT. Catches false-rejection / under-reduction.

The **control** (an accept shape with the reject filler → REJECT) is the load-bearing evidence that acceptance is reduction-driven, not vacuous.

## What was built

- **`Antigen.Generators.Conversion`** — `conv_reject/0` (→`:mutant_term`), `conv_accept/1` (→`:typed_term`), the 2 carrier builders, `vec_of/1`, uniform `conv_depth`-first depth-split draw. **No new assay, no `Cure.Core.Term` seam** (carriers closed + binder-free — the A design's seam guess was pessimistic). Backend-free.
- **`Challenge.@known_atoms`** += the 8 conversion atoms (genuine out-of-source-blob red test, per the A/v1 `[:safe]` lesson).
- **`Runner.conversion_metrics/1`** + `conv_carrier_of/1` — reject subset via `fault.carrier`; accept subset via **structural detection** of `:typed_term` terms (a `plus`-headed `Vec` index), which is safe in v1 because the ordinary `Term` generator never emits one. Health line + `:vacuous` stamp on carrier-diversity (≥2) + both-polarities.
- **`mix antigen`** default_gen wires `conv_reject` ×1 + `conv_accept` ×3 (one per `term/*` assay).
- **Conversion seeds banked** (both carriers reject + accept) + a static-replay meta-test that both polarities replay to the correct verdict, plus a negative test that ordinary typed-terms contribute **zero** to the accept detector.

## Acceptance run (`mix antigen --count 800`)

```
antigen health[conversion]: carriers=2 both_polarities=true reject=88 accept=198 → healthy
antigen health[mutant_term]: reason_diversity=9 max_depth=8 wrap_diversity=5 survivors=0 → healthy
antigen health[typed_term]:  binder_usage=0.93 reduction_activity=0.66 fuel_exhausted=0 discard=0.0 → healthy
antigen: 0 infection(s), 58 seed(s) banked
```

**0 infections** across 286 conversion challenges: no reject survivor (the checker over-accepts nothing at depth) and no accept false-violation (it under-rejects nothing). Side effects confirm the carriers do real work: `typed_term` reduction_activity rose 0.33 → 0.66 (accept carriers add genuine NbE), and `mutant_term` reason_diversity rose 7 → 9 (the two conv reject kinds fold in). A survivor or false-violation here would have been a genuine conversion-at-depth bug; there were none.

## Known gap (documented, spec §6 "Masking caveat")

Reject conv kinds and `conv_depth` fold into the shared `reason_diversity`/`max_depth` floors, so B's own generation can push those to their floors even if v1/A generation regressed. Accepted for v1 of B; the two conversion-specific signals catch B's own vacuity, and a wholesale v1/A regression would also surface via the per-vertical tests.

## Deep-injection arc — closed

A (propagation) + B (conversion) are the two halves named in the mutation-corpus report's "v2 deep-injection" follow-on. Both shipped; the follow-on is fully discharged.

## Follow-ons still queued (unrelated to deep injection)

- **Human-readable corpus terms + fault provenance** (operator-requested; its own spec/plan).
- **Value-level post-shrink + `ChoiceSeq` backend** — gated behind real antibodies.

## Next

Operator review + merge of `autopilot/antigen-tier-b` (now carries: Tier B + lazy generator + ChoiceSeq reference spec + mutation corpus + deep-propagation (A) + conversion-at-depth (B)).
