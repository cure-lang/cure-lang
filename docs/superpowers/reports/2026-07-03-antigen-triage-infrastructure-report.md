# Antigen Triage Infrastructure — Completion Report (Run D)

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot (design-approved gate → hands-off)

Makes Antigen's infection triage **kind-agnostic**: every banked infection is now
minimized regardless of challenge kind (previously only `:typed_term`/`:mutant_term`
were shrunk), and structural **delta-debugging** (ddmin) drops whole
name-referenced list elements — redundant defs, ctors, families — alongside term
shrinking, under one shared predicate-call budget. Pure-Antigen, kernel public-API
only: **no `Cure.Core.*` (TCB) edits, no `:meck`, no new dependency.**

## What shipped

- **`Antigen.Shrink.candidates/1` generalized to all kinds** via the existing
  `Challenge.to_pieces/1` ↔ `from_pieces/7` corpus bridge. Term rewrites now fire
  for every kind's Term pieces (`:family`/`:indexed_case`/`:rewrite_eq`/
  `:forcing_pair`/`:stuck_elim`/`:def_group`/`:stub`); the de-Bruijn ctx-drop path
  stays exactly as-was for `:typed_term`/`:mutant_term`; `:elab_program` is a
  principled `[]` (no Term pieces). `reseed/1` and `well_formed?/1` exposed
  (`@doc false`) for the orchestrator.
- **`Antigen.Bisect`** — `candidates/1` drops one whole name-referenced element per
  candidate via a payload-direct `List.delete_at` (no de-Bruijn reindexing — members
  are referenced by `{:global, name}`, not index) and prunes any now-dangling
  `focus` entry naming a removed def.
- **`Antigen.Triage`** — `minimize/3 :: {Challenge.t(), stats}` drives a single
  one-accepted-step-at-a-time fixpoint over `Bisect.candidates ++ Shrink.candidates`
  (bisect first), gated by a **kind-agnostic `size/1`** (pieces' term nodes +
  numeral magnitude + list-element count). Deterministic, monotone (size strictly
  decreases per accepted step), budget-bounded (one shared predicate-call budget),
  `safe_pred`-guarded, `well_formed?`-prefiltered.
- **Runner wiring** — the infection branch calls `Triage.minimize/3` for **every**
  kind (the old `c.kind in [:typed_term, :mutant_term]` guard removed); `:triage`
  stats merged into the health map.
- **Report** — an optional `triage:` line (`size o→m · bisect −b elems · shrink −s
  rewrites`) rendered when `:triage` is present; omitted otherwise. No signature
  change to `write_infection/4`.

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | design approved (in-challenge ddmin — NOT git-bisect/TCB); spec written | `2256e7b` |
| 1 — Spec review (Sonnet subagent) | hardened; `:stub` added to kind list, §6.3 focus-cleanup crash rationale corrected to `Totality`/`StuckElimDelta`/`Generators.Forcing` | `9e6e262` |
| 2 — Plan | 6-task TDD plan | `8982464` |
| 3 — Plan review (Sonnet subagent) | 5 passes; folded `Coverage.terms_of/1` `:stuck_elim` widening + red test into Task 1 (silent-no-op gap) | `8102a66` |
| 4 — Execute (Opus, TDD, one build at a time) | red → green per task, ghost-authored | `ffbbdb1`, `5b624b9`, `c882f32`, `b97bd66`, `4b4a21c` |

### Per-task execution (Stage 4)

1. **`ffbbdb1`** — generalize `Shrink.candidates` to all kinds via pieces bridge +
   widen `Coverage.terms_of/1` to `:stuck_elim`. Red: `candidates/1` private + crashes
   on `:family` ctx-deref; `well_formed?/1` undefined. Green 15/15.
2. **`5b624b9`** — `Antigen.Bisect` (name-referenced element ddmin + focus cleanup).
   Red: module undefined. Green 4/4.
3. **`c882f32`** — `Antigen.Triage` (`minimize/3` + kind-agnostic `size/1` + combined
   fixpoint). Red: module undefined. Green 5/5 (size monotone, both-dims reduce,
   budget-bound determinism, safe_pred no-crash, elab no-op). Architecture test green.
4. **`b97bd66`** — runner wiring for all kinds + `:triage` thread. Red: `:def_group`
   infection banked whole (`[:f, :g]`). Green: bisect drops redundant `:g`, banks `[:f]`.
5. **`4b4a21c`** — report `triage:` line. **Test strengthened before green** — see below.

## One test strengthened (TDD red-step correction, Task 5)

The plan's positive report test asserted `body =~ "triage:"` + substrings `"27"`,
`"9"`, `"bisect"`, `"shrink"`. All of these are **already emitted by
`#{inspect(health)}`** (the health map's `triage: %{orig_size: 27, …,
bisect_drops: 2, shrink_rewrites: 11}` key), so the test passed **before**
implementing `triage_line/1` — TDD's red step was impossible, and the test failed
to pin the feature. Per the plan's sole immutability exception (a test proven to
encode inadequate behavior, argued explicitly), the positive assertion was
strengthened to the **distinctive formatted line** only `triage_line/1` produces —
`size 27→9`, `bisect −2 elems`, `shrink −11 rewrites` (which `inspect` never emits;
it renders `orig_size: 27, min_size: 9`). This produced a genuine red, then green.
The omit test was already correct and unchanged.

## Verification

- **Full suite (single authorized run):** `2605 passed` (3 doctests, 2602 tests),
  0 failures — up exactly **+15** from Run C's 2590 (3 shrink + 4 bisect + 5 triage
  + 1 runner + 2 report). No regressions: `:typed_term`/`:mutant_term` candidate
  enumeration is byte-identical (pinned by the Task 1 regression test).
- **StreamData quarantine:** clean; `test/antigen/architecture_test.exs` green
  (`lib/antigen/{triage,bisect}.ex` are outside the quarantined glob, no `StreamData`
  literal).
- **Working tree:** clean (test-run `seeds.sexp` side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Well-formedness gap closed (found during Stage 3 hardening)

`Coverage.terms_of/1` had a **literal** `kind: :forcing_pair` clause but no
`:stuck_elim` clause, despite `:stuck_elim` sharing `:forcing_pair`'s exact payload
shape. Because `well_formed?/1` rescues any crash to `false`, this made every
`:stuck_elim` candidate silently malformed — harmless while only
`:typed_term`/`:mutant_term` routed through `Shrink`, but the moment Task 4 routed
**every** kind through `Triage.minimize/3` it would have made `:stuck_elim` a silent,
permanent, unminimized no-op (indistinguishable from `:elab_program`'s legitimate
no-op). Fixed in Task 1 by widening the clause to `k in [:forcing_pair, :stuck_elim]`,
pinned by a red test.

## Boundaries (honest framing)

This is **triage infrastructure** — it minimizes already-found infections; it does
not find new ones. `:elab_program` is a deliberate no-op (string-source shrinking is
a documented non-goal, §3). Minimization is greedy 1-minimal (first-accepted,
restart-on-acceptance), not a full ddmin granularity ladder (§3 non-goal). Safety is
the caller's same-violation-shape predicate, not static analysis — a dropped
element that changes the violation shape is simply rejected.

## Next runs

- **Task #66** (spec drafted, `8bbd309` + V6 `9218344`): Antigen beyond the kernel —
  property-test the untrusted dependent-type machinery (normalizer, unifier,
  elaborator-soundness, erasure, totality-closure, SMT lint). Not yet through the
  autopilot design gate; awaiting operator's remaining open questions (phase order
  V1 vs V3, `Types.Reduce` untranslatable-fragment reach, `Types.Unify` timing).

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
