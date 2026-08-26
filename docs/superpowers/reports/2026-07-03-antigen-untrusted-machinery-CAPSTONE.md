# Antigen Untrusted-Machinery Initiative — Capstone Report

**Branch:** `autopilot/antigen-tier-b` (NOT merged — awaiting operator) · **Date:** 2026-07-03
**Task:** #66 (complete) · **Mode:** autopilot via standing `/loop`, one bounded+committed stage per tick

This is the single consolidated read for the **merge + next-step decision**. It ties
together the six per-vertical reports (linked below) so you don't have to reconstruct
the arc. Each vertical also has its own spec, plan, two hardening reviews, and report.

## What the initiative did

Antigen was a property-based soundness engine for Cure's **trusted kernel**
(`Cure.Core.*`). This initiative extended it **beyond the TCB** to the **untrusted**
dependent-type machinery — the normalizer, unifier, elaborator, erasure/relevance
pass, totality-closure driver, and SMT lint — on the thesis that a component being
"untrusted" is not the same as "checked," and the kernel's own guarantees don't cover
bugs in the machinery that feeds it.

**Six verticals, each via the full autopilot chain** (spec → Sonnet spec-review → plan
→ Sonnet plan-review → Opus TDD execution → verify + report), all on one branch, no
auto-merge. Roadmap order run: V3 → V1 → V2 → V5 → V4 → V6.

## Result at a glance

| Vertical | Target (untrusted) | Assays | Verdict |
|---|---|---|---|
| **V1** normalizer | `Types.Reduce` | `normalizer/{differential,equal,intrinsic}` | sound |
| **V2** unifier | `Elab.Unify` + `Types.Unify` | `unify/{soundness,intrinsic}`, `unify_types/{fixpoint,intrinsic}` | sound |
| **V3** elaborator | elaboration surface | (elab-soundness suite) | sound |
| **V4** erasure/relevance | `Elab.Erase` + `Elab.Relevance` | `erasure/{idempotent,selective,wellformed}`, `relevance/soundness` | 🔴 **found: `erase/2` non-idempotence** |
| **V5** totality-closure | closure driver | `totality_closure/{soundness,completeness}` | sound |
| **V6** SMT lint | `SMT.Solver` (+ `SMT.Parser`) | `smt/{implication,unsat,witness}` | 🔴 **found: `parse_model/1` negative-value truncation** |

- **Full suite: 2728 passed, 0 failures** (grew from 2691 pre-initiative-tail through
  each vertical: V5 2691 → V4 2713 → V6 2728).
- **Two genuine defects surfaced**, both in untrusted (non-TCB) code.
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## The two findings — both now FIXED (2026-07-04, operator-authorized)

Both were surfaced by the audit, reported not-patched per the initiative's
find-don't-fix discipline, then fixed red-green as a separate authorized effort. Each
fix flipped its banked known-finding test from asserting the violation to asserting
`:ok`, so those tests now stand as regression guards. Full suite green at **2732** after
both fixes (0 failures). Fix commits: `06014ca` (erase), `748f949` (parse_model).

### Detail (as originally surfaced)

### 🔴 Finding 1 — `Cure.Elab.Erase.erase/2` is non-idempotent (V4)

`erase(env, erase(env, t)) ≠ erase(env, t)` whenever a constructor or global def has an
**`:erased`-before-`:present`** quantity ordering. The `:ctor`/`:app`-head clauses
re-`Enum.zip` the **original full-length** quantity vector against the already-shrunk
args on the second pass, so survivors realign to leading `:erased` entries and get
dropped. The production `seq` ctor (`[:erased×5, :present×2]`) collapses to
`{:ctor, :seq, []}` on a second application.
- **Severity:** dormant — `erase/2` is called exactly once per body (verified at both
  `emit.ex` sites), so no live path double-erases; and it's untrusted (a wrong erasure
  is a wrong runtime value, not an unsound type).
- **Fixed (`06014ca`):** arity guard on both the `:ctor` and `:app`-head clauses — only
  apply the quantity filter to full-form terms; an already-erased term (fewer args than
  the full arity) keeps all args and recurses. Single-erase behavior unchanged (the
  four existing `erase_test` cases stay green).
- **Regression guard:** V4's two `erasure/idempotent` known-finding tests (ctor `:MkP`,
  app-head `:g`), now asserting `:ok`, plus two new direct idempotence tests in
  `erase_test.exs`.
- Report: `2026-07-03-antigen-erasure-relevance-report.md`.

### 🔴 Finding 2 — `Cure.SMT.Parser.parse_model/1` truncates negative witnesses (V6)

Z3 emits negative model integers as `(- N)`; the parser's outer `[^\)]+` capture stops
at the first `)`, yielding the malformed string `"(- N"` instead of `-N`. So
`prove_with_counterexample` on any implication whose only counterexamples are negative
hands back a "witness" that isn't a usable value.
- **Severity:** real but narrow — the `:sat`/`:unsat` *verdict* is unaffected (Z3 still
  decides correctly); only model *extraction* corrupts, and only for negative witnesses
  consumed as diagnostics. Untrusted (SMT is a lint outside the TCB).
- **Fixed (`748f949`):** widened the `define-fun` value-capture regex from `[^\)]+` to
  `(?:\([^\)]*\)|[^\)])+` so a parenthesised `(- N)` group is captured whole and parsed
  to `-N` (bare tokens still parse as before).
- **Regression guard:** V6's negative-witness known-finding test (real Z3 on
  `x > -100 ⇒ x >= 0`), now asserting `:ok` (the witness parses and genuinely refutes),
  plus two new direct `parse_model` tests in `smt_test.exs`.
- Report: `2026-07-03-antigen-smt-lint-report.md`.

Both were **confirmed empirically at execution**, not merely traced — V4's via direct
Core-term construction, V6's via the real `z3` subprocess.

## The reusable pattern (why the six verticals look alike)

1. **Op-map seam** — every assay is `run/1` → `run/2(challenge, ops)`; `run/1` uses the
   real `@real` ops, negative controls inject a broken op via `%{Assay.__real__() | op: stub}`.
   No TCB edits, no `:meck`, no new dependency.
2. **Independent oracle** — the assay re-derives the reference computation (V1's
   surface→Core encoder, V5's reachability walk, V6's bounded `eval_pred`) so a real bug
   *mismatches* rather than mirrors. For V6 specifically the oracle is **not** the kernel
   (the kernel doesn't decide refinement arithmetic) — it's a bounded brute-force
   evaluator giving a **sound-in-one-direction** differential, matching the locked "lint
   soundness, not completeness" decision.
3. **Every violation branch has a negative control** (V2's dead-branch lesson: an
   untested branch is unverified dead code).
4. **Fixed catalog** wired via `Runner.assay_module/1` (no catch-all) + a typespec-only
   `Challenge` kind + `@known_atoms` — replayed deterministically, no corpus banking.
5. **Real findings kept as known-finding fixtures** OUT of the clean catalog (V4-style),
   so the clean sweep stays all-`:ok` while the bug is documented as a true-positive.

## Recommended next steps (your call — none started autonomously)

The defined roadmap (#66) is **exhausted**. The candidate follow-ons each need your
direction; the autopilot design gates new sub-initiatives on your design approval, and
the two fixes need explicit authorization (they're untrusted code, so outside the
blanket-TCB-approval standing order). In rough value order:

1. ~~**Authorize the two fixes.**~~ ✅ **Done** (2026-07-04, `06014ca` + `748f949`) —
   both fixed red-green, banked guards flipped to `:ok`, full suite green at 2732.
2. **Generator-expansion** (the umbrella's named follow-on). Today each vertical uses a
   small *curated fixed catalog* — it can only probe cases we thought of. Routing the
   catalogs through the `Antigen.Gen` reified-AST backend would let each assay find bugs
   in cases we *didn't* anticipate. This is a new sub-initiative (its own spec →
   design-approval gate → plan → execute).
3. **SMTCoq / proof-reconstruction** — explicitly the deferred "someday" from the locked
   SMT trust-boundary decision; only relevant if Z3 ever needs to move toward the TCB.

## Pre-merge audit (read-only, done 2026-07-03)

A cross-vertical audit of the initiative's own code confirms merge-cleanliness:
- **Contract:** every assay is `run/1`→`run/2` returning only `:ok | {:violation, _}`;
  every generator assay id has a matching `Runner.assay_module/1` clause; all six new
  `Challenge` kinds (`surface_expr`, `unify_problem`, `elab_program`, `closure_env`,
  `erasure_term`, `smt_query`) are in the `@type kind` union.
- **Hygiene:** no `TODO`/`FIXME`/`IO.inspect`/`dbg` in any of the six new assay/generator
  files; StreamData quarantine intact (`architecture_test` green).
- **Warnings:** `mix compile --warnings-as-errors` surfaces only **pre-existing**
  warnings (older verticals `positivity.ex`/`universes.ex`; `Cure.*` machinery) — **zero
  from the files this initiative added.** Not regressions.

## Merge

**Do NOT auto-merge.** `autopilot/antigen-tier-b` holds the whole initiative (six
verticals + this capstone). Per-vertical reports under
`docs/superpowers/reports/2026-07-03-antigen-*`. Merge when you've reviewed; the two
findings are the parts most worth your eyes.
