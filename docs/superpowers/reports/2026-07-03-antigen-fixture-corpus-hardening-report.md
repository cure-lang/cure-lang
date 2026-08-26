# Autopilot completion report — Antigen fixture & corpus robustness hardening

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — stayed on this branch per operator preference. Written after merging `autopilot/lean-shape-matching` (112 commits) into it.
**Status:** complete. Full suite green — **2558 passed, 0 failures** (3 doctests, 2555 tests). `mutation_test.exs` green across a **12-seed sweep** (0 failures). **Not merged** — operator merges when ready.

This closes the flaky-mutation-test handoff and the three "defects surfaced by making the corpus readable," as three bundled robustness items: draw-independent mutation tests, a `@known_atoms` decode-safety fix, and regression guards locking the fault-schema + all-corpora-readable guarantees.

## Preface — the merge

Per the operator's instruction, `autopilot/lean-shape-matching` (112 commits of elaborator/kernel work: records, GADTs, polymorphism, first-class functions, nested matching) was merged into `antigen-tier-b` first (merge `5c9a15a`). One conflict — `test/antigen/corpus.sexp` (my readable migration vs their 11 added Base64 records) — resolved by taking the union (`--theirs`, 28 records) and re-running `mix antigen.migrate` to normalize all to readable. Full suite after merge: 2555 passed.

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Two AskUserQuestion rounds resolved the handoff's contradictions (see below) → approved a 3-part design. Spec written + self-reviewed | `aaf6491` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | 6 passes (2 clean). Corrected the spec's technical premises against live source | `67e3a1e` |
| 2 — Plan (writing-plans, inline) | 4-task TDD plan; probe-derived the exact membership check | `d415c2e` |
| 3 — Plan review (Sonnet) | 3 passes (2 clean). Caught a real test bug (see below); ran every concrete infer call | `b178a79` |
| 4 — Execute (Opus, strict TDD) | 4 tasks, red/green per §5's split | `bb8bf4d`…`b9aa34c` |
| 5 — Verify + report | Full suite green; 12-seed determinism sweep; this report | — |

## Investigation — the handoff didn't match the code

The handoff named `mutation_test.exs:36` (`f.expected_head != f.injected_head`) with a "draws an injected constructor equal to expected" mechanism. Grounding against the code falsified this: that assertion reads a **static** constant (`index_mismatch` is hard-coded `:Z`/`:S`), the test never samples StreamData, every `build/2` operator uses a **fixed** structural mismatch, a 600-draw-per-operator probe found **0 no-op** terms, and a 15-seed sweep was green. So rather than fix a mis-described flake, the operator approved **hardening by construction** — make the invariants draw-independent so no seed-flake can exist in the file regardless. The two Sonnet reviews then confirmed (5,000/3,000/600-draw probes) that the construction guarantees already hold, making Part 1 a pure test-determinism rewrite.

## What was built

**Part 1 — mutation determinism (`bb3870b`).** Factored `Mutation.apply_wrapper` into a pure, draw-free `wrap(inner, kind, filler)` (behavior-preserving — same terms, same `gnat` draws in production). Rewrote the three probabilistic assertions to be draw-independent: the uncontaminated-control test now enumerates each wrapper once with a fixed filler (well-typed inner accepts, fault inner rejects), a companion test folds a fixed deep stack (composition), and the diversity asserts became deterministic reachability (each operator's deterministic fault kind; each wrapper yields a distinct well-formed term).

**Part 2 — `@known_atoms` completeness (`bb8bf4d`).** The readable-corpus work surfaced that a bare-process decode raises when `from_pieces` runs `String.to_existing_atom` on a scaffold-carried def-name not pre-interned. Audit (probe-derived, values-only scaffold walk) found exactly `:data_split`, `:reify_distinct`, `:reify_eq` (lean-match's reify/data-split verticals) missing — added them. A new membership guard (`corpus_atoms_test.exs`) asserts every hazard-string in every committed corpus ∈ `@known_atoms`, permanently catching the class.

**Part 3 — regression guards (`38b0e6a`, `b9aa34c`).** A 4th committed corpus `reach_reify_split.sexp` (missed by the readable-corpus migration) was still Base64 — migrated it, and added a guard that all **four** corpora are fully readable + decode. Locked the fault-codec coverage with a test round-tripping every fault shape the generators actually emit (7 operators + a deepened `depth`/`wrap_path` fault + a conversion carrier fault).

## Reviewer catches (why the two-stage review paid off)

- **Spec review** rewrote three wrong premises: the decode hazard is `to_existing_atom` on scaffold *strings*, not raw atoms in the `[:safe]` blob; the real missing atoms are `:data_split`/`:reify_distinct`/`:reify_eq`, not the handoff's `:boom`/`:stuck_elim_delta` (both false positives); and a **4th** un-migrated corpus existed.
- **Plan review** caught a real bug in the reachability test: `wrap(Z, k, Z)` produces byte-identical terms for `:case_scrut` and `:case_branch` when inner==filler (4 unique, not 5 → the test would fail). Fixed to use a distinct filler `S(Z)`. It also flagged the out-of-scope `:elab_program` scaffold-atom hazard (documented) and ran every 5×2 concrete infer call to confirm the refactor is behavior-preserving.

## Verification

```
Full suite: 2558 passed (3 doctests, 2555 tests), 0 failures
mutation_test.exs seed sweep: 0 failures across 12 seeds (deterministic)
```

## Known follow-ons (documented, out of scope)

- **`:elab_program` scaffold-atom hazard** — `to_pieces(:elab_program)` stringifies scaffold *keys* only, so its atom-valued payload fields (`expect`/`relation`) would ride into the `[:safe]` blob as raw atoms; not exercised today (no committed `elab_program` record), must be re-audited if such challenges are ever banked.
- **Full spec-§2.2 conformance** — `:9-21` (per-operator rejection) was left as bounded sampling; it's construction-safe (can't flake) so rewriting it buys only stylistic uniformity. One-line follow-up if wanted.
- **`to_existing_atom` corpus decoder** — still deferred (would give hand-edit typo-safety).

## Next

Operator review + merge of `autopilot/antigen-tier-b`, which now carries: Tier B + lazy generator + ChoiceSeq spec + mutation corpus + deep-propagation + conversion-at-depth + value-level post-shrink + human-readable corpus + the full lean-shape-matching elaborator/kernel work (merged) + this fixture/corpus hardening.
