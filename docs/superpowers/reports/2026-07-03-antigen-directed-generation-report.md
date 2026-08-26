# Autopilot completion report — Antigen directed generation (Run A of A/B/C/D)

**Branch:** `autopilot/antigen-tier-b`. **Status:** complete, **not merged**. Full suite **2568 passed** (3 doctests, 2565 tests), 0 failures — +10 tests over the 2558 baseline. First of four sequential autopilot runs (A→B→C→D) improving the Antigen engine; B/C/D follow on the same branch.

## Motivation

A `mix antigen --count 50000` run banked a large seed set but found **0 infections** — undirected generation plateaus because dedup collapses to a coarse feature vector. This run makes generation reach deeper/more-diverse shapes, pure-Antigen (no `Cure.Core.*` TCB edits).

## Stage outcomes

| Stage | Outcome | Commit |
|---|---|---|
| 0 — Spec | 3-part design (coverage enrichment / SeedPool crossover / health-adaptive rounds), self-reviewed | `7953bd8` |
| 1 — Spec review (Sonnet, 12 passes) | 9 fixes — biggest: the backward-compat claim was wrong (`Corpus.dedup_key(_, :seed)` **is** `Coverage.key_string` → enrichment re-banks seeds); Part-3 branch-metric entanglement (only 4 of 11 branches have signals → 3-group T/M/F model); `:mutant_term`-pool soundness exclusion; arity-preservation | `f590d5f` |
| 2 — Plan | 3-task TDD plan, concrete code | `a6aafb9` |
| 3 — Plan review (Sonnet, 8 passes) | 9 fixes — non-colliding RED fixtures (`constructors/1` folds every AST tag), undefined `child_terms/1` (→ reuse `fold/3`), `Antigen.Gen` has no struct, canonical `Cure.Core.Term.closed?/1`, a `round_size: 0` infinite-loop floor | `e0f231c` |
| 4 — Execute (Opus, TDD) | 3 tasks, red→green | `f9…`→ below |
| 5 — Verify | full suite + baseline-vs-bias sanity | — |

## What was built

**Task 1 — enriched coverage key.** Folded a **former-histogram** (per-Core-former count bucket 0/1/many) and a **binder-depth bucket** into `Coverage.key/1`'s existing `flags` `MapSet` — arity-preserved (4-tuple), so `Runner.coverage_flags/1`'s positional destructure is untouched. Two terms that key **identically** today (`{app,(app plus v0),v0}` vs `{app plus v0}` — same ctors/bucket/flags/label) now separate; a plateau test proves the key still saturates (≤ 12 distinct keys over 40 varied terms).

**Task 2 — SeedPool crossover.** New `Antigen.Generators.SeedPool`: loads **closed** `:typed_term` seeds indexed by their kernel-checked type, exposes them as fillers. `:mutant_term` seeds are excluded (their `type` is a nominal fault-site goal the term does not inhabit); closedness uses the kernel's own `Cure.Core.Term.closed?/1`. Wired opt-in into `gnat` via a process-scoped pool — with no pool installed (every existing test) `gnat` is byte-identical to before. Quarantine-clean (no sampling-backend literal).

**Task 3 — health-adaptive rounds.** `Runner.explore/1` gains a `bias:` opt: `bias: false` (default) issues exactly **one undivided `draw`** (spec §4 — `take` is not composable); `bias: true` runs `round_size` batches, stamps per-group health, and reweights `default_gen`'s 11-branch mix by challenge-KIND **group** (T = branches 4–6,9–11; M = 7–8; F = 1–3 never bumped). A guard test pins `default_gen`'s branch count/order so a future reorder fails loudly. `mix antigen --bias` installs the CLI path + the seed pool.

## Execution catch

Beyond the two review stages, execution caught one more proven-wrong test: the bias:false regression guard asserted `r.discards`, a key `explore/1` has never returned (it exposes `health.discard_rate`) — corrected to the real return shape (stated explicitly, per the test-immutability exception).

## Verification

```
Full suite: 2568 passed, 0 failures  (+10 over baseline)
--count 800 sanity (tmp corpora, 0 infections both):
                     baseline   --bias
  binder_usage         0.91      0.93
  reduction_activity   0.64      0.69
  seeds banked         63        80     (+27%)
  conv accept          200       228
```

Directed generation measurably lifts diversity/activity and banks more distinct seeds at equal count — the intended effect. (0 infections at 800 is expected; the payoff is depth per token on longer hunts.)

## Non-goals (documented, deferred)

- Grey-box kernel-branch instrumentation (needs TCB edits — separate operator-reviewed run).
- Open-term splicing / kernel-call type matching (closed-only + syntactic equality this run).
- Finer-than-group reweighting; Group-F health metrics.

## Next

Run B (new invariant assays) proceeds on this branch.
