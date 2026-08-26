# Autopilot completion report — Antigen Tier B (term generator + differential assays)

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`, cut from `autopilot/transliteration-p0`).
**Status:** complete. Full suite green — **2269 passed, 0 failures** (3 doctests, 2266 tests). **Not merged** — operator merges when ready.

Realizes parity-ledger **#22 / expansion A8** ("the capability jump"): turns Antigen from a known-label regression net into a term-generator producing soundness *evidence*.

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Design approved (via `/autopilot`); spec written | `8d5290f` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | Converged 8 passes, 13 findings fixed; caught a `Conv.conv_within?` Term/Value type mismatch → steered to the kernel's real idiom | `60275a0` |
| 2 — Plan (writing-plans, inline) | 10-task TDD plan with real code against verified interfaces | `751beb1` |
| 3 — Plan review (Sonnet) | Converged 3 passes (2 clean); **biggest catch**: every `Normalise.nf`/`whnf` call omitted `fuel:` → all `:fuel_exhausted` logic would have been dead code (violating locked decision #6). Fixed at 4 sites. (First attempt died on a transient Sonnet 401; checkpointed at `11c422e`, retried to convergence.) | `0dfbc05` |
| 4 — Execute (Opus, strict TDD) | 10 tasks, red→green→commit each | `ba722b3`…`4247a04` |
| 5 — Verify + report | Full suite green; this report; notify | `f909cf6` (ledger) |

## What was built

- **`Antigen.Generators.SigMenu`** — versioned v1 signature menu (`Nat`, `Bd`, indexed `Vec`; certified `plus`/`dbl` via the real `Kernel.validate_certificate/2`), `inhabitable?/2` + `canon/2` totality scaffolding, `rebuild_context/2`.
- **`Antigen.Generators.Context`** — dependent-telescope Γ generator (inner entries may depend on outer, e.g. `Vec(n)` after `n : Nat`).
- **`Antigen.Generators.Term`** — the mode-directed dependent `gen_term(Γ, T)`: check-mode intros + infer-mode eliminations (var, INDIR, plain-app β-redex, `case`, `fst`/`snd`), every semantic side-condition discharged through the kernel's fuel-bounded conversion, canonical-inhabitant fallback for totality. `typed_term/1` + `default_gen/0`.
- **`Antigen.Assays.Term`** — the three differential self-consistency assays: `term/infer_check`, `term/subject_reduction`, `term/normalization`.
- **`:typed_term` Challenge kind** — C2 serialization, coverage keying, replay registry (Runner + `corpus_replay_test`).
- **Health gate** — binder-usage (≥0.60) + reduction-activity (≥0.25) + fuel-exhausted count over the `:typed_term` subset; `:healthy`/`:vacuous` stamp; static-replay meta-test enforcing the floors on the banked corpus.

## Acceptance run (`mix antigen --count 500`)

`antigen health[typed_term]: binder_usage=0.87 reduction_activity=0.31 fuel_exhausted=0 discard=0.0 → healthy` — **0 infections** over the generated stream. Banked `:typed_term` seeds committed to `test/antigen/seeds.sexp` (coverage-deduped, never-pruned).

## Notable deviations discovered during execution (all resolved, none silent)

1. **Data normal-form param/index reshuffle** — the kernel reifies `{:vdata, :Vec, [i]}` with the index in the *params* slot, not *indices*; `SigMenu`/`Term` Vec matches were made position-agnostic (`vec_index/2`).
2. **Eager-generator explosion** — the `Antigen.Gen` DSL builds `frequency` branches eagerly, so the generator tree is exponential in size and the backend feeds sizes up to ~80 (a 305s hang). Fixed with `@max_size 3` (aligned with the spec's "small v1 fragment") plus strict size-decrease and INDIR size-gating.
3. **Non-inhabitable stuck-Vec goals** — `goal_gen` originally offered `Vec(var)` goals with no witness → `canon` returned `nil`; fixed to offer only the exact Vec type of a Vec-typed context variable.
4. **Health-metric honesty** — the constant-motive lam is a type annotation, not a term binder, so it is excluded from binder-usage; binding constructs were restricted to Nat goals (where the Nat predecessor is usable) and biased to reference their binder (`gen_referencing/4`) — this is generator *tuning* to clear the floor, not floor-lowering.
5. **Reduction-activity flakiness** — hovered at 0.26 (floor 0.25); raised the redex-producing rule weights (`@redex_weight 5`) so it clears with margin (0.31, green across 5 seeds).
6. **Replay registry gap** — the plan wired the Runner registry but not `corpus_replay_test`'s parallel map; added the three `term/*` ids so the banked seeds replay.

## Reach left open (follow-up spec, per the Tier-B design §1)

`conversion_termination` / `erasure_preservation` assays; ill-typed mutation corpus; `Backend.ChoiceSeq`; richer menu (Pi/Sigma goals, type parameters); A10's wiring of the *existing* known-label verticals onto the generated stream.

## Next

Operator review + merge of `autopilot/antigen-tier-b`. No sub-projects were deferred (single-spec run).
