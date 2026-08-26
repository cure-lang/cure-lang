# Autopilot completion report — Antigen ill-typed mutation corpus

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — the run stayed on this branch per operator instruction (no separate worktree cut).
**Status:** complete. Full suite green — **2284 passed, 0 failures** (3 doctests, 2281 tests; +14 over the pre-mutation 2270). **Not merged** — operator merges when ready.

Realizes the **second polarity** of soundness testing (Tier-B report §"Reach left open"): where the `:typed_term` corpus catches *false breakage* (well-typed terms the kernel mishandles), this corpus catches *false acceptance* (ill-typed terms the kernel wrongly admits).

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Design approved interactively (3 forks: construction-guaranteed ill-typedness / generation-time fault injection / rejection-reason diversity floor); spec written + self-reviewed | `6bd18dc` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | Converged 6 passes; 7–8 findings, all code-verified — biggest: `@known_atoms` interning gaps (incl. missing `:Sigma`), universe `j`-bound below `Universe.ceiling()`=2, 4 (not 2) site-restricted operators | `48bc884` |
| 2 — Plan (writing-plans, inline) | 10-task TDD plan; **all 7 operator constructions probed against the live kernel** (verified each rejects under `infer`) before writing | `1d45e94` |
| 3 — Plan review (Sonnet) | Converged 7 passes; added the missing static-replay diversity meta-test (Task 9), corrected an alias collision (`CtxGen`), qualified the raw-tag determinism claim, and documented the §5 "fault burial" property as a genuine v1 limitation | `4a6f8ec` |
| 4 — Execute (Opus, strict TDD) | 10 tasks, red→green→commit each | `b368659`…`f31fb43` |
| 5 — Verify + report | Full suite green; acceptance explore; this report | — |

## What was built

- **`Antigen.Generators.Mutation`** — the 7 fault operators, each a self-contained *checked scaffold* (a minimal well-typed enclosing form wrapping one construction-guaranteed-wrong subterm, with deep well-typed filler drawn from the lazy `Term.gen_term`): `:head_swap`, `:ctor_arg`, `:index_mismatch`, `:app_domain`, `:out_of_scope_var`, `:proj_non_pair`, `:universe`. Plus `mutant/0` (challenge) and `operators/0`/`build/2`.
- **`Antigen.Assays.Mutation`** (`mutation/rejection`) — the inverted assay: `Kernel.infer` `{:error,_}` = correct rejection = `:ok`; `{:ok,_}` = **antibody** (`{:violation, {:accepted_ill_typed, term, fault}}`). Injectable-infer seam for the polarity test.
- **`:mutant_term` Challenge kind** — serialization (with a `fault` provenance map riding safely through `binary_to_term [:safe]`), coverage keying, replay registry.
- **Rejection-reason diversity gate** — `Runner.mutation_metrics/1` buckets *correctly-rejected* mutants by `fault.kind` (not raw kernel tag, which collapses 3 kinds onto `:index_mismatch` and 2 onto `:foreign_ctor`); floor ≥5 of 7. Stamp measures vacuity only; survivors are surfaced separately as infections.
- **Two guard tests that keep the corpus honest:** the construction-guarantee test (every operator's term is `infer`-rejected) and the **kernel-independent** invariant-(b) meta-test (each `fault` carries a decidable witness — head/index/level/scope — checkable without the kernel-under-test).

## Acceptance run (`mix antigen --count 500`)

```
antigen health[mutant_term]: reason_diversity=7 survivors=0 → healthy
antigen health[typed_term]:  binder_usage=0.94 reduction_activity=0.38 fuel_exhausted=0 discard=0.0 → healthy
antigen: 0 infection(s)
```

All **7** fault kinds exercised (max diversity), **0 survivors** — the kernel correctly rejects every ill-typed mutant — both corpora healthy. 7 coverage-deduped `:mutant_term` seeds banked into `test/antigen/seeds.sexp` (one per fault kind).

## Issues found + fixed during execution (none silent)

1. **Fault-map KEY atoms un-interned** — `:kind/:witness/:expected_head/:injected_head` were missing from `@known_atoms`, so banked mutant scaffolds failed `binary_to_term [:safe]` decode. Task 1's unit test passed only because *that test's own source* interns those literals; the corpus-replay structural-integrity test caught the real gap. Fixed by adding the key atoms (the spec's §8 atom-safety rule applies to map keys, not just values).
2. **StreamData quarantine grep** — the literal word "StreamData" in `mutation.ex`'s moduledoc tripped `architecture_test.exs` (the exact class that bit Tier-B). Reworded to "Backend-free".

## Accepted v1 limitation (documented, named follow-on)

Faults sit at each operator's own scaffold root, not buried at arbitrary depth inside a `gen_term`-generated carrier (the spec §5 "buries it in a real, deep surrounding term" property for operator 3). The filler is deep but is always a *sibling* of the fault, never an *ancestor*. So the corpus does not yet exercise whether the kernel correctly propagates a rejection up through many nested checked levels — a distinct bug class. Recorded as a follow-on ("v2: deep-injection variant"), not folded into "preserves every guarantee."

## Follow-ons queued

- **Human-readable corpus terms + fault provenance** (operator-requested, its own spec/plan): inline piece s-expressions + note (drop base64), and inline the `fault` map as a decodable text field so a banked mutation record is hand-debuggable; leave general scaffolds/keys base64. Vars stay positional de Bruijn (documented).
- **Value-level post-shrink + `ChoiceSeq` backend** — this corpus is the precondition (real antibodies to shrink); see the `ChoiceSeq` reference spec's §9 gate.
- **v2 deep-injection** variant of the fault operators (above).

## Next

Operator review + merge of `autopilot/antigen-tier-b` (now carries Tier B + lazy generator + ChoiceSeq reference spec + this mutation corpus).
