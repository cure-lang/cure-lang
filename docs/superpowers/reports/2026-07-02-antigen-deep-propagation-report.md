# Autopilot completion report — Antigen deep-propagation (sub-project A of "deep injection")

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — the run stayed on this branch per operator instruction (no separate worktree cut; see the `autopilot-worktree-preference` memory).
**Status:** complete. Full suite green — **2291 passed, 0 failures** (3 doctests, 2288 tests; +7 over the pre-deep 2284). **Not merged** — operator merges when ready.

Closes the v1 limitation recorded in the mutation-corpus report §"Accepted v1 limitation": v1 faults sat at their scaffold root, so the corpus never tested whether the kernel correctly **propagates a rejection up through many nested checked positions**. This buries each v1 fault under `D` nested well-typed checked contexts so `infer` must thread its rejection up `D` distinct error-propagation paths.

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Design approved interactively (both sub-projects A+B; A first). Probed all wrappers reject at depth; established no-binder-over-hole constraint | `03650f3` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | Converged 8 passes (7–8 clean); 4 findings — biggest: **legacy banked-seed backward-compat** (7 v1 seeds lack `depth`/`wrap_path` → defensive `Map.get` required), TDD mandate, metric scoping, "Extend" vs "Create" | `57a…` (spec harden) |
| 2 — Plan (writing-plans, inline) | 6-task TDD plan; **probed a mixed deep stack against the live kernel** and caught the contamination flaw (below) before writing | `0e3d5b0` |
| 3 — Plan review (Sonnet) | Converged 4 passes (3 clean); 1 finding (tests-immutable-once-green rule). **Independently validated the 6→5 wrapper deviation** by tracing `kernel.ex` | `…` (plan harden) |
| 4 — Execute (Opus, strict TDD) | 5 tasks, red→green→commit each | `d7e94ae`…`6198fb6` |
| 5 — Verify + report | Full suite green; acceptance explore; this report | — |

## The load-bearing design correction (spec §3: 6 wrappers → 5)

Planning probed a **mixed deep wrapper stack** against the live kernel and found the spec's 6-wrapper set produced *contaminated* deep mutants: the spec's `:ctor_vec` wrapper produces a `Vec`, so the next layer (which expects a `Nat`) becomes **independently** ill-typed and `infer` rejects it for a wrapper-internal type error — **not** because the buried fault propagated. Such a mutant is still `{:error,_}` (so the assay never notices), but it tests *nothing* of deep propagation — it would give false confidence that "we tested to depth 8."

Fix: use the **5 `Nat→Nat` wrappers** (`:app_arg, :ctor_nat, :case_scrut, :case_branch, :pair`), which compose so that every stack is **well-typed except at the innermost hole**. The proof is a new **uncontaminated-control test**: the same wrapper stack around a *well-typed* `Nat` inner must `infer`-**ACCEPT** — so the rejection of the fault-filled stack is provably fault-propagation-driven. `:ctor_vec`'s dependent-ctor-arg path is not lost: it is already exercised at the **base** of every v1 `:index_mismatch`/`:ctor_arg` mutant (those faults *are* `vcons` terms checked through `check_ctor_app_rec`). The Sonnet plan reviewer independently traced the kernel and confirmed all three claims.

## What was built

- **`Mutation.deepen/3`** — `Gen` of `{deep_term, wrap_path}`; wraps a fault in `D` `Nat→Nat` checked layers (`wrap_path` innermost-first, `length == depth`). `wrappers/0`, `max_depth/0` (=8).
- **`mutant/0`** draws `D` uniformly in `0..@max_depth` and records `fault.depth` / `fault.wrap_path` (shallow v1 output = depth 0; strict generalization).
- **`Challenge.@known_atoms`** += the 5 wrapper kinds + `:depth` + `:wrap_path`, so a deep `fault` map rides safely through `binary_to_term [:safe]`.
- **`Runner.mutation_metrics/1`** += `max_depth` + `wrap_diversity`, computed over **every** mutant (survivors included), read defensively for legacy seeds; `mutation_stamp/1` + health line gate on both floors (≥4 depth, ≥4 of 5 wrappers).
- **4 deep `:mutant_term` seeds** banked (depth ≥4, covering all 5 wrapper kinds) + a static-replay meta-test enforcing the floors on the banked corpus.

## Two guard tests that keep the deep corpus honest

1. **Uncontaminated control** — a well-typed `Nat` inner must `infer`-ACCEPT through the identical wrapper stack (proves rejections are fault-driven, not wrapper-internal). This is what makes "deep propagation" a real test rather than a claim.
2. **Genuine file-decode red for atom interning** — the Task 1 red test decodes an out-of-source base64 blob (wrapper atoms appear only in opaque bytes), so `[:safe]` genuinely fails without `@known_atoms`. The in-source round-trip test cannot be this — its own literals pre-intern the atoms (the exact v1 false-green that let the v1 key-atom bug slip to corpus-replay).

## Acceptance run (`mix antigen --count 500`)

```
antigen health[mutant_term]: reason_diversity=7 max_depth=8 wrap_diversity=5 survivors=0 → healthy
antigen health[typed_term]:  binder_usage=0.95 reduction_activity=0.33 fuel_exhausted=0 discard=0.0 → healthy
antigen: 0 infection(s), 54 seed(s) banked
```

All **7** base fault kinds × depth to the **8** ceiling × all **5** wrapper paths, **0 survivors** — the kernel correctly propagates every deep rejection up to depth 8 across all five error-propagation paths (`app_arg` / `ctor` / `case_scrut` / `case_branch` / Σ-component). A survivor here would have been a genuine error-swallowing bug; there were none.

## Follow-ons queued

- **Sub-project B — conversion-at-depth** (its own spec → plan → execute cycle, next): reuse this depth machinery but swap the fault to a **well-typed-but-wrong-type** subterm at a hole whose expected type the kernel must **compute** (e.g. `Vec (plus n m)`), exercising NbE/conversion at depth. Needs a `Cure.Core.Term` seam. Structurally unreachable by A (A's fault dies at its own `infer` before any expected type is consulted), so A does not subsume it.
- **Human-readable corpus terms + fault provenance** (operator-requested, deferred; its own spec/plan).
- **Value-level post-shrink + `ChoiceSeq` backend** — gated behind real antibodies.

## Next

Operator review + merge of `autopilot/antigen-tier-b` (now carries Tier B + lazy generator + ChoiceSeq reference spec + mutation corpus + this deep-propagation layer).
