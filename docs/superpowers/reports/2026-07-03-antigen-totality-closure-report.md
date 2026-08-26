# Antigen V5 — Totality-Closure Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot via `/loop` (autonomous continuation)

Fourth phase of the untrusted-machinery initiative (task #66), after V3/V1/V2. Tests
the **untrusted totality-closure driver** `Cure.Elab.TotalityClosure` — the module
that decides *which* type-level functions must be certified total and submits each
to the trusted kernel. No `Cure.Core.*`/`Cure.Elab.*` edits, no `:meck`, no new dep.

## The framing decision — driver, not decision procedure

Type-level non-termination is a **logical-inconsistency** hole. But the per-function
totality *decision* (`Certificate.terminating?/3`) is already covered by the
existing `totality/diverging` + `totality/terminating` assays, and
`Kernel.validate_certificate` is trusted TCB. V5's new, uncovered surface is the
**driver** around them:

- `type_level_fns/1` — the untrusted transitive-closure walk over type positions.
- `certify_type_level/1` — the end-to-end driver folding `validate_certificate`
  over that closure.

## What shipped — two assays

| id | property | oracle |
|---|---|---|
| `totality_closure/soundness` | diverging-in-type-position ⟹ rejected | known label |
| `totality_closure/completeness` | `type_level_fns ⊇` independent reachability | independent walk |

- **V5a (soundness, end-to-end, adversarial):** a by-construction diverging `:loop`
  placed in a *type position* (family index or ctor `result_indices`) must be
  rejected by the whole driver. Strictly stronger than the existing per-function
  assay — it exercises the **closure-reachability + submission** path, catching a
  driver that *misses* the diverging function (never submits it → silent `{:ok}`).
- **V5b (completeness, intrinsic):** `type_level_fns(env)` must be a superset of an
  Antigen-owned independent type-position reachability walk (the V1/V2
  independent-oracle tactic), built over the **full `Cure.Core.Term` taxonomy
  including `{:prim, op, args}`** — which the engine's own `collect/1` omits.

Plus `Antigen.Generators.ClosureEnv` (fixed catalogs of pre-built `%Env{}`) and
`assay_module/1` dispatch for the two ids.

## Result of running it

**The driver is sound on the whole catalog** — every soundness and completeness
entry re-checks clean under the real ops (Task 3's "whole catalog" test is green).
The real `certify_type_level` genuinely rejects a diverging `:loop` in both a
family-index and a ctor-result-index type position, and certifies the all-total
control env. No infection surfaced; the four negative controls (unconditional-`{:ok}`
certify, error-on-total certify, empty `type_level_fns`, dropping-callee
`type_level_fns`) each infect, and the isolated `:prim` unit test confirms the
independent walk catches `collect/1`'s blind spot.

## The hardest correctness risk — cleared before code

V5a could have **passed for the wrong reason**: `certify_type_level` routes through
`validate_certificate → check_def`, which requires a `{:data,…}`-typed def's family
registered. A naive family-free env would make `check_def` crash with
`{:unknown_family}` *before* the divergence check ever runs — the reject baseline
would go green without exercising the property. Spec review caught this and fixed
the construction to `{:int_type}`-only (`loop = λx. loop x`, no family needed); plan
review then **traced the full path end-to-end against source** and confirmed the
rejection is specifically `Certificate.terminating?` returning `false`. Execution
confirmed it empirically (all baselines green on first GREEN run).

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Spec | V5 driver-focused two-family design | `<spec>` |
| 1 — Spec review (Sonnet) | 6 passes; **fixed the "passes for the wrong reason" env trap** (`{:int_type}`-only construction); required the V5b walk use the full Term taxonomy (not `collect/1`'s `:prim`-blind clauses); `:loop` atom-interning | `5469697` |
| 2 — Plan | 4-task TDD plan (4 reconciliations) | `e21977b` |
| 3 — Plan review (Sonnet) | 5 passes; **traced the reject baseline end-to-end and confirmed it rejects for the right reason**; added the `:total_env_not_certified` negative control; corrected `@known_atoms` overstatement | `efd902c` |
| 4 — Execute (Opus, TDD) | red → green per task, ghost-authored | `0827eb9`, `5a88b76`, `d28e074` |
| 5 — Verify | full suite green; quarantine clean | (this report) |

### Per-task execution (Stage 4)

1. **`0827eb9`** — `totality_closure/soundness` (reject + accept clauses). Green 5/5 — the critical end-to-end rejection confirmed empirically.
2. **`5a88b76`** — `totality_closure/completeness` + independent `__reachable__/1` walk (full taxonomy incl. `:prim`). Green 10/10.
3. **`d28e074`** — `ClosureEnv` catalogs + dispatch + `:closure_env` kind + `@known_atoms`. Green 12/12 — whole catalog clean.

## Verification

- **Full suite (single authorized run):** `2691 passed` (3 doctests, 2688 tests),
  0 failures — +12 from V2's 2679.
- **StreamData quarantine:** `architecture_test.exs` green (constraint pre-banked;
  never tripped).
- **Working tree:** clean (test-run seed side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Boundaries

V5 **finds** unsound closure behavior; it does not fix any (none surfaced). Curated
fixed catalog, not a random env fuzzer. V5 does **not** duplicate the existing
`totality/*` assays (per-function decision) nor test the trusted
`Kernel.validate_certificate`. The clean completeness catalog deliberately avoids a
`:prim`-nested type-position global (whether `collect/1`'s `:prim` omission is a real
hole or by-design is out of V5's scope to adjudicate — the independent walk *can*
catch it, exercised in isolation). V5's incompleteness direction (a total function
the closure refuses, or an over-approximation) is out of scope. No SMT (V6).

## Next phases (umbrella roadmap, task #66)

- **V4 erasure/relevance**, then **V6 SMT lint**.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
