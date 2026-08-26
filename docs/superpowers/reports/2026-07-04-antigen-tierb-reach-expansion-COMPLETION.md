# Antigen Tier-B Reach Expansion — Completion Report

**Date:** 2026-07-04
**Branch:** `autopilot/antigen-tier-b` (no auto-merge — operator merges on return)
**Autopilot run:** brainstorm → spec → spec-review → plan → plan-review → TDD execution → verify

## Goal

Extend the reach of the existing Antigen Tier-B term generator (the mode-directed
bidirectional term synthesizer + its three differential self-consistency assays)
along the three "reach left open" axes from the Tier-B capstone: a **richer menu**
(parametric `List(A)`, Π/Σ goals), an **`erasure_preservation`** differential
assay, and **ill-typing mutation operators** for the new type formers.

## Headline outcome: a real kernel (TCB) bug found

The expansion did exactly what Antigen exists to do — the richer menu surfaced a
**genuine non-idempotence bug in the trusted `Cure.Core.Normalise`**: on ~5% of
Π challenges (a lambda closing over context variables through `plus`/`dbl`
unfolding), `nf(nf t) ≠ nf(t)` — the normal form **oscillates with period 2**,
transposing two context de Bruijn indices. This is the **third real bug** the
untrusted-machinery + reach-expansion initiative has found, and the **first in
the trusted kernel**. Full write-up + reproduction:
`docs/superpowers/reports/2026-07-04-antigen-nf-nonidempotence-finding.md`.
Banked as a red-green fixture that flips to `:ok` when the normalizer is fixed;
Π menu seeds withheld until then. **Fix is an open item for the operator** (a
separate, isolated TCB cycle).

## What shipped, per task (commit-by-commit)

| Task | Deliverable | Status |
|------|-------------|--------|
| 1 | `List(A)` parametric family added to the v1 menu (Nil/Cons, `ctor/5` + `result_params`, canon/inhabitable) | ✅ shipped |
| 2 | `List` intro rule + List goal seeds + top-level check-mode wrap in `typed_term/1` | ✅ shipped |
| 3 | Σ goal seed shipped (clean); **Π seeds withheld** (banked nf finding) | ✅ shipped (reduced) |
| 4 | `vcons`'s length witness `n` marked `:erased` (makes `{0,ω}` erasure non-vacuous) | ✅ shipped |
| 5 | `term/erasure_preservation` assay (`nf∘erase ≡ erase∘nf`) + redex-bearing negative control | ✅ shipped |
| 6–8 | Three self-wrapped mutation operators: `pair_component`, `app_result`, `type_param_mismatch`, each with a load-bearing analog-accepted test | ✅ shipped |
| 9 | Full-suite verification gate: **2750 passing**, quarantine clean, corpus expanded (+21 seeds) | ✅ passed |

## Plan corrections surfaced during execution (all fixed in place)

Real TDD caught four defects the plan/review pipeline missed — each a genuine
"the plan's assumption was wrong" case, fixed by asserting the true contract, not
by weakening:

1. **`canon`/`gen_term` soundness tests infer bare check-mode-only terms** — List
   goals yield bare `Nil`/`Cons` (sound but not inferable). Retargeted three
   existing tests to **check-at-goal** (the generator's real contract) rather than
   infer-then-check. (Tasks 1–2)
2. **The nf non-idempotence finding itself** — the headline (Task 3).
3. **`erasure_preservation` used `Context.env/1`** (the de Bruijn value env) where
   `Erase.erase` needs the **`%Env{}` signature** (`Context.signature/1`) to read
   ctor quantities. (Task 5)
4. **`build/2` contract** — the plan's Task 6–8 pseudocode returned bare terms and
   ignored the `deepen` machinery; the real contract is `{Gen.t(), fault_map}` and
   every operator is uniformly deepened. Reconciled: the new operators return the
   proper tuple and are `@self_wrapped` (forced depth 0) so their non-Nat pre-wrap
   isn't contaminated by the Nat→Nat deepen layers. (Tasks 6–8)

## Net menu/assay growth

- **Menu:** `List(Nat)`, `List(Bd)`, `Σ(Nat×Nat)` goal seeds; `List(A)` family;
  `vcons.n` erased. (Π generation retained as an intro rule + unit test; Π *menu
  seeds* withheld pending the kernel fix.)
- **Assays:** a fourth differential assay `term/erasure_preservation`, green over
  600 random samples.
- **Mutation:** 10 operators (was 7) — the three new ones ill-type the Σ/Π/List
  formers, each proven genuine by an analog-accepted test.

## Remaining Tier-B reach items (roadmap, deferred)

- **Fix the `Normalise` non-idempotence** (operator decision) → then re-enable Π
  menu seeds and confirm the trio stays green over Π at scale.
- `Backend.ChoiceSeq` (value-level post-shrink), `conversion_termination` assay,
  A10 broader wiring — untouched by this initiative.
