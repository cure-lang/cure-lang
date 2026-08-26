# Cross-Function / Mutual Size-Change (#13 reach) — Design

**Layer:** K (TCB — `lib/cure/core/certificate.ex`). Builds directly on the landed #14 single-function size-change (`b871b37`).
**Approval:** pre-approved under the broadened TCB blanket (aligns with Idris `SizeChange.idr` `addFunctions` + `CallGraph.idr` / Agda `Termination/CallGraph.hs`+`TermCheck.hs`). Full gate.
**Kind:** assurance/reach — not oracle-measurable (both accept). Antigen-tested + Idris cross-check.

## Problem

Today `terminating?/3` short-circuits ALL mutual recursion to `false` via `mutually_recursive?/3` (sound but incomplete — a well-founded mutual pair like `is_even`/`is_odd` is rejected, never δ-reduced). #13 replaces that blanket reject with actual **cross-function size-change**: the #14 change-matrix / idempotent-loop machinery, generalised from self-calls to **calls to any global in the mutual group**.

## Algorithm (port of Idris `addFunctions` + `findNonTerminatingLoop`)

1. **Mutual group.** Reuse the existing `called_globals`/`reaches?` machinery to find the SCC (the set of globals mutually reachable with `name`). If the group is `{name}` alone, this is exactly #14 (single-function) — unchanged.
2. **Cross-function change edges.** Generalise #14's `build_matrix`: for a call `g(y₀…y_{m-1})` (g in the group, arity m) appearing in `f`'s body (f arity k), build a **non-square** `m×k` matrix `M_{f→g}[i][j]` = relation of g-call-arg `yᵢ` to f-param `xⱼ` — using the SAME `arg_relation` + per-parameter `roots`/`smallers`/`recons` tracking (reconstruct-equal included; it works across the call boundary — a g-call arg that reconstructs f's matched param is `:equal`). Collect edges for EVERY function in the group over EVERY intra-group call (self-calls included — those are the #14 `f→f` edges).
3. **Transitive closure over the multi-function edge set** (the Idris `SCSet`): compose `M_{f→g} ∘ M_{g→h} = M_{f→h}` when g's dimension matches (m). Close to a fixpoint (worklist, dedup by `(f,g,matrix)` equality). Composition is defined only when inner dims agree; skip otherwise.
4. **Certificate condition.** Certify the whole group total iff EVERY idempotent **endo-edge** `M_{f→f}` in the closure (square, `M∘M==M`) has a strictly-decreasing diagonal (`M[i][i]==:smaller`). A single group member with a bad idempotent loop fails the whole group (they're δ-certified together).

## Soundness obligations (TCB)

- **The `d13d718` `diverging_mutual_pair` antibody MUST stay green.** The divergent pair `f→g→f` where neither decreases produces an idempotent `f→f` (and `g→g`) endo-edge with no `:smaller` diagonal → rejected. This flips from "guarded by a conservative short-circuit" to "guarded by the size-change criterion itself" — the antibody is now the PRIMARY soundness witness.
- **Over-approximation unchanged:** entries are `:smaller`/`:equal` only via the #14 `arg_relation` (variable subterm / same-var / exact reconstruct-equal); never over-claimed across the call boundary.
- **Strict generalisation:** a single-function group reduces to #14 exactly (same square self-edges, same check) — no #14 regression. Non-cyclic helpers (`reaches?` returns false) are unaffected.
- **Composition partiality is sound:** only same-dimension composition is defined; a missing composition just omits an edge (can only make the criterion see fewer paths → but every real loop is still generated from the base edges, so no bad loop is missed — the base `f→f`/`g→g` edges and their closure suffice to expose any idempotent divergent loop).

## Verification gate (full TCB run)

1. **Red→green unit tests** (`test/cure/core/`): `is_even`/`is_odd` (mutual, shared arg decreases through the cycle) certifies total; a `ping`/`pong` well-founded pair certifies; the diverging mutual pair (`f b = g b; g b = f (S b)` style, no descent) is rejected. Include a single-function case to prove #14 still holds.
2. **Antigen:** the `d13d718` `diverging_mutual_pair` antibody stays green under the new path; add a mutual-reach antibody (`is_even`/`is_odd` must-eventually-certify).
3. **Full Antigen** + **full suite** green.
4. **Idris cross-check:** `is_even`/`is_odd` are total in Idris (`%default total` accepts); the diverging pair is rejected by Idris — Cure must agree both ways.
5. **Adversarial verify** of the multi-function closure argument (every idempotent endo-loop is generated; over-approximation only).

## Non-goals
- Higher-order / non-variable strictly-decreasing args (same as #14).
- Any `assert_total`/`assert_smaller` escape hatch.
