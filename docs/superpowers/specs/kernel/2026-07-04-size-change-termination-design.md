# Size-Change Termination Certificate (#14) — Design

**Layer:** K (TCB — `lib/cure/core/certificate.ex`, the module the "total" guarantee rests on).
**Approval:** pre-approved under the broadened TCB blanket (aligns with Idris `Core/Termination/SizeChange.idr` / Agda `Termination/*`); full verification gate still required. No design gate.
**Kind:** assurance, not reach — NOT oracle-measurable (both Cure and Idris already *accept* these programs; the gap is that Cure elaborates them *uncertified*, so δ never unfolds them). Tested via **Antigen**, not the differential oracle.

## Problem

`certificate.ex terminating?/3` today certifies a self-recursive global only when there is a **single fixed argument position `p`** that is a structural subterm of the `p`-th parameter in *every* self-call (`Enum.any?(0..arity-1, fn p -> guarded?(...) end)`, lines 64-68). Multi-argument functions where **no single position decreases in every call** — Ackermann, lexicographic descent, permuting/swap descent (`f(S x,S y)=f(y,x)`), course-of-values — are therefore **rejected** (accepted by the elaborator, but not certified total → never δ-reduced during conversion). Idris/Agda certify them via the size-change principle (Lee–Jones–Ben-Amram, doi:10.1145/360204.360210).

Empirically pinned by oracle cluster `lexterm` (all `same`/accept): lex01 Ackermann, lex02 mutual even/odd, lex03 acc-grows, lex04 swap-SCT, lex05 course-of-values fib. These *elaborate* today; #14 makes the certificate *prove them total*.

## Algorithm (port of Idris SizeChange.idr, scoped to single-function self-recursion)

`SizeChange = Smaller | Equal | Unknown`, ordered `Smaller < Equal < Unknown` for the semiring:
- **multiply (path composition, ∘):** `Unknown` absorbs (any ∘ Unknown = Unknown); `Equal` is neutral; `Smaller ∘ Smaller = Smaller`; `Smaller ∘ Equal = Equal ∘ Smaller = Smaller`. (Take the *stronger* of Equal/Smaller along a path unless broken by Unknown.)
- **add (choosing between parallel arcs / matrix mult sum):** keep the *strongest* (`Smaller` beats `Equal` beats `Unknown`).

**Change matrix** for a self-call `f(y₀ … y_{k-1})` inside `f`'s body, relative to params `x₀ … x_{k-1}`: entry `M[i][j] ∈ SizeChange` = relation of call-arg `yᵢ` to param `xⱼ`:
- `Smaller` if `yᵢ` is a variable in the `smaller`-set derived from matching on `xⱼ` (reuse `subterm_scrutinee?` / field-tracking already in `guarded_node?`),
- `Equal` if `yᵢ` *is* `xⱼ` (same de Bruijn var, unmatched), **OR `yᵢ` is a constructor application that EXACTLY reconstructs the form `xⱼ` was matched against in the current branch** (reconstruct-equal — see below),
- `Unknown` otherwise.

This reuses the existing de Bruijn `root`/`smaller` tracking across binders (`{:case,…}` branches add fields; `shift` on binder entry) — but generalised from "one root at position `p`" to "all `k` parameters tracked simultaneously", so the matrix's `j` column is per-parameter.

**Reconstruct-equal (required for Ackermann / course-of-values, ADDED after the Stage-4 soundness escalation).** Ackermann's inner call `ack(S m, n)` passes `S(m)` — a *rebuilt constructor*, not the variable `a` — in the argument position that must stay size-equal for the lexicographic order. This is exactly what Idris (`SizeChange.idr`, size info from the case tree) and Agda (structural order) do to certify Ackermann. Soundness: in the branch where `xⱼ` matched pattern `C(f₀…fₘ)`, `xⱼ` is *definitionally* `C(f₀…fₘ)`, so a call-arg **syntactically identical** to that reconstruction genuinely equals `xⱼ` → `Equal` is exact, not over-claimed. A non-matching or larger form (e.g. `S(S(m))` when `xⱼ` matched `S(m)`) does NOT match and stays `Unknown` (sound — never claim ≤ for a possibly-larger term; NEVER assign `Smaller` from reconstruction). Implementation: track per-parameter the constructor form it was matched against (alongside `smaller`/`root`), shifted across binders identically; assign `Equal` on exact syntactic match in the current frame.

**Transitive closure:** collect the self-call matrices `{M₁ … Mₙ}`; close under composition (`Mᵢ ∘ Mⱼ`) to a fixpoint (worklist, dedup by matrix equality — the `SCSet` of Idris, here a single-function set of `k×k` matrices).

**Certificate condition (`findNonTerminatingLoop`):** the function is **non-terminating** iff some matrix `M` in the closure is **idempotent** (`M ∘ M == M`) AND has **no strictly-decreasing diagonal** (no `i` with `M[i][i] == Smaller`). Certify total iff **every** idempotent loop has a `Smaller` on its diagonal.

## Soundness obligations (why this is safe to put in the TCB)

- **Conservative direction preserved:** `Unknown` and rejection are always sound; a matrix over-approximates (never claims `Smaller`/`Equal` it can't prove from structural subterm tracking).
- **Strictly generalises the current check:** a single fixed decreasing position `p` yields an idempotent loop with `M[p][p]=Smaller`, so everything certified today stays certified.
- **Mutual recursion stays conservatively rejected** (`mutually_recursive?/3` short-circuits before the size-change check) — cross-function SCT is out of scope (#13 row; its soundness hole is already closed). Only single-function multi-arg is added.

## Verification gate (full TCB run)

1. **Red→green unit tests** (`test/cure/core/`): Ackermann / swap / lexicographic certify total; a genuinely non-total multi-arg control (`loop(a,b)=loop(S(a),S(b))`, all-`Equal`/`Unknown` idempotent loop, no decreasing diagonal) is rejected. Include the current single-position cases (no regression).
2. **New Antigen antibody** (size-change): must-eventually-accept a lexicographic function AND must-reject a non-total multi-arg control; proves the change terminates (the closure is finite — `k×k` matrices over a 3-element lattice) and equates no distinct normal forms (certificate is a boolean gate on δ, not a reduction rule, so NF-preservation is via "no *new* global becomes δ-reducible that wasn't total").
3. **Full Antigen suite** green.
4. **Full test suite** green.
5. **Adversarial verify** of the soundness argument (idempotent-loop condition = LJB principle; over-approximation only).

## Non-goals
- Mutual / cross-function size-change (call graph through sibling globals — Idris `addFunctions`). Deferred; #13 keeps it conservatively rejected.
- Non-variable **strictly-decreasing** arguments (a call-arg that is smaller than a parameter but not a bare subterm variable — the cases Idris needs `assert_smaller` for). Only reconstruct-**equal** (size-preserving) non-variable args are handled; genuinely-smaller non-variable args stay `Unknown` (sound incompleteness). Higher-order recursion also out.
- Non-variable decreasing arguments, higher-order recursion (Idris also needs `assert_smaller` for many of these).
- Any oracle probe — this is Antigen-tested. `lexterm` fixtures already pin the elaborator-acceptance side.
