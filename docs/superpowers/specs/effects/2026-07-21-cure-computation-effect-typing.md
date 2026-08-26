# Cure Computation and Effect Typing

**Status:** Normative design specification  
**Parent:** `2026-07-21-lean-verified-middle-end-design.md`

## 1. Core judgments

Cure separates values from computations:

```text
Γ ⊢v v : A
Γ ⊢c c : A ! ρ [ι]
```

`A` is a value type. `ρ` is a qualitative effect row. `ι` is optional indexed
or refinement information. Computations are never normalized as values by the
dependent kernel.

## 2. Value types

The initial fragment contains base types, products, sums, functions, and
named data types. Dependent functions, dependent pairs, and refinements are
represented but admitted incrementally.

Types may depend only on a restricted `IndexTerm` language of total,
effect-free, ground values: variables, literals, constructors, projections,
and certified pure primitives. A type may not contain an unevaluated
computation, a lambda/recursive closure, an effect invocation, or a runtime
Flow frame.

## 3. Computation types

```text
Comp(A, ρ, ι)
```

Examples:

```text
return v       : Comp(A, ∅, 1)
perform op     : Comp(B, {op}, ιop)
```

The row and index are separate. A qualitative label says what operation may
occur; an index can describe cost, protocol state, ownership, temporal facts,
or a refinement summary.

## 4. Effect rows

```text
ρ ::= {ℓ1, ..., ℓn | α}
```

Rows support normalization, inclusion, union, and checked subtraction. Labels
are nominal and categorized as:

```text
EffectDecl := {
  category : primitive | abstract | higher-order | suspend | concurrency | foreign,
  handling : open | sealed,
  control  : ordinary | suspending
}
```

Primitive and abstract labels share the namespace so that effect closure can
be computed uniformly. Category, sealing, and suspension are independent
properties. A sealed primitive or sealed suspension cannot be removed by an
ordinary user handler.

## 5. Typing rules

Selected rules:

```text
Γ ⊢v v : A
────────────────────────────
Γ ⊢c return v : A ! ∅ [1]
```

```text
Γ ⊢c c₁ : A ! ρ₁ [ι₁]
Γ, x : A ⊢c c₂ : B ! ρ₂ [ι₂]
────────────────────────────────────────────
Γ ⊢c let x = c₁ in c₂ : B ! (ρ₁ ∪ ρ₂) [ι₁ ⋄ ι₂]
```

Initially, `ι₂` may not depend directly on the runtime result of `c₁`.
Refinement substitution can remove that dependency when a checked value
relation proves the required equality or predicate.

```text
Γ ⊢v f : (A → Comp(B, ρ, ι))
Γ ⊢v v : A
────────────────────────────────────
Γ ⊢c apply f v : B ! ρ[v/x] [ι[v/x]]
```

## 6. Handlers

A handler has handled labels `H`, a return clause, operation clauses, a mode,
and a continuation ownership policy.

```text
Γ ⊢c c : A ! ρ [ι]
handler h handles H and returns B ! ρ' [ι']
H ⊆ ρ
────────────────────────────────────
Γ ⊢c handle c with h : B ! ((ρ \ H) ∪ ρ') [ι'']
```

The rule is admissible only if every handled operation has a compatible clause,
the return path is typed, and sealed effects are not removed. Deep versus
shallow behavior is a semantic field, not an optimization choice.

## 7. Higher-order and latent effects

An operation receiving or storing a computation must record its latent
computation type separately from the caller's immediate effects:

```text
runLater : Deferred(Comp(A, ρ, ι)) → Comp(B, {runLater}, ι')
```

`Deferred(Comp(A, ρ, ι))` is a computation-layer value carrying a latent row;
it does not perform `ρ` at the point of scheduling. The operation cannot be
treated as first-order merely because the computation is represented by a
closure. Callbacks, process children, supervisor bodies, resource brackets, and
deferred device work retain latent rows for deployment closure checking.

## 8. Suspension

`Suspend` is initially an effect with category `suspend`, handling `sealed`, and
control `suspending`. It records the operation, payload, result type, owning
scheduler, and continuation policy. User code may
name an abstract operation that eventually lowers to suspension, but it cannot
forge a scheduler continuation or remove `Suspend` by an ordinary handler.

## 9. Foreign operations

Every foreign operation declares:

```text
name, argument types, result type, effect row,
capability, failure behavior, ownership/resource behavior
```

An FFI call without a declaration is rejected. Deployment closure checks all
reachable foreign capabilities.

## 10. Lean implementation requirements

Lean must provide checked operations for:

- row union, inclusion, and subtraction;
- effect-category validation;
- dependent substitution over value terms;
- computation typing;
- handler effect accounting;
- latent-effect propagation;
- deployment effect closure.

The first implementation should use explicit derivations or intrinsically typed
IR values after JSON validation. Raw decoded syntax must not be accepted by
lowering functions.

## 11. Initial restrictions

The first theorem-bearing implementation supports first-order effects,
one-shot continuations, sealed primitive effects, and conservative dependent
sequencing. It defers unrestricted multi-shot handlers, arbitrary answer-type
modification, effectful dependent indices, and full higher-order handler
composition.

## 12. Consolidated decisions from earlier effect designs

This specification incorporates the surviving decisions from the earlier
effect documents:

- surface `!` annotations may remain as syntax or diagnostics, but computation
  typing and effect rows are authoritative;
- the old inert `Effect(T)` former is implementation history, not the complete
  semantic model;
- effects-as-data/free-monad interpretation is not required for the first
  implementation;
- computation values, latent effects, handlers, and suspension are distinct
  concepts and must not be collapsed into one opaque runtime wrapper;
- unresolved open rows, sealed primitive effects, and effectful dependent
  indices remain subject to the restrictions above.

The deferred-work ledger for this model belongs in the implementation ledger
of the Lean middle-end and the multiple-IR architecture, rather than in a
second competing `Effect(T)` specification.
