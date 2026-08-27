# Stdlib Dependent-Type Claims Audit

> Historical audit, now resolved. Its `Std.Equal` runtime-token and classic
> checker findings describe the pre-0.34 state. Current proof equality is the
> kernel-recognised inductive `Std.Equivalent.Equivalent` family with
> `reflexive`; `Std.Proof` elaborates through the dependent pipeline. See
> `docs/PROOFS.md` and `docs/STDLIB.md`.

This note records stdlib-facing APIs and documentation that currently claim,
imply, or rely on dependent typing without being checked by the trusted
dependent kernel.

The current compiler routes a module through `Cure.Elab`/`Cure.Core` only when
the parsed AST contains an `indexed type` declaration. Stdlib modules listed
below do not use `indexed type`, so their dependent-type claims are handled by
the legacy checker, runtime conventions, documentation, or not at all.

## Fixed Claims

### `Std.Vector`

Source: `lib/std/vector.cure`

`Std.Vector` has been migrated from the old tuple-backed API to a real indexed
family checked by the dependent kernel:

```cure
indexed type Vector(a: Type, n: Nat) where
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The current trusted API includes:

- `empty() -> Vector(a, Z)`
- `prepend(x: a, xs: Vector(a, n)) -> Vector(a, S(n))`
- `append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n))`

The erased runtime representation is the constructor shape `:empty` and
`{:prepend, head, tail}`; the `a`, `m`, and `n` arguments are compile-time-only.
`Nat` is defined separately in `lib/std/nat.cure`.

## Incorrect Or Unsupported Claims

### `Std.Equal`

Source: `lib/std/equal.cure` -- this module has since been removed entirely
(folded into `Std.Equatable`; see `lib/cure/migrate/rules/removed_module.ex`).
The description below records what it looked like before removal.

`Std.Equal` used to document `Eq(T, a, b)` proofs, erased equality values, and
rewrite behavior. The exported functions returned plain `Atom`:

- `refl(_x: T) -> Atom`
- `sym(_eq: Atom) -> Atom`
- `trans(_p: Atom, _q: Atom) -> Atom`
- `cong(_f: T -> U, _eq: Atom) -> Atom`

The stdlib comments marked this as a legacy equality-token API. The runtime
value was always `:cure_refl`, and there was no per-call kernel proof
validation in this module.

### `Std.Proof` (resolved)

Source: `lib/std/proof.cure`

`Std.Proof` used to contain law-shaped definitions returning `Eq(...)`-looking
types, checked only by the legacy checker's proof-shaped-return-type rule
rather than validated in the trusted kernel (examples formerly included
`plus_zero(_n: Int) -> Eq(Int, n, n)`, `zero_plus`, and a "commutativity" law
`plus_comm(_a: Int, _b: Int) -> Eq(Int, a, a)` that was weaker than its name
suggested).

The module has since been rewritten. Every function --
`plus_zero_right(n) -> Equivalent(Nat, plus(n, Z), n)`,
`plus_succ_right(m, n) -> Equivalent(Nat, plus(m, S(n)), S(plus(m, n)))`, and
`plus_comm(m, n) -> Equivalent(Nat, plus(m, n), plus(n, m))` -- is typed with
`Std.Equivalent.Equivalent` and proved by induction over `Std.Nat`, closing
each case with `reflexive`/`rewrite`. These are proof-checked by the trusted
dependent kernel, not merely proof-shaped.

### `Std.CRDT`

Source: `lib/std/crdt.cure`

`Std.CRDT` used to claim that CRDT merge laws were asserted in companion
`Std.Proof` obligations emitted by `lib/std/crdt.cure` when re-checked. The
source comment now says the runtime implementation is intended to satisfy those
laws, but no trusted Core proof obligations are emitted yet.

## Borderline: Real Refinements, Not Kernel Dependent Types

### Refinement types (`Std.Refine`)

Source: `lib/std/refine.cure`

The refinement-type aliases (`NonZero`, `Positive`, `Negative`,
`NonNegative`, `NonPositive`, `Percentage`, `PositiveFloat`, `Probability`,
...) are back, no longer SMT-backed. `{x: T | condition}` is now an ordinary
kernel-checked dependent pair (`Sigma`-backed): `refine/4` pairs a value with
compiler-checked evidence of the predicate, and `refined_value/3` /
`refinement_proof/3` project the value and its evidence back out. There is no
solver involved and no separate SMT-backed refinement-subtype checker, so this
is a trusted-kernel dependent type after all; this entry is kept only to
record that the earlier removal described in prior revisions of this document
was later reversed.

## Routing Implication

The dependent-kernel handoff now routes the supported surface through Core:
indexed types, typed erased parameters, `Sigma(...)`, pair literals, and pair
projections. It still does not route public `Eq(...)`/`refl`/`rewrite` or proof
containers as trusted proofs, because that Cure source elaboration is not
implemented yet.
