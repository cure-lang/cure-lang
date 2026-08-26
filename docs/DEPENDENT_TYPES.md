# Cure Dependent Types Guide

Every accepted Cure program follows the dependent path: surface syntax
elaborates to `Cure.Core`, `Cure.Core.Kernel` validates it, and quantitative
erasure removes compile-time-only evidence before BEAM emission. The former
`Cure.Types.*` classic pipeline has been deleted.

## Indexed families

Parameters are uniform across constructors; indices may vary:

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The checker preserves constructor index equations. A match on `Vector(a, n)`
therefore refines `n` independently in each branch, and a constructor whose
indices cannot unify is impossible.

Empty families use `= |`; a single constructor needs no leading bar:

```cure
type Void = |
type Wrapper = Wrap(Int)
```

## Dependent functions and implicits

A result type may mention explicit arguments:

```text
fn append(
  {a: Type},
  {m: Nat},
  {n: Nat},
  xs: Vector(a, m),
  ys: Vector(a, n)
) -> Vector(a, plus(m, n))
```

Braced parameters are implicit. The elaborator solves them from explicit
arguments, postponing constraints when necessary so argument order does not
decide typability. Grade-`0` arguments are checked but erased and do not change
the emitted BEAM arity.

## Sigma types

`Sigma(x: a, b)` pairs a witness `x` with a second component whose type may
mention that witness:

```text
fn pack(d: Dec) -> Sigma(x: Dec, Dec) = %[d, d]
fn recover(p: Sigma(x: Dec, Dec)) -> Dec = p.2
```

Sigma introduction uses the tuple surface and dependent projections use `.1`
and `.2`. Runtime pairs emit as ordinary BEAM tuples after evidence erasure.

## Definitional equality

The kernel decides type equality with normalization by evaluation. Beta
reduction, projections, dependent-case iota reduction, and certified global
definitions participate automatically. A global definition unfolds only when
its size-change totality certificate validates, preventing conversion from
running arbitrary nonterminating code.

## Propositional equality

`Std.Equivalent` declares the inductive identity type:

```cure
@builtin(:eq)
type Equivalent(a: Type) indices (x: a, y: a)
  reflexive : Equivalent(a, w, w)
```

`reflexive` closes goals whose endpoints are definitionally equal. Matching an
equality proof against `reflexive` identifies the endpoints, which is enough to
implement transport, symmetry, transitivity, and congruence as ordinary Cure
functions. Primitive `Eq`, `refl`, and `rewrite` Core nodes are retired.

`Equivalent` is proof equality. `Std.Equatable` is a separate runtime
comparison interface returning `Bool`.

## Impossible and forced patterns

When index unification proves that a constructor cannot inhabit the scrutinee
type, the branch may be written `impossible`. A forced (`.`) pattern records
that a value is already determined by surrounding indices. These forms are
checked rather than trusted.

## Quantitative binders

Binders carry grades from `{0, 1, ω}`, with affine usage available:

- `0` values are compile-time-only;
- `@linear` values are consumed exactly once;
- `@affine` values are consumed at most once;
- `ω` values are unrestricted.

The kernel rejects returning, scrutinizing, or reusing erased data at runtime.
This same discipline checks typed OTP capabilities before they are erased or
lowered.

## Holes

`?name` and `?_` create typed holes. Tooling reports the expected type and local
context, but final emission rejects any reachable definition that still
contains a hole.

## Trust boundary

Strict positivity, totality certification, conversion, dependent case, and
usage checking live inside the trusted kernel. `postulate`, bodyless `@extern`,
and `believe_me` are explicit axiom roots and are recorded in the trust ledger:

```bash
cure audit trust My.Module
```

Z3 guard coverage and shadow analysis are useful lint diagnostics but are
outside the trusted kernel and never synthesize proof evidence.

See [Type System](TYPE_SYSTEM.md), [Proofs](PROOFS.md), and
[Kernel](KERNEL.md) for more detail.
