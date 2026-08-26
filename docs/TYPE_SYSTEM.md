# Cure Type System

## Overview

Cure uses one bidirectional dependent type checker. The pre-0.34 classic
checker and code-generation path have been deleted. Surface programs elaborate
to dependent Core, the small kernel validates that Core, proof/index arguments
are erased according to their quantitative grades, and the remaining program
is emitted as BEAM code.

The type system includes:

- cumulative universes and dependent function (`Pi`) types;
- dependent pairs (`Sigma`) and indexed inductive families;
- definitional equality by normalization;
- inductive propositional equality through `Std.Equivalent`;
- implicit arguments and higher-order pattern unification;
- quantitative `{0, 1, ω}` binder usage;
- structural pattern refinement and exhaustiveness;
- interfaces, implementations, and explicit `requires` constraints;
- union types, a bottom type, and `Any` as a top type in safe covariant
  positions;
- totality certificates governing which definitions may reduce during type
  checking.

## Bidirectional elaboration

Elaboration alternates between:

- **infer** — synthesize a Core term and its type from an expression;
- **check** — elaborate an expression against an expected type.

Expected types flow into lambdas, constructors, holes, blocks, and local
bindings. Implicit constraints may be postponed until later explicit
arguments reveal enough information, so typability does not depend on argument
order.

Declarations receive canonical owner-qualified identities. Imports control
lexical visibility, while module interfaces separately retain qualified
availability. Repeated interface loading is idempotent and does not leak
transitive bare names.

## Universes and dependent functions

`Type`, `Type 1`, and higher universes are cumulative and predicative. A
function result may mention its arguments:

```text
fn append(
  {a: Type},
  {m: Nat},
  {n: Nat},
  xs: Vector(a, m),
  ys: Vector(a, n)
) -> Vector(a, plus(m, n))
```

Brace-delimited parameters are implicit. They are inferred from explicit
arguments and can be grade `0`, so they disappear at runtime.

## Indexed inductive families

`indices` separates uniform parameters from constructor-varying indices:

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

Constructor checking preserves the index equations. Pattern matching unifies
those equations per branch, narrows local bindings, and rejects impossible
constructor/index combinations. `impossible` arms and forced (`.`) patterns
make those proofs explicit.

## Sigma pairs and tuples

`Sigma(name: A, B(name))` pairs a value with a second component whose type may
depend on it. Ordinary tuples use matching value/type syntax:

```text
let pair : %[Int, Bool] = %[42, true]
```

`%[A, B, ...]` is the canonical tuple type. Legacy `(A, B)` is accepted only
for migration and emits `E086 / E-TYPE-TUPLE-PAREN`; grouped types and function
domains are unaffected.

## Primitive and structural types

Visible primitive homes include `Std.Int`, `Std.Float`, `Std.Char`,
`Std.Atom`, and `Std.Binary`. `String` is the transparent alias
`List(Char)`. `Option(t)` and `Result(t, e)` are ordinary inductives imported
from `Std.Option` and `Std.Result`.

`Map(k, v)` is parameterized. Record declarations introduce nominal product
types, while tuple and map types remain structural.

## Subtyping and `Any`

`Never` is the bottom type and `Any` is the top type. Widening propagates only
through positions declared safe:

- `List(Int)` can satisfy `List(Any)` because list elements are covariant;
- function inputs remain contravariant and outputs covariant;
- invariant or dependent positions reject widening that would lose an index or
  permit an unsafe write;
- `Pid(inbox)` is covariant in its accepted-message type.

Diagnostics identify the invariant/dependent position that prevented a
widening. Erasure never uses `Any` to discard runtime checks or proof
obligations.

## Quantitative types

Every binder carries a grade in `{0, 1, ω}`:

- `0` — compile-time only and erased;
- `1` / `:linear` — used exactly once;
- `:affine` — used at most once;
- `ω` — unrestricted.

The kernel rejects scrutinizing, returning, or using an erased value in runtime
computation. Initializers are still checked even when their binding is unused.
Linear capabilities, such as typed OTP replies, therefore cannot be duplicated
or silently dropped.

## Definitional and propositional equality

Definitional equality normalizes both terms and compares their normal forms. It
is automatic and produces no proof object.

`Equivalent(a, x, y)` is propositional equality. Its `reflexive` constructor is
accepted when the endpoints are definitionally equal; matching the proof
identifies the endpoints. `Std.Equivalent` provides symmetry, transitivity, and
congruence as checked Cure functions.

`Equivalent` is distinct from the `Equatable(t)` interface. `Equatable`
computes `Bool` through `==`; it does not prove an identity proposition.

## Interfaces and implementations

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

fn display(x: t) -> String requires Show(t) = show(x)
```

The compiler checks implementation signatures, required superinterfaces,
coherence, and method bodies. Resolution is compile-time and canonical; a
missing dictionary produces a structured diagnostic. Higher-kinded interfaces,
including `Functor(Type -> Type)`, use the same mechanism.

Generated declarations from `@derive` enter the same declaration and module
interface tables as authored implementations.

## Structural patterns

One typed pattern elaborator handles literals, tuples, lists and cons cells,
maps, records, user constructors, `Option`, `Result`, pins, repeated variables,
guards, and multi-clause function heads. It preserves constructor identity,
nested source spans, narrowed bindings, equality constraints for repeated
variables, and pattern-only erasure evidence.

Pattern-valued `let` uses the same grammar and introduces all narrowed bindings
sequentially:

```text
let Ok(%[head, tail]) = parse(input)
```

Exhaustiveness and unreachable-branch analysis operate on the elaborated
constructors and index equations. Z3-backed guard coverage is an untrusted
warning layer; kernel validity never depends on it.

## Totality and conversion

Type checking may unfold only definitions backed by a validated size-change
termination certificate. The analysis covers structural recursion and mutual
recursion. An uncertified definition can still exist, but remains opaque during
conversion. `@total true` requires certification at the declaration.

## Holes and diagnostics

`?name` and `?_` are typed holes. They report the expected type and local
context through the structured diagnostic pipeline. Diagnostics retain
authored source ranges, canonical definition identities, machine-readable
codes, related spans, and safe code actions for terminal, JSON, and LSP
consumers.

See [Dependent Types](DEPENDENT_TYPES.md), [Patterns](PATTERNS.md),
[Proofs](PROOFS.md), and [Kernel](KERNEL.md) for the detailed guides.
