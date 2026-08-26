%{
  title: "Type System",
  description: "The dependent kernel: indexed families, conversion, quantitative binders, patterns, and interfaces.",
  order: 3
}
---

Cure has one bidirectional dependent type checker. The classic checker and
code-generation path have been removed: every program elaborates to dependent
Core, is validated by the small trusted kernel, has compile-time evidence
erased, and is then emitted as BEAM code.

## Bidirectional elaboration

The elaborator alternates between two modes:

- **Infer** synthesizes a Core term and its type.
- **Check** elaborates a term against an expected type.

Expected types flow into lambdas, constructors, blocks, holes, and local
bindings. Implicit constraints may be postponed until later arguments reveal
enough information, so argument order does not decide whether a well-typed call
can be inferred.

Declarations receive canonical owner-qualified identities. Lexical imports and
qualified module availability are tracked separately, repeated interface loads
are idempotent, and imports do not leak transitive bare names.

## Universes and dependent functions

Universes are cumulative and predicative. A function's result may mention its
arguments:

```text
fn append(
  {a: Type},
  {m: Nat},
  {n: Nat},
  xs: Vector(a, m),
  ys: Vector(a, n)
) -> Vector(a, plus(m, n))
```

Brace-delimited parameters are implicit and solved from explicit arguments.
When graded `0`, they cost nothing at runtime.

## Indexed inductive families

`indices` separates uniform parameters from constructor-varying indices:

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

Constructor checking preserves index equations. Pattern matching solves those
equations per branch, narrows local bindings, and can prove a branch
impossible. Forced (`.`) patterns and `impossible` arms expose that reasoning
on the surface.

Empty and single-constructor types are supported:

```cure
type Void = |
type Wrapper = Wrap(Int)
```

## Primitive and composite types

Visible primitive homes include `Std.Int`, `Std.Float`, `Std.Char`,
`Std.Atom`, and `Std.Binary`. `String` is a nominal type (`Std.String`)
storing its text as a `List(Char)`, not a transparent alias for it.

Common composite types are:

- `List(t)` — covariant linked lists;
- `Map(k, v)` — parameterized maps;
- `%[a, b, ...]` — flat tuples;
- `a -> b` and `(a, b) -> c` — function types;
- nominal records declared with `rec`;
- `Option(t)` and `Result(t, e)`, imported from `Std.Option` and
  `Std.Result`.

Use the canonical modules and bare imported names:

```cure
use Std.Result

fn parse_flag(x: Bool) -> Result(Int, Atom) =
  pickup
    x    -> Ok(1)
    else -> Error(:disabled)
```

`Std.Result.Result` is not the intended spelling.

## Sigma pairs and tuples

`Sigma(name: a, b(name))` pairs a value with a second component whose type may
depend on it. Ordinary tuple values and types use the same `%[...]` shape:

```text
let pair : %[Int, Bool] = %[42, true]
```

Legacy `(A, B)` tuple types are accepted for migration and emit
`E086 / E-TYPE-TUPLE-PAREN`; grouped types and function domains are unchanged.

## Subtyping and `Any`

`Never` is the bottom type and `Any` is the top type. Widening propagates only
through safe positions:

- `List(Int)` satisfies `List(Any)` because list elements are covariant;
- function inputs are contravariant and outputs covariant;
- `Pid(inbox)` is covariant in its message type;
- invariant and dependent/indexed positions reject widening that would lose
  evidence or permit an unsafe value.

Diagnostics identify the invariant position that blocks a widening. Erasure
does not turn `Any` into an escape hatch.

## Quantitative binders

Each binder carries a usage grade in `{0, 1, ω}`:

- `0` — compile-time only and erased;
- `@linear` — used exactly once;
- `@affine` — used at most once;
- `ω` — unrestricted.

The kernel rejects returning, scrutinizing, or reusing an erased value at
runtime. Initializers are still checked when their binding is unused. Linear
typed-OTP reply capabilities therefore cannot be duplicated or silently lost.

## Definitional and propositional equality

Definitional equality is automatic: the checker normalizes both terms and
compares their normal forms.

`Std.Equivalent` supplies propositional equality:

```cure
@builtin(:eq)
type Equivalent(a: Type) indices (x: a, y: a)
  reflexive : Equivalent(a, w, w)
```

Matching a proof against `reflexive` identifies its endpoints.
`Std.Equivalent` implements `sym`, `trans`, and `cong` as ordinary,
kernel-checked Cure functions. Proof values are erased.

Do not confuse this with `Std.Equatable`. `Equatable(t)` computes a runtime
`Bool` through `==`; `Equivalent(a, x, y)` is evidence that two endpoints are
identical.

## Structural patterns

One typed pattern elaborator handles:

- integer, negative integer, float, string, atom, boolean, character, and other
  literal patterns;
- tuples, nested lists and cons cells;
- open map patterns and field punning;
- records and nested records;
- user ADTs plus `Option` and `Result` constructors;
- pins, repeated variables, guards, and multi-clause heads.

Bindings retain their narrowed types, repeated variables generate equality
constraints, and every nested pattern retains its authored source span.

Pattern-valued `let` uses the same grammar and introduces bindings
sequentially:

```text
let Ok(%[head, tail]) = parse(input)
```

Exhaustiveness and unreachable-branch diagnostics operate on constructor and
index information. Z3-backed guard coverage is an untrusted warning layer; the
kernel never accepts a term because the solver said so.

## Interfaces and implementations

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

fn display(x: t) -> String requires Show(t) = show(x)
```

The compiler checks implementation signatures, superinterfaces, method bodies,
and coherence. A missing dictionary is a structured error. Implementations are
loaded before callers regardless of file order and retain their owner,
namespace, type arguments, and source origin.

Generated `@derive` implementations are published in the same declaration and
module-interface tables as authored ones.

## Totality and conversion

Type checking may unfold only definitions backed by a validated size-change
termination certificate. Structural recursion, argument permutations, and
mutual recursion are covered. An uncertified function may still exist, but
remains opaque during conversion. `@total true` requires certification.

## Holes and proof authoring

`?name` and `?_` create typed holes and report the goal plus local context.
`have`, `proof chain`, and `because` blocks elaborate to ordinary proof terms;
they do not add unchecked Core constructs.

`postulate`, bodyless `@extern`, and `believe_me` are explicit trust roots.
Inspect a module's reachable roots with:

```bash
cure audit trust My.Module
```

## Effects

The kernel recognises `Effect(t)` as a type former for direct-style effectful
computations; BEAM-facing APIs (OTP, I/O, and so on) return values wrapped in
it. Erased binders cannot carry runtime effects.

For deeper treatment, read the
[Dependent Types](https://hexdocs.pm/cure/dependent-types.html),
[Patterns](https://hexdocs.pm/cure/patterns.html),
[Proofs](https://hexdocs.pm/cure/proofs.html), and
[Kernel](https://hexdocs.pm/cure/kernel.html) guides.
