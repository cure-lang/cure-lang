%{
  title: "Interfaces & Protocols",
  description: "Ad-hoc polymorphism with interfaces, implementations, and explicit constraints.",
  category: :learn,
  category_title: "Learn Cure",
  order: 7
}
---

Interfaces are Cure's mechanism for ad-hoc polymorphism. An interface declares
an operation; implementations provide that operation for concrete types. The
dependent elaborator resolves the required implementation at the call site and
records its canonical owner-qualified identity.

The pre-0.34 `proto` and `impl` spellings are retired. `cure migrate` rewrites
them to `interface` and `implementation`.

## Defining an interface

```cure
interface Show(t)
  fn show(x: t) -> String
```

Interfaces may declare more than one method and may require another interface:

```cure
interface Comparable(t) requires Equatable(t)
  fn `<`(a: t, b: t) -> Bool
```

`Comparable(t)` therefore carries both its own ordering dictionary and the
`Equatable(t)` dictionary it depends on.

## Implementing an interface

```text
implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

implementation Show for Bool
  fn show(x: Bool) -> String =
    pickup
      x    -> "true"
      else -> "false"
```

An implementation method is checked against the interface method after the
interface parameters have been instantiated. Missing methods, incompatible
signatures, and missing required implementations are structured compiler
diagnostics.

Implementations are loaded before their callers regardless of source-file
order. Their machine data retains the interface owner, implementation owner,
type arguments, namespace, and source origin.

## Constrained generic functions

A generic function states the dictionaries it needs with `requires`:

```text
fn display(x: t) -> String requires Show(t) =
  "[" <> show(x) <> "]"
```

At `display(42)`, the compiler resolves `Show(Int)`. If no implementation is
available, compilation fails at the call rather than falling back to a dynamic
guard dispatch.

A bare method name is visible only when the relevant interface and dictionary
are in lexical scope. Loading a module for qualified access does not leak its
bare names, and an interface imported transitively through another module does
not become an accidental lexical import.

## Standard interfaces

### `Std.Show`

`Show(t)` provides `show/1`. The standard module includes implementations for
`Int`, `Float`, `String`, `Bool`, and `Atom`, plus the constrained
`show_line/1` helper.

### `Std.Equatable`

`Equatable(t)` provides the runtime comparison operator `` `==` ``.
`` `!=` `` is a constrained helper derived from it. Standard implementations
cover primitive values and structural bootstrap types such as lists, `Nat`,
and `Option`.

`Equatable` is not propositional equality. A comparison returns `Bool`;
`Std.Equivalent.Equivalent(t, x, y)` is the identity type whose inhabitants
are kernel-checked proofs.

### `Std.Comparable`

`Comparable(t)` requires `Equatable(t)` and provides the minimal `` `<` ``
operation. `<=`, `>`, `>=`, and `compare` are constrained helpers. `compare`
returns `LessThan`, `EqualTo`, or `GreaterThan`.

### `Std.Functor`

`Functor(f)` is higher-kinded: `f` has kind `Type -> Type`.

```cure
interface Functor(f)
  fn fmap(container: f(a), g: a -> b) -> f(b)

implementation Functor for List
  fn fmap(container: List(a), g: a -> b) -> List(b) =
    Std.List.map(container, g)
```

### `Std.Semigroup`

`Semigroup(a)` provides associative `combine/2`. The `<>` operator, and `+`
for non-numeric operands, resolve through this interface. Lists provide the
standard implementation; `String` is nominal, so it supplies its own instance
(`Std.String.concat`) rather than reusing the list append.

## Derivation

Records can publish generated implementations through `@derive`:

```cure
use Std.Show
use Std.Equatable
use Std.Comparable

@derive(Show, Equatable, Ord)
rec Point
  x: Int
  y: Int
```

`Ord` is accepted as the derive tag for the `Comparable` implementation.
Generated declarations are registered in the same module-interface and
declaration tables as authored functions, so `show(point)`, `point == other`,
and ordering operators resolve normally. `@derive(JSON)` similarly publishes
`to_json/1` through `Std.Json`.

Derivation is structural: each field must provide the required implementation.
A missing field implementation is an error, and a conflicting authored
implementation is not silently overwritten.

## Complete custom example

```cure
mod MyApp.Stringify
  use Std.String
  use Std.Semigroup

  interface Stringify(t)
    fn stringify(x: t) -> String

  implementation Stringify for Int
    fn stringify(x: Int) -> String =
      "Int(" <> Std.String.from_int(x) <> ")"

  implementation Stringify for Bool
    fn stringify(x: Bool) -> String =
      pickup
        x    -> "Bool(true)"
        else -> "Bool(false)"

  fn stringify_line(x: t) -> String requires Stringify(t) =
    stringify(x) <> "\n"
```

Keep an interface's required method set minimal and build derived operations as
ordinary `requires`-constrained functions. This keeps implementation
obligations small and makes dictionary use explicit.
