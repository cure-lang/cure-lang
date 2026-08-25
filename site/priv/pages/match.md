%{
  title: "Pattern Matching",
  description: "Every pattern shape Cure supports: literals, variables, lists, tuples, maps, records, ADTs, bitstrings, pins, repeated variables, guards, nested destructuring, exhaustiveness, and flow-typing.",
  order: 11
}
---
> **Normative source (v0.33.0).** The `match` construct is specified at
> version 1.0.0 in
> [`docs/MATCH.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/MATCH.md).
> That document covers grammar, the full pattern sub-grammar, static /
> dynamic / operational semantics, formatter conformance, the
> Maranget-style exhaustiveness algorithm, refinement narrowing, the
> diagnostic catalogue, and a soundness proof sketch. This page is the
> user-facing tutorial complement; for any conflict, the formal
> specification is the authority.

Pattern matching is the primary way Cure programs decompose data and
direct control flow. Every pattern passes through the dependent elaborator,
which preserves constructor identities, narrowed bindings, index equations,
and source spans before kernel validation and erasure. Runtime guards, pin
equalities, and repeated-variable constraints then lower to atomic BEAM
matching behavior.

This page is the authoritative user-facing reference for the language
feature. The on-disk companion document
[docs/PATTERNS.md](https://github.com/cure-lang/cure-lang/blob/main/docs/PATTERNS.md)
describes the AST-to-Erlang lowering in full.

## Where patterns can appear

Patterns are not confined to `match`. The same grammar is accepted in
every one of these positions:

- **`match` expressions**: arm heads and their `when` guards.
- **Multi-clause function heads**: each `| pat -> body` clause.
- **`let` bindings**: `let pat = expr` destructures immediately, with
  a compile-time failure if the pattern is not exhaustive for the
  declared scrutinee type.
- **`fn` parameters**: parameter positions accept the full pattern
  grammar, not just variable names.
- **Comprehension generators**: `for pat <- source` and the
  corresponding filter forms.
- **`try ... catch`**: the `catch` clauses match on the raised value
  the same way a `match` would.

Each clause starts with a fresh scope, so names can be reused freely
between clauses without shadowing warnings.

## Literal patterns

Every literal form that Cure accepts in expression position is also a
pattern. A literal pattern succeeds exactly when the scrutinee is
structurally equal to the literal.

```cure
fn classify(n: Int) -> Atom =
  pickup
    n == 0 -> :zero
    n == 1 -> :one
    n == -1 -> :minus_one
    n == 0xFF -> :byte
    else -> :big
```

Supported literal shapes:

- Integers (`42`, `0xFF`, `0b1010`, `1_000_000`), with unary minus
  accepted as `-42`.
- Floats (`3.14`, `0.001`).
- Strings (`"hello"`), elaborated as `List(Char)` patterns. Byte literals
  lower through `Std.Binary`.
- Atoms (`:ok`, `:error`, `:my_atom`).
- Booleans (`true`, `false`).
- `nil`.
- Characters (`'a'`, `'Z'`).

## Variables, wildcards, and repeated names

A bare identifier binds a fresh variable; the underscore is the
wildcard and binds nothing.

```cure
fn classify(value: Int) -> Atom =
  match value
    _ -> :anything
```

When a name occurs more than once in the same pattern, the compiler
emits a synthetic equality guard: every occurrence must match the same
value.

```cure
fn classify(pair: Tuple(Int, Int)) -> Atom =
  match pair
    %[x, x] -> :equal
    _ -> :different
```

The injected guard is conjoined with any user-written `when` clause
via `andalso`, so repeated variables compose cleanly with guards.

## The pin operator `^x`

`^x` compares against an already-bound variable instead of binding a
fresh one. It lowers to a fresh variable plus a synthetic equality
guard against the pre-existing binding.

```cure
fn pinned(value: Int) -> Atom =
  let target = 1
  match value
    ^target -> :hit
    _ -> :miss
```

If `target` is not in scope at the pin position, the compiler reports
an unresolved-name error at the pin site rather than binding a fresh
variable there.

## Lists

Two cons forms are accepted in both pattern and construction position.
Single-head cons matches the head and the tail:

```cure
fn classify(xs: List(Int)) -> Atom =
  match xs
    [] -> :empty
    [_h | _t] -> :nonempty
```

Multi-head cons desugars to right-associated cons cells. The pattern
below is identical to `[a | [b | [c | rest]]]`:

```cure
fn first_three(xs: List(Int)) -> Int =
  match xs
    [a, b, c | _rest] -> a + b + c
    _ -> 0
```

Fixed-size list patterns without a tail also work:

```cure
fn first_two(xs: List(Int)) -> Int =
  match xs
    [a, b] -> a + b
    _ -> 0
```

## Tuples

Tuple literals and patterns share the `%[...]` prefix.

```text
fn tuple_kind(value: Tuple(Int, Int)) -> Atom =
  match value
    %[0, 0] -> :origin
    %[_, _] -> :other
```

Tuple patterns recurse into every element, so arbitrary nesting works
out of the box.

## Maps

Map patterns use the `%{...}` prefix. Every key **must be a literal**;
the compiler lowers each field to an Erlang `map_field_exact` entry,
which means the key is required to be present in the scrutinee. Fields
not listed in the pattern are ignored (open matching).

```text
fn request_kind(request: Map) -> Atom =
  match request
    %{method: "GET", path: _p} -> :fetch
    %{method: _m, path: _} -> :reject
```

A bare identifier at a map-key position is shorthand for `key: key`:

```text
fn map_punning(x: Int, y: Int) -> Bool =
  %{x: x, y: y} == %{x: x, y: y}
```

A non-literal, non-identifier map key triggers `E023`.

## Records

Record patterns lower to a map pattern with the implicit
`__struct__ := :tag` guard plus one `map_field_exact` entry per named
field. They participate in schema-driven type checking: referencing a
field that does not exist emits `E021`, and supplying a sub-pattern
whose type does not unify with the declared field type emits `E022`.

```cure
rec Point
  x: Int
  y: Int

fn classify_point(p: Point) -> Atom =
  match p
    Point{x: 0, y: 0} -> :origin
    Point{x: _, y: _} -> :point
```

A bare identifier inside a record pattern is the field-punning
shorthand: `Person{name}` expands to `Person{name: name}`. Unspecified
fields are matched open, so records can be extended without breaking
existing patterns.

## ADT constructors

Constructors of algebraic data types lower to tagged tuples of the
form `{:tuple, L, [tag_atom | child_forms]}`. Any PascalCase name in
function-call position inside a pattern is treated as a constructor
pattern.

```text
type Maybe = Some(Int) | None
type Outcome = Ok(Int) | Error(Int)

fn unwrap(opt: Maybe) -> Int =
  match opt
    Some(v) -> v
    None -> 0
```

Nullary constructors may be written bare (`None`) or with explicit empty
parentheses (`None()`). Bare PascalCase names resolve against the scrutinee
type's constructors; lowercase bare names remain variable bindings.

Constructor patterns recurse into their arguments as patterns, so
nested ADTs decompose in a single arm:

```text
type Nested = Some(Outcome) | None

fn unwrap_nested(x: Nested) -> Int =
  match x
    Some(Ok(v)) -> v
    Some(Error(_)) -> -1
    None() -> 0
```

## Nested destructuring

Every shape above composes with every other. The classic stress test
from the v0.18.0 release notes destructures a 3-tuple whose middle
element is a map holding a cons list:

```text
type Event = Event(Int)

fn nested(value: Tuple(Map, Int, Int)) -> Int =
  match value
    %[ %{list: [head | _]}, _, _] -> head
    %[_, _, _] -> 0
```

There is no imposed depth limit.

## Guards

Guards restrict when a clause applies. They appear after `when`, both
in function heads and in `match` arm heads:

```text
type Message = Msg(String)

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _            -> "zero"

fn message(event: Message) -> String =
  match event
    Msg(s) when s != "" -> s
    Msg(_) -> "empty"
```

Guards accept the usual set of operators:

- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Boolean connectives: `and`, `or`, `not`
- Arithmetic: `+`, `-`, `*`
- Effect-free calls permitted by BEAM guard grammar

Synthetic guards injected by the compiler (pin equalities, repeated
variables) are conjoined with the user-written guard via `andalso`.

## Bitstring patterns

Since v0.20.0, bitstring patterns accept the full Elixir-style segment
grammar. Segments inside `<<...>>` carry type, size, endianness,
signedness, and unit specifiers chained with `-`:

```text
fn decode_packet(packet: Bitstring) -> Atom =
  match packet
    <<_tag::utf8, _size::16, _payload::binary, _rest::binary>> -> :decoded
    _ -> :malformed
```

The specifier grammar mirrors Erlang's exactly. Type atoms are
`integer`, `float`, `bits`, `bitstring`, `bytes`, `binary`, `utf8`,
`utf16`, `utf32`. Endianness (`big` / `little` / `native`),
signedness (`signed` / `unsigned`), and size/unit (`size(n)`,
`unit(u)`) are optional and carry Erlang's defaults:
`integer-unsigned-big-size(8)-unit(1)`. A bare integer after `::` is
shorthand for `size(n)`.

```text
fn decode_bits(bin: Bitstring) -> Int =
  match bin
    <<x::8>> -> x
    <<x::32-signed>> -> x
    _ -> 0
```

## Negated literals

Unary minus in a pattern position compiles to the negated literal, so
`-5` matches the integer `-5`. This works for both integer and float
literals.

```text
fn temperature_kind(temperature: Int) -> Atom =
  match temperature
    -273 -> :absolute_zero
    0 -> :freezing
    _ -> :other
```

## Exhaustiveness

The elaborator checks pattern coverage against the scrutinee's declared
constructors (refined by any indices in scope). A pattern match that
omits a reachable constructor, repeats one, or marks a reachable
constructor `impossible` is a compile **error**, not a warning -- the
program does not build until the gap is closed:

```text
error: Pattern match is missing a case (E118)
  missing: Error(_)
```

Structural problems -- a name bound twice in one pattern, more than one
catch-all, or an open binary/map match with no fallback branch -- are
reported separately as a pattern-structure error.

For infinite types (`Int`, `Float`, `String`), a trailing wildcard `_`
is required for exhaustiveness; you cannot enumerate all integers.

## Error codes

The pattern engine contributes the following dedicated error codes,
each available via `cure explain Edd` or `cure why Edd`:

- **E021** - unknown record field in a record pattern.
- **E022** - record-pattern field type mismatch.
- **E118** - Pattern Coverage: a reachable constructor is missing,
  repeated, or wrongly marked `impossible`.
- **E119** - Pattern Structure: a name is bound more than once, a
  catch-all is duplicated or impossible, a branch is unreachable after
  a catch-all, or a binary/map match has no fallback.

Earlier releases reported non-exhaustive and malformed patterns under
dedicated codes `E004`, `E023`, `E024`, and `E025`. Those codes are
still documented by `cure explain` for historical continuity, but the
current compiler no longer produces them -- the coverage and structure
checks above have taken over that role.

## Dependent branch refinement

Pattern matching refines constructor indices and local binding types in each
arm. This is performed by dependent pattern elaboration and index unification,
not by the removed classic `Cure.Types.PathRefinement` /
`PatternRefinement` modules.

Literal and repeated-variable patterns contribute equality constraints;
constructor patterns preserve their canonical family/constructor identity;
record, tuple, list, and map subpatterns propagate the expected component
types. Pattern-only evidence is erased after the kernel validates the branch.

Guard coverage and shadowing may additionally be checked by Z3-backed linting.
Those warnings do not create trusted refinement types or proof evidence.

## Worked example: JSON-shaped data

The example below uses only pattern matching -- no recursion helper,
no conditional expression -- to classify a JSON-shaped value across
five constructor variants, each with a different secondary shape:

```text
type Json =
  | JNull
  | JBool(Bool)
  | JInt(Int)
  | JStr(String)
  | JArr(List(Json))
  | JObj(List(Tuple))

fn is_truthy(j: Json) -> Bool =
  match j
    JNull()    -> false
    JBool(b)   -> b
    JInt(0)    -> false
    JInt(_)    -> true
    JStr("")   -> false
    JStr(_)    -> true
    JArr([])   -> false
    JArr(_)    -> true
    JObj([])   -> false
    JObj(_)    -> true
```

Every arm combines constructor destructuring with a literal-equality
witness (`0`, `""`, `[]`) to decide truthiness without a single
conditional.

## Limitations

A small set of pattern shapes are reserved for future versions:

- **Range patterns** (`1..10 -> ...`) are compile-time rejected.
- **Bitstring segment specifiers** beyond integer and variable tails
  were only partial before v0.19.0; the current parser accepts the
  full grammar, but a handful of Erlang-level segment combinations
  still fall through to the interpreter rather than the native
  compiler. They are accepted by the surface syntax and documented as
  experimental.
- **Regex patterns** are not part of the surface language; use
  `Std.Regex` in expression position instead.

See `examples/destructuring.cure`, `examples/json_tree.cure`, and
`examples/pattern_guards.cure` for end-to-end programs that exercise
every shape on this page.

## See also

- The `pickup` construct -- the predicate-dispatch counterpart -- is
  documented at [`/pickup`](/pickup) and specified normatively at
  [`docs/PICKUP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PICKUP.md).
- The full normative specification of `match` is at
  [`docs/MATCH.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/MATCH.md).
  Both specifications were published into HexDocs in v0.33.0.
- The pattern-shape lowering tutorial lives in
  [`docs/PATTERNS.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PATTERNS.md).
- The binary-segment grammar lives in
  [`docs/BINARIES.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/BINARIES.md).
