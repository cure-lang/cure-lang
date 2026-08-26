# General and Literal-Aware Conversion — Design

**Status:** design locked 2026-07-22.

**Goal:** provide one ordinary typeclass substrate for total and fallible
conversion of both runtime values and literals, while letting literal-specific
implementations exploit exact spelling and proof-carrying syntax facts such as
list length. No conversion-specific declaration grammar is added.

**Authoritative decisions:**

- The public names are `From`, `TryFrom`, `FromLiteral`, and `TryFromLiteral`.
- All four are ordinary Cure interfaces implemented with ordinary
  `implementation` declarations. There is no `conformance`, `accepting`,
  `initialise as`, or literal-only implementation syntax.
- `From`/`TryFrom` work for ordinary runtime values, including variables,
  interpolated strings, and dynamically constructed binaries.
- At an authored literal, applicable `FromLiteral`/`TryFromLiteral`
  implementations take precedence. Only when none applies does the literal
  materialize its ordinary value and use `From`/`TryFrom`.
- Failure or ambiguity in a selected literal-specific tier never silently falls
  back to the general tier.
- Literals retain exact spelling and structural facts until resolution. They are
  never prematurely converted through a lossy representation.
- A literal with no expected type creates a deferred, monomorphic literal
  constraint. Uses may determine its type; the literal never chooses a
  "canonical" type or scans instances to invent its target.
- Accepted conversion output is ordinary Core checked by the kernel. Literal
  descriptors, dictionaries, and compile-time conversion results do not become
  trusted Core claims.

---

## 1. Ordinary interface surface

`Std.Convert` defines the general interfaces:

```cure
mod Std.Convert
  interface From(target, source)
    fn from(value: source) -> target

  interface TryFrom(target, source, error)
    fn try_from(value: source) -> Result(target, error)

  interface ExplainConversionError(error)
    fn conversion_message(error: error) -> String
    fn conversion_help(error: error) -> Option(String)
```

`Std.Literal` defines the literal-aware interfaces:

```cure
mod Std.Literal
  interface FromLiteral(target, literal)
    fn from_literal(value: literal) -> target

  interface TryFromLiteral(target, literal, error)
    fn try_from_literal(value: literal) -> Result(target, error)
```

The `for` head is the target; explicit interface arguments identify the source
and, for fallible conversions, the implementation-specific error type:

```cure
implementation From(Nat) for Int
  fn from(value: Nat) -> Int = ...

implementation TryFrom(Nat, BoundsError) for Bounded(n)
  fn try_from(value: Nat) -> Result(Bounded(n), BoundsError) = ...

implementation TryFrom(String, RegexError) for Regex
  fn try_from(value: String) -> Result(Regex, RegexError) = ...
```

These declarations parse, print, reflect, complete, hover, resolve, and
elaborate through the same machinery as every other interface. The parser does
not recognize their names and produces no conversion-specific declaration AST.
Macro-authored and directly authored implementations are identical.

The elaborator recognizes only the canonical identities `Std.Convert#From`,
`Std.Convert#TryFrom`, `Std.Literal#FromLiteral`, and
`Std.Literal#TryFromLiteral` at implicit conversion sites. Same-spelled user
interfaces elsewhere remain ordinary interfaces with no special behavior.

### 1.1 Full multi-parameter instance identity

The normalized full interface application participates in instance identity:

```text
(canonical interface, normalized explicit arguments, normalized for-head)
```

Thus these are distinct, legal implementations:

```cure
implementation FromLiteral(Float) for Decimal
implementation FromLiteral(String) for Decimal
```

They are ambiguous when both apply to one floating literal; they are not a
declaration-time duplicate. This supersedes the older typeclass design's
single-parameter shorthand key `(interface, for-head)`. Exact duplicate or
unifiably overlapping full applications remain ordinary typeclass declaration
errors. No functional dependency is added.

Named implementations retain the ordinary rule: they are explicit dictionary
values and do not enter automatic conversion resolution.

---

## 2. Meaning of the four interfaces

### 2.1 `From`: total conversion

`From(source) for target` promises that every source value produces a target:

```cure
implementation From(Nat) for Int
implementation From(Char) for Nat
implementation From(Bounded(n)) for Nat
```

It may be inserted for both literals and runtime expressions when uniquely
selected:

```cure
let count: Int = natural_value
```

`From` must not hide validation failure, throw, trap, return a sentinel, or
silently clamp. A conversion which can reject any inhabitant belongs in
`TryFrom`.

### 2.2 `TryFrom`: fallible conversion

`TryFrom(source, error) for target` works on every source value but returns an
ordinary `Result`:

```cure
implementation TryFrom(String, RegexError) for Regex
implementation TryFrom(Nat, BoundsError) for Bounded(n)
implementation TryFrom(String, DecimalError) for Decimal
```

At runtime the caller handles the result:

```cure
match try_from(pattern_text)
  Ok(regex) -> use(regex)
  Error(error) -> report(error)
```

A potentially failing runtime conversion is never silently inserted into a bare
target position:

```cure
let regex: Regex = interpolated_pattern
```

This receives a diagnostic explaining that `String -> Regex` may fail and
showing the explicit `try_from` form. An implementation-specific error type is
allowed; automatic literal diagnostics additionally require a visible
`ExplainConversionError(error)` implementation.

### 2.3 `FromLiteral`: total literal-aware conversion

`FromLiteral` receives a representation derived from authored literal syntax.
It can use facts unavailable after ordinary materialization: exact decimal
spelling, character escape provenance, list length, tuple arity, statically
known keys, or binary bit length.

It need not be compile-time evaluated. A list literal containing runtime
variables still has a statically known spine length, so a total
`FromLiteral` conversion can emit ordinary runtime construction while using the
length at the type level.

### 2.4 `TryFromLiteral`: fallible literal-aware conversion

`TryFromLiteral` is chosen when literal syntax exposes useful information but
conversion can still reject the literal. When the descriptor and conversion are
compile-time evaluable, `Ok(value)` is inserted and `Error(error)` becomes a rich
compiler diagnostic. If value-dependent runtime components prevent evaluation,
the conversion remains an ordinary `Result`; it cannot fill a bare target
position without explicit handling.

---

## 3. Literal representations

> **0.34 bootstrap debt — spelling fields use `List(Char)`:** `Std.Literal` is
> compiled before the friendly `String` alias in `Std.String`, so the initial
> implementation spells the `NaturalLiteral`, `IntegerLiteral`, and
> `DecimalLiteral` text fields as `List(Char)`. This is definitionally the
> current representation of `String`, but it is not the intended long-term
> public abstraction. Fix the foundational module layering so the descriptor
> API can name `String` directly without making `Std.Literal` depend on a later
> stdlib layer or exposing String's representation. Do not add conversions or
> duplicate storage merely to hide this ordering problem.

Literal representations are ordinary, stdlib-visible indexed types with
compiler construction support. They are not trusted evidence: their
constructors and indices are checked normally by the kernel.

The initial family is conceptually (field details may be hidden behind public
accessors, but these are ordinary well-kinded declarations):

```cure
rec NaturalLiteral
  spelling: String
  value: Nat

rec IntegerLiteral
  spelling: String
  value: Int

rec DecimalLiteral
  spelling: String

rec StringLiteral
  value: String

rec CharacterLiteral
  value: Char

rec AtomLiteral
  value: Atom

type ListLiteral(a) indices (n: Nat)
  EmptyLiteral : ListLiteral(a, Z)
  PrependLiteral : a -> ListLiteral(a, n) -> ListLiteral(a, S(n))

rec BinaryLiteral indices (bits: Nat)
  value: Binary
```

Numeric descriptors retain normalized exact spelling. Integral descriptors also
carry their already-checked semantic value; decimal syntax deliberately does
not carry a host `Float`, coefficient/exponent decomposition, or a duplicate
parsed representation:

```text
12       -> NaturalLiteral(value=12, spelling="12")
-12      -> IntegerLiteral(value=-12, spelling="-12")
12.340   -> DecimalLiteral(spelling="12.340")
1.2e6    -> DecimalLiteral(spelling="1.2e6")
-0.0     -> DecimalLiteral(spelling="-0.0")
"\n"     -> StringLiteral(value=[U+000A])
'\n'      -> CharacterLiteral(value=10)
```

Source spans and authored spelling live in metadata/provenance and are not part
of definitional equality. Digit separators are removed from normalized numeric
text while sign, fractional scale, exponent, and negative zero remain intact.
String/Char escape syntax is decoded exactly once by the lexer.

`ListLiteral(a,n)` is proof-carrying structure: its type index is the authored
element count. Its runtime erasure may be the same list spine as `List(a)`.
`BinaryLiteral(bits)` is available when segment widths determine a static bit
length. A binary construction with unknown total length remains an ordinary
`Binary` source, though statically known prefix/segment facts remain available
to diagnostics and future refinements.

The compiler must preserve descriptors through parsing, printing, MetaAST,
macro transport, hashing, caching, and incremental interfaces. It must not turn
a `DecimalLiteral` into a host float before selecting a conversion.

Each category exposes a small, specified candidate representation set to the
literal tier:

| Syntax | Literal-tier source representations |
|---|---|
| unsigned integral | `NaturalLiteral`, `Nat`, normalized `String` |
| negative integral | `IntegerLiteral`, `Int`, normalized `String` |
| decimal/exponent | `DecimalLiteral`, exact `String`, rounded `Float` |
| string | `StringLiteral`, decoded `String`, UTF-8 `Binary` |
| character | `CharacterLiteral`, `Char`, `Nat` |
| atom | `AtomLiteral`, `Atom` |
| list | `ListLiteral(a,n)`, ordinary `List(a)` |
| statically-sized binary | `BinaryLiteral(bits)`, `Binary`, and byte-aligned `List(Int)` |

This is a whitelist of representations the compiler knows how to construct,
not a whitelist of target types. An implementation chooses a path solely by its
ordinary source argument. Adding a new target never requires a parser change.

---

## 4. Deferred inference and two-tier resolution

Literal syntax does not determine its own target type. When no expected type is
available, elaboration records a deferred constraint instead of defaulting:

```text
LiteralConstraint {
  kind,
  exact_descriptor,
  target_meta,
  element_metas,
  source_span,
  provenance
}
```

For example:

```cure
let x = [1, 2, 3]
```

initially has the conceptual state:

```text
x : ?target
pending ListLiteral(?element, 3) -> ?target
```

It does not become `List(Int)`, `Vector(Int,3)`, or any other type merely
because an implementation is visible. Literal constraints refine expected
types; they never search the instance environment to invent an outer target.

Uses of the binding constrain the shared target meta. Once target `T` is known:

1. Build the exact literal descriptor representations supported by the syntax.
2. Gather visible `FromLiteral` and `TryFromLiteral` implementations whose
   target unifies with `T` and whose literal source can be constructed.
3. If the literal tier has candidates:
   - one candidate: select it;
   - more than one: issue a literal-conversion ambiguity diagnostic;
   - do not inspect the general tier to break the tie.
4. If the literal tier has no applicable candidate, materialize the syntax's
   ordinary source representation and gather `From`/`TryFrom` for it and `T`.
5. In the general tier:
   - no candidate: report missing conversion/type mismatch;
   - one candidate: select it;
   - more than one: report conversion ambiguity.
6. A selected `From`/`FromLiteral` produces a target term directly.
7. A selected `TryFrom`/`TryFromLiteral` is evaluated early only when its input
   and dependency closure are compile-time reducible. `Ok` inserts a checked
   target; `Error` becomes a diagnostic. Otherwise an explicit runtime `Result`
   is required.

Fallback occurs only when the literal tier has zero applicable candidates. It
never occurs after:

- ambiguity within the literal tier;
- a selected `TryFromLiteral` returns `Error`;
- literal conversion gets stuck or exhausts fuel;
- the conversion produces the wrong type;
- kernel checking rejects the produced term.

Declaration order, import order, module load order, and a compiler preference
for total/fallible or exact/lossy sources never resolve ambiguity. The sole
priority rule is:

```text
literal-aware tier > general-value tier
```

Within either tier, two applicable paths are ambiguous. For example, defining
both `FromLiteral(Float) for Decimal` and
`FromLiteral(String) for Decimal` requires the user to remove/hide one or call
an explicit conversion.

### 4.1 Monomorphic deferred bindings

A deferred literal binding has one inferred type and is elaborated once. It is
not implicitly generalized over all possible literal interpretations:

```cure
fn consume(values: Vector(Int, 3)) -> Unit = ...

consume([1, 2, 3])

let values = [1, 2, 3]
consume(values)
```

The direct call gets `Vector(Int,3)` immediately from the parameter. In the
second call that same requirement flows back through `values` to its deferred
constraint. Both select the same `FromLiteral(ListLiteral(Int,3)) for
Vector(Int,3)` implementation and produce equivalent checked Core modulo the
administrative let. Introducing or removing a single-use unannotated binding
cannot change resolution or diagnostics.

Multiple uses still constrain one shared type:

```cure
let x = [1, 2, 3]
consume_vector(x)
consume_list(x)
```

If the first use requires `Vector(Int,3)` and the second requires `List(Int)`,
the result is an incompatible-use diagnostic naming both sites. The compiler
does not duplicate or reinterpret `x` per use. Users who need two
representations write two bindings or convert explicitly.

Nested constraints flow together. An expected `Matrix(Int,2,2)` can determine
the target of `[[1,2],[3,4]]`, both inner targets, both length indices, and all
element literal types without any inner default.

### 4.2 Resolution checkpoints

Every deferred literal constraint must be solved before the binding leaves the
elaboration boundary where its type is required.

An unused, unannotated binding receives one combined diagnostic rather than an
unused warning plus an unrelated inference error:

```text
cannot determine the type of unused literal binding `x`

The literal has no use that determines what it should become.
Delete the unused binding or add a type annotation.
```

A used but underconstrained literal receives a targeted annotation diagnostic.
Conflicting uses receive one diagnostic listing each demanded type and use
span. A public/exported signature cannot depend on future downstream callers:
if its literal result remains unresolved at the module-interface boundary, it
requires a type annotation. Deferred inference does not cross separately
compiled public interfaces.

### 4.3 Ordinary literal materializations

When the literal tier is absent, the general tier starts from these ordinary
values:

| Authored syntax | Ordinary source |
|---|---|
| unsigned integral | `Nat` |
| negative integral | `Int` |
| decimal/exponent | `Float` |
| non-interpolated string | `String` |
| character | `Char` |
| atom | `Atom` |
| list | `List(a)` |
| binary construction | `Binary` |

Prelude identity `From` implementations preserve literals when surrounding
context explicitly determines their ordinary type. The table defines fallback
source representations after a target is known; it does not define default
target types. A completely unconstrained literal remains deferred.

Interpolated strings, integer variables, list variables, and dynamic binaries
are already ordinary values and therefore begin directly in the general tier.

---

## 5. Exact floating and Decimal behavior

A decimal/exponent literal is initially represented only by its exact
`DecimalLiteral` spelling. The selected target's protocol implementation owns
parsing and validation:

```cure
implementation ExpressibleByDecimalLiteral for Float
  fn from_decimal_literal(literal: DecimalLiteral) -> LiteralResult(Float) =
    # parse exact spelling using the specified binary64 policy

implementation ExpressibleByDecimalLiteral for Decimal
  fn from_decimal_literal(literal: DecimalLiteral) -> LiteralResult(Decimal) =
    # parse literal.spelling directly as an exact decimal
```

Thus:

```cure
let f: Float = 0.1
let d: Decimal = 0.1
```

Float deliberately performs IEEE-754 conversion. Decimal consumes exact text
and never round-trips through Float. Runtime strings use the general interfaces:

```cure
implementation TryFrom(String, DecimalError) for Decimal
implementation From(Float) for Decimal  # explicitly approximate, if provided
```

The Float materialization policy is BEAM-compatible binary64, round-to-nearest
ties-to-even, negative-zero preserving, finite normal/subnormal permitting, and
overflow rejecting rather than silently producing infinity. NaN and infinities
are named values, not numeric literal spellings.

There is exactly one decimal-literal protocol lookup for a target, so competing
intermediate representations cannot make a literal ambiguous. Precision is
never sacrificed by an implicit intermediate conversion.

---

## 6. Vector and proof-derived indices

The motivating indexed conversion is ordinary source code:

```cure
implementation FromLiteral(ListLiteral(a, n)) for Vector(a, n)
  fn from_literal(values: ListLiteral(a, n)) -> Vector(a, n) =
    match values
      EmptyLiteral() -> Empty()
      PrependLiteral(head, tail) -> Prepend(head, from_literal(tail))
```

At:

```cure
fn consume(values: Vector(Int, 3)) -> Result = ...
consume([10, 20, 30])
```

the descriptor has type `ListLiteral(Int, 3)`, so the kernel checks the Vector
length without a user-written proof or runtime length check. In a dependent
context `Vector(Int,n)`, ordinary unification may solve `n = 3` from the
descriptor. A completely unconstrained list remains deferred until annotation
or use determines whether it is `List(Int)`, `Vector(Int,3)`, or another target.

This substrate also supports user-defined `NonEmptyList`, fixed-size matrices
from nested list literals, typed tuples, fixed byte arrays, and map literals
with statically known key sets. Each requires its own ordinary implementation;
the compiler never hard-codes target types such as Vector.

---

## 7. Bounded values, refinement, and runtime proof

`Char` is a nominal, constructor-less carrier declared with
`@erases(:integer)`. It therefore remains one raw BEAM code-point integer at
runtime without being definitionally interchangeable with an arbitrary
`Bounded(1114112)`. Construction is restricted to Unicode scalar values:
`0..0x10ffff` excluding the UTF-16 surrogate interval `0xd800..0xdfff`.

An arbitrary runtime Nat uses a fallible general conversion:

```cure
implementation TryFrom(Nat, BoundsError) for Bounded(n)
```

A refined source carrying the bound proof permits a total conversion:

```cure
rec Below(n)
  value: Nat
  {0 proof: LessThan(value, n)}

implementation From(Below(n)) for Bounded(n)
```

A natural literal can use `TryFromLiteral` or the general `TryFrom` fallback.
Because its value is known, the elaborator evaluates the check, inserts the
compact `{:bounded_lit,k}` on success, and gives a range diagnostic on failure.
There is no unchecked `Nat -> Bounded(n)` cast.

Implementation status (2026-08-03): range rejection is enforced, but the
property suite currently exposes a diagnostic-shaping defect. The semantic
reason
`{:bounded_lit_out_of_range, value, bound}` is wrapped as
`{:invalid_literal_implementation, :from_natural_literal, reason}`. This is not
the specified public diagnostic: a valid literal implementation rejecting an
out-of-range value must report the range reason directly, preserving the value,
bound, authored spelling, and source span. `invalid_literal_implementation` is
reserved for an implementation whose declaration or returned Core value
violates the literal-protocol contract.

Generic JSON collection instances expose a separate coherence requirement. An
instance such as `ToJSON(Option(t)) requires ToJSON(t)` is a dictionary factory:
constructing the outer dictionary requires the inner `ToJSON(t)` dictionary.
The coherence registry keeps the normalized outer head (`Option`) for candidate
selection and retains the instance's applied head plus `requires` templates as
the canonical factory description. Dispatch unifies the concrete applied type
with that template, recursively constructs each required dictionary, and closes
the outer method dictionary over those dependencies. With a rigid inner type it
captures the caller's in-scope dictionary; with a concrete inner type it selects
the canonical implementation recursively. The same `requires` source is copied
onto the mangled method for checking its body. This mechanism is general and
must not be replaced by JSON-specific whitelists or unchecked structural
encoding. `String = List(Char)` still requires normal-form overlap handling so
the specialized JSON string representation remains distinct from a generic JSON
array representation.

`Bounded(0)` has no values; `Bounded(1)` contains exactly zero. Compact bounded
values remain definitionally equal to their `First`/`Next` forms and erase to
the same BEAM integer.

---

## 8. Binary, String, Char, and Atom conversions

The existing `<<...>>` segment AST remains unchanged. When segment widths give
a static total, `BinaryLiteral(bits)` enables indexed targets such as
`FixedBits(bits)` or `FixedBytes(n)`. Byte-aligned literals may additionally
expose an exact `List(Int)` representation. Otherwise the expression
materializes as ordinary `Binary` and uses general `From`/`TryFrom`.

`<<1,2,3>>` can therefore initialize a fixed three-byte value without an
authored length proof, while `<<tag,payload::binary>>` remains usable through
ordinary runtime Binary conversion. Patterns and binary comprehension
generators never invoke conversion interfaces.

String literals expose decoded `String` plus exact spelling to the literal
tier; interpolated strings are runtime `String`. Character literals expose the
decoded Erlang-compatible `Char`; escapes are not reparsed by implementations.
Atom literals expose only statically authored Atom values and never create atoms
from runtime strings.

Boolean and record construction do not automatically become conversions in the
first slice. List and binary syntax are included because their literal
descriptors carry indices unavailable from ordinary runtime values. Further
tuple/map literal descriptors require separate specs before activation.

---

## 9. Trust and evaluation boundary

Conversion resolution and evaluation are untrusted elaborator work:

- conversion methods elaborate to ordinary dictionaries and functions;
- compile-time evaluation requires a totality-certified dependency closure or
  an audited primitive;
- evaluation is fuel-bounded and reports structured stuck/fuel diagnostics;
- extern/runtime-only work cannot masquerade as compile-time validation;
- sibling conversions have independent evaluator/freshening state;
- every produced target term is independently checked by the kernel.

No new Core inference rule is introduced merely to trust a conversion. Indexed
literal descriptor types use ordinary inductives. Descriptor lowering may use
compact existing literal forms, but their indices and payloads remain
kernel-checkable. All dictionaries, descriptors used only for elaboration,
proofs marked quantity zero, and compile-time Results erase.

---

## 10. Diagnostics

Every failure is registered in Cure's existing typed diagnostic registry.
Numeric codes are allocated only after rebasing over the active diagnostics
work; this spec reserves reason keys and payload requirements:

1. `:missing_conversion`
2. `:ambiguous_conversion`
3. `:fallible_runtime_conversion_requires_handling`
4. `:conversion_source_materialization_failed`
5. `:conversion_not_total`
6. `:conversion_stuck`
7. `:conversion_rejected`
8. `:conversion_wrong_result`
9. `:conversion_kernel_rejected`
10. `:literal_descriptor_mismatch`
11. `:underconstrained_literal_binding`
12. `:unused_untyped_literal_binding`
13. `:conflicting_literal_binding_uses`
14. `:public_literal_type_unresolved`

Every diagnostic includes the expression/literal span, authored spelling when
present, expected and normalized target, source/descriptor type, all candidate
implementation identities and definition spans, visibility/import provenance,
selected tier, macro provenance, and failing Core context when available.

Ambiguity explicitly explains the tier and never suggests that ordering will
fix it. A runtime fallibility diagnostic shows an explicit `try_from`/`match`
repair. A literal `Error(error)` is rendered through
`ExplainConversionError`; malformed or unavailable renderers fall back to a
compiler-owned message rather than E101 or a raw tuple.

For example:

```text
1114112 cannot be converted to Char

Char accepts Unicode scalar values from 0 through 1114111, excluding surrogates.
The supplied literal is one greater than the maximum.
```

No user-authored conversion failure may surface `ArgumentError`, `MatchError`,
missing-definition crashes, or generic E101.

---

## 11. Completion, hover, navigation, and reflection

Tooling is definition-of-done work:

- completion offers applicable `From*`/`TryFrom*` source and error types;
- implementation-body completion supplies the resolved method signature;
- hover on an interface explains totality, fallibility, and tier precedence;
- hover on a conversion site shows the selected tier, implementation, source,
  target, and whether work occurs at compile time or runtime;
- hover on a deferred literal binding shows constraints accumulated from its
  uses and its resolved type, or explains why it remains underconstrained;
- Float-source hover may show rounding; exact-String hover never invents a
  Float approximation;
- ambiguous hover exposes the same candidates as the compiler diagnostic;
- go-to-definition reaches the selected implementation and method;
- Vector/list hover shows the derived length index;
- macro-expanded conversions retain original and generated provenance.

MetaAST exposes interface declarations normally and preserves literal semantic
descriptors plus authored metadata. Parse/print and macro conversion must not
round-trip floating syntax through a host float or discard list/binary indices.

---

## 12. Required properties and gates

### Resolution

- literal tier takes precedence exactly when it has an applicable candidate;
- a literal never invents a target by scanning visible implementations;
- use-flow shares one monomorphic target meta and elaborates each binding once;
- direct literal use and wrapping that literal in a single-use unannotated `let`
  select the same implementation, infer the same element/index types, produce
  the same diagnostics, and yield equivalent checked Core modulo the
  administrative binding;
- unused, underconstrained, conflicting-use, and unresolved-public-boundary
  constraints receive their dedicated diagnostics;
- inference never depends on downstream callers across a module interface;
- zero/one/many behavior is deterministic in each tier;
- rejection, stuck evaluation, or ambiguity never triggers fallback;
- declaration, import, file, and interface-load order cannot change selection;
- repeated interface loading is idempotent and cannot duplicate candidates;
- qualified availability does not leak an automatic lexical implementation;
- macro-authored and directly authored conversions behave identically.

### Exactness and indices

- Decimal floating literals never pass through Float on the exact String path;
- Float conversion agrees bit-for-bit with the specified BEAM policy;
- String/Char escapes decode exactly once and preserve authored provenance;
- ListLiteral indices equal authored element counts under arbitrary elements;
- nested literal indices compose for matrices and other indexed consumers;
- nested expected types solve outer, inner, element, and index constraints
  without canonical literal defaults;
- binary descriptors preserve segment semantics and exact known bit length;
- interpolated strings and dynamic binaries use the general tier.

### Safety and runtime behavior

- arbitrary runtime Nat-to-Bounded is fallible; refined proof input is total;
- `Char` accepts exactly the Unicode scalar values in `0..1114111`, including
  zero and excluding `0xd800..0xdfff`;
- every compile-time-produced payload is kernel-checked;
- non-total, stuck, extern-dependent, and fuel-exhausting conversions receive
  dedicated diagnostics;
- a fallible runtime conversion cannot be silently coerced to its success type;
- emitted code contains no compile-time-only descriptor/dictionary/Result;
- proof and index erasure is verified in BEAM.

### Diagnostics and tooling

- every reason has a registry entry, schema, fixture, catalog case, snapshot,
  explanation, and fingerprint test;
- missing, ambiguous, fallible-runtime, rejected, stuck, wrong-result, and
  kernel-rejected cases name exact source/target/implementation context;
- completion, hover, go-to-definition, reflection, and macro provenance cover
  all four interfaces and both tiers.

### Full gate

- clean dependency-ordered stdlib build;
- complete `MIX_ENV=test mix test`;
- TCB, totality, erasure, and relevant Antigen suites;
- incremental/interface-order and escript gates;
- no E101, compiler warning, unresolved canonical key, or runtime conversion
  silently selected for a compile-time proof obligation.

---

## 13. Implementation sequence

1. Generalize multi-parameter instance identity to the normalized full
   application and test ambiguity independently of conversions.
2. Add `From`, `TryFrom`, error explanation, explicit method calls, and runtime
   Result behavior.
3. Add literal descriptor types and exact lexer/parser/printer/MetaAST/hash
   preservation while replacing eager defaulting with deferred literal
   constraints.
4. Add monomorphic use-flow, scope/interface checkpoints, unused/
   underconstrained/conflicting-use diagnostics, and nested-literal solving.
5. Add the two-tier resolver with strict no-fallback-after-selection laws.
6. Route natural/integer/Float contexts without canonical defaults, preserve
   exact Float descriptors, and add Float and Decimal precision pins.
7. Add proof-producing Bounded conversions and exact Erlang Char gates.
8. Add `ListLiteral(a,n)` and the Vector vertical slice, including runtime
   elements with compile-time length.
9. Add String/Char/Atom descriptors and interpolated/runtime fallback tests.
10. Add indexed BinaryLiteral for statically sized segments and ordinary Binary
   fallback for dynamic construction.
11. Land each producer's rich registry/catalog/fixture coverage with that
    producer, not as a later cleanup pass.
12. Land completion, hover, navigation, and reflection alongside each semantic
    slice.
13. Run the complete stabilization gate.

At no stage may the compiler round Decimal through Float without an explicitly
selected Float source, silently break an ambiguity, insert a fallible runtime
conversion as a bare value, add conversion declaration syntax, or admit an
unchecked Nat-to-Bounded cast.
