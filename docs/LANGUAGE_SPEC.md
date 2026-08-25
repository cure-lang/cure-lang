# Cure Language Specification

## Syntax Overview

Cure is an indentation-structured language. Blocks are delimited by
indentation level, not by keywords like `do`/`end` or braces.

### Keywords

The active edition reserves the words reported by the lexer. The declaration
and expression keywords most users encounter are:

`fn`, `mod`, `rec`, `fsm`, `actor`, `interface`, `implementation`, `type`,
`typealias`, `primitive`, `let`, `pickup`, `else`, `match`, `with`, `when`,
`local`, `use`, `return`, `throw`, `try`, `catch`, `finally`, `for`, `in`,
`true`, `false`, `nil`, `and`, `or`, `not`, `spawn`, `send`, `receive`,
`after`, `unsafe`, `quote`, `syntax`, `becomes`, `computed`, `by`, `end`,
and `do`.

`requires` is contextual in function and implementation signatures. It lists
interface obligations without reserving the word as an ordinary identifier:

```text
fn show_both(a: t, b: t) -> String requires Show(t) =
  show(a) <> show(b)
```

`where` is reserved for declaration-local definition blocks. The former
constraint spelling `fn ... where Interface(t)` is deprecated; the parser still
accepts it during migration and the printer canonicalizes it to `requires`.

`sup` is a *contextual* soft keyword (v0.25.0): at the lexer level it is
an ordinary identifier so legacy code that uses it as a field or variable
name keeps compiling; the parser dispatches `sup <Name>` to the
supervisor container only at statement-prefix position.

`app` is a *contextual* soft keyword (v0.26.0) with the same treatment:
`app <Name>` at statement-prefix position opens an application
container; every other use of `app` remains a plain identifier.

### Identifiers

Identifiers may carry a trailing `?` to signal a predicate (Elixir
convention):

```text
fn even?(n: Int) -> Bool = n % 2 == 0
fn is_empty?(xs: List(t)) -> Bool = ...
```

The `!` suffix is reserved for effect annotations and FSM hard
events.

### Comments and docstrings

- `# ...` -- line comment.
- `## text` -- single-line doc comment. One per line; attached to the
  following definition. Consecutive `##` blocks separated by a
  blank-line gap (or by plain `#` comments that the lexer drops) are
  merged into a single docstring with a paragraph break between
  blocks (v0.29.0: `Cure.Compiler.Parser.collect_all_doc_comments/1,2`).
  This lets you write a long docstring in natural paragraphs without
  leaving orphan `:doc_comment` tokens ahead of the next definition.
- `###\n...\n###` -- fenced multi-line doc comment. Opens on a line
  whose first three non-whitespace characters are `###`; closes on the
  next line whose first three non-whitespace characters are `###`.
  Leading indentation common to every body line is stripped.
- **Docstring body grammar.** Doc-comment bodies are Markdown: `cure`
  doc tooling (`Cure.Doc.Markdown`, `cure doc`, the REPL's `:doc` /
  `:help` output, and the Cure website's `/stdlib/:module` pages) pipe
  the body through the NIF-free `:md` library. Fenced code blocks
  carrying a known language (`cure`, `elixir`, `erlang`) are
  syntax-highlighted via Makeup; unknown languages pass through with a
  stable `language-<lang>` class for downstream CSS. The strings
  `{{cure_version}}` and `{{cure_vversion}}` are substituted for the
  running Cure version before parsing so release-sensitive copy can
  travel inside docstrings.

### Operators (by precedence, low to high)

- `|>` -- pipe (left-assoc)
- `<-|` / `✉` -- Melquiades send (non-assoc, v0.25.0); binds one notch
  below `|>` so `x |> encode |> pid <-| _` groups as
  `pid <-| (x |> encode)`
- `or` -- boolean or (left-assoc)
- `and` -- boolean and (left-assoc)
- `==`, `!=`, `<`, `>`, `<=`, `>=` -- comparison (non-assoc)
- `..`, `..=` -- range (non-assoc)
- `<>` -- string concat (right-assoc)
- `+`, `-` -- additive (left-assoc)
- `*`, `/`, `%` -- multiplicative (left-assoc)
- `-`, `not` -- unary prefix
- `.` -- field access (left-assoc)

### Literals

- Integers: `42`, `0xFF`, `0b1010`
- Floats: `3.14`
- Strings: `"hello"`, `"hello #{name}"`
- Booleans: `true`, `false`
- Atoms: `:ok`, `:error`
- Nil: `nil`
- Chars: `'a'`
- Lists: `[1, 2, 3]`, `[h | t]`
- Tuples: `%[a, b]`
- Maps: `%{key: value}`

## Modules

```cure
mod MyApp.Math
  fn add(a: Int, b: Int) -> Int = a + b
  local fn helper() -> Int = 42
```

All functions are public by default. Use `local fn` for private.

## Functions

### Single-expression body

```cure
fn add(a: Int, b: Int) -> Int = a + b
```

### Multi-expression body (indented block)

```cure
fn compute(x: Int) -> Int =
  let y = x * 2
  let z = y + 1
  z
```

### Multi-clause (pattern matching on arguments)

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

### Guards

```cure
fn abs(x: Int) -> Int when x >= 0 = x

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

### FFI (Foreign Function Interface)

`@extern(<module>, <function>, <arity>)` binds a Cure function to an external
BEAM function. It is a **type-only signature**: the compiler trusts the declared
types and lowers each call to a direct remote call.

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

Two rules are enforced:

- The head must be **fully typed** -- every parameter annotated and a return type
  declared (`E056`). An untyped head would default to `Any` and defeat the type
  checker.
- The declaration must **not have a body** (`E057`). Codegen ignores any body,
  so a `= ...` is dead code.

Erlang/OTP modules are plain atoms (`:erlang`, `:io`); Elixir modules use their
dotted `Elixir.` path (`Elixir.MyApp.Native`). `@extern` composes with
`local` for private bindings.

See `docs/FFI.md` for the full guide (module forms, effects, lowering, and
patterns).

## Types

### Primitive types

`Int`, `Float`, `String`, `Bool`, `Atom`, and `Char` are foundational surface
types. The formal OTP library defines indexed `Pid(message)` handles and
distinct `MonitorRef` and `TimerRef` types; the old unindexed `Pid` and `Ref`
spellings are retired.

### Composite types

- `List(T)` -- linked list
- `Map(K, V)` -- hash map
- `%[A, B]` -- tuple (the type-level counterpart of the value `%[a, b]`)
- `A -> B` -- function type

`%[A, B]` is the canonical tuple-type spelling; `Tuple(A, B)` parses to the
same `{:tuple_type, ...}` node. The legacy spelling
`(A, B)` remains accepted and has the same elaborated and runtime
representation, but emits the `E086 / E-TYPE-TUPLE-PAREN` deprecation so the
rewrite can be applied mechanically. A grouped type `(A)` and a function domain
`(A, B) -> C` are unaffected.

### ADT (sum types)

```cure
type Option(t) = Some(t) | None
type Result(t, e) = Ok(t) | Error(e)
```

**Multi-line layout (v0.21.0).** ADT declarations may span multiple
lines with leading `|` on continuation lines. The single-line and
multi-line forms are syntactically equivalent.

```cure
type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

**Function-type payloads (v0.21.0).** Constructor payloads accept
arbitrary type expressions, including function arrows:

```cure
type Callback = On(Int -> Int) | Off
type Transform = Morph((Int, Int) -> Int) | Id
```

Function-typed payloads compile to first-class functions at runtime;
pattern matching binds the function to a variable you can call like
any other lambda.

### Refinement types

The classic `{x: T | predicate}` type former has been retired from the trusted
dependent pipeline. Express structural invariants with indexed families and
proof arguments. Guard predicates still narrow control flow for diagnostics
and exhaustiveness; SMT-backed guard analysis is linting outside the trusted
kernel, not evidence for a dependent type.

### Sigma types (dependent pairs)

```text
type Sized(t) = Sigma(n: Nat, Vector(t, n))
```

A Sigma type pairs a value with a type that may depend on it.
The surface forms `Sigma(T1, T2)`, `Sigma(name: T1, T2)`, and
`DPair(...)` are all recognised.

### Pi types (dependent function types)

```text
fn append({t: Type}, xs: Vector(t, m), ys: Vector(t, n)) -> Vector(t, m + n)
```

Return types may freely reference parameter names. The type checker
substitutes the call-site arguments and compares the resulting Core terms by
normalization and definitional equality.

### Equality types

```text
reflexive : Equivalent(t, x, x)
```

`Std.Equivalent` declares the kernel-recognised inductive identity family
`Equivalent(T, a, b)` and its sole constructor `reflexive`. Matching a proof
against `reflexive` identifies its endpoints definitionally. `sym`, `trans`,
and `cong` are ordinary Cure functions checked by the same kernel. This proof
type is distinct from `Std.Equatable`, whose `==` method computes a runtime
`Bool`.

### Proof authoring

The proof surface is implemented as ordinary, kernel-checked Cure terms. It
includes `have name [: Proposition] = expression`, `proof chain` with
`because`, `rewrite [backwards] using proof [at n] [in hypothesis]`,
`simplify [using rules-or-proof]`, and structural `induction` with
`case Constructor(fields, induction_hypotheses) =>`. Proof commands are
elaboration-only and never appear in runtime Core or BEAM output. The complete
worked authoring guide is [PROOFS.md](PROOFS.md); this section and that guide
define the same surface rather than separate proof languages.

Generated defining equations are certified theorem members and can be found
after `function.` in completion and hover. Named arguments may be written in
any order after a positional prefix (`label: value`); the compiler aligns them
to the declaration telescope before dependent solving. Unknown, duplicate,
missing, misplaced, and ambiguous labels use E115 with authored ranges and
machine-safe code actions. Named implicit constructor patterns (`{n = .k}`)
expose and force erased indices during dependent branch refinement. Automatic
congruence lets directed rewriting descend through a unique function context.
Proof-language diagnostics E109–E114 follow the same terminal, JSON, and LSP
structured-diagnostic path.

### Implicit arguments

```cure
fn id({t: Type}, x: t) -> t = x
```

Parameters in `{...}` braces are solved by dependent elaboration from
explicit-argument types at each call site. They cost nothing at runtime.

### Holes

```text
fn safe_head({t: Type}, xs: List(t)) -> t = ?body
```

A `?name` or `?_` placeholder triggers a `:hole_goal` pipeline event
that reports the goal type and the local context at the hole position.

### Totality

```cure
@total true
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

The dependent totality closure classifies definitions before certification.
Add `@total true` to require a successful totality proof at compile time.

### Indexed families

Use `indices` to separate uniform parameters from constructor-varying indices:

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

Constructor-index equations refine each match branch. A branch whose
constructor cannot inhabit the scrutinee indices may be marked `impossible`;
forced (`.`) patterns record values already determined by those equations.
Empty families use `type Void = |`.

### Quantitative binders

Core binders carry a grade in `{0, 1, ω}`. The surface supports `@erased`,
`@linear`, `@affine`, and unrestricted parameters and local bindings. Grade
`0` values are checked but erased. The kernel rejects using erased data in
runtime computation and rejects duplicating or dropping a linear value.

### Union and top types

`A | B` is permitted in any type position and discrimination is ordered.
`Never` is bottom and `Any` is top. Top-type widening propagates through safe
covariant positions (`List(Int)` satisfies `List(Any)`) but not through
invariant or index-sensitive positions.

### Contextual integer literals

A numeral infers as `Int` without an expected type. In a checking position the
elaborator may resolve `ExpressibleByNaturalLiteral(t)` or
`ExpressibleByIntegerLiteral(t)` and call its total conversion. Conversion
returns `LiteralValue(value)` or `InvalidLiteral`, allowing bounded domains to
reject an out-of-range source literal during compilation.

## User-defined syntax

Surface macros declare grammar with `syntax ... becomes`. Holes carry a syntax
kind, may repeat, and may request hygienic fresh names:

```text
syntax beam_ops tell <dest: Code> <message: Code>
  becomes Std.Otp.tell(dest, message)
```

`quote` constructs syntax and `$(...)` splices:

```text
let ast = quote %[:ok, $(payload)]
```

`computed by` delegates expansion to an elaborator function.
`to_syntax`/`from_syntax` reflect losslessly through `Std.Syntax`. Generated
declarations retain both macro-invocation and macro-definition provenance and
are published through the ordinary module-interface tables.

## Editions and migration

`@edition` and `[project].edition` in `Cure.toml` select a grammar/keyword
edition. Earlier spellings remain recognizable to migration tooling rather
than becoming parallel current syntaxes:

```bash
cure migrate --check src
cure migrate --print src/old.cure
cure migrate --strict src
```

The canonical renames include `proto` / `impl` to `interface` /
`implementation`, legacy conditionals to `pickup`, uppercase type variables to
lowercase, and retired module names to current providers.

## Records

Records are named, typed product types. They compile to BEAM maps with a
`__struct__` discriminator key, giving them nominal identity at runtime.

### Definition

```cure
rec Point
  x: Int
  y: Int

rec Person
  name: String
  age: Int

rec Rectangle
  origin: Point
  width: Int
  height: Int
```

Type parameters are supported for generic records:

```cure
rec Pair(a, b)
  first: a
  second: b
```

Type parameters are erased at runtime but are tracked by the type checker.

### Construction

Use `TypeName{field: expr, ...}` to build a record value:

```text
fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
fn origin() -> Point = Point{x: 0, y: 0}
fn make_person(name: String, age: Int) -> Person =
  Person{name: name, age: age}
```

### Field access

Use dot notation `record.field`, which compiles to `maps:get(field, map)`:

```text
fn x_coord(p: Point) -> Int = p.x
fn area(r: Rectangle) -> Int = r.width * r.height
fn rect_origin_x(r: Rectangle) -> Int = r.origin.x  # nested access
```

### Record update

Produce a modified copy of a record with `TypeName{base | field: val, ...}`.
Only the listed fields change; all others are copied from `base`:

```text
fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}
fn translate(p: Point, dx: Int, dy: Int) -> Point =
  Point{p | x: p.x + dx, y: p.y + dy}
fn rename(p: Person, new_name: String) -> Person =
  Person{p | name: new_name}
```

Multiple fields can be overridden in one expression:

```text
fn move(p: Point, nx: Int, ny: Int) -> Point = Point{p | x: nx, y: ny}
```

The type name before `{` is required and must match the type of the base
expression. The compiler verifies override field types against the declared
schema.

### Runtime representation

Records compile to BEAM maps:

```
Point{x: 3, y: 4}  ->  %{__struct__: :point, x: 3, y: 4}
```

Record construction uses `map_field_assoc` (`:=>`). Record update uses
`map_field_exact` (`:=`) which requires the keys to already exist, giving
a `bad_key` error at runtime if the base value has an incompatible shape.

## Interfaces and implementations

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)
```

Generic callers state dictionary requirements explicitly:

```text
fn display(x: t) -> String requires Show(t) = show(x)
```

A constraint head need not occur as the direct type of a value parameter. When
it occurs only in the result, a call in checking position obtains the head from
the expected result type and supplies the corresponding dictionary. `Std.Json`
declares `decode_as` that way — `t` is named by the result and by the
constraint, never by an argument:

```text
fn decode_as(source: String) -> Result(t, DecodeError) requires FromJSON(t)
```

The caller fixes `t` from the expected result type:

```cure
mod DecodeExample
  use Std.Result
  use Std.Json

  fn flag() -> Result(Bool, DecodeError) =
    assert_type decode_as("true") : Result(Bool, DecodeError)
end
```

The annotation (or another surrounding expected type) is semantically relevant:
without an argument or expected result that fixes `t`, the call is
underconstrained. For a rigid `t` inside another constrained generic function,
resolution threads that function's in-scope dictionary rather than selecting a
concrete implementation.

Definitions, methods, and implementations are published under canonical
owner-qualified identities. A bare method is available only when its interface
and implementation dictionary are in lexical scope; qualified module
availability does not leak transitive bare names.

## FSMs (Finite State Machines)

`fsm` is an auto-preluded standard-library macro. It is transparent:
the macro expands to a lifted module whose behavior declaration and
callbacks are written in Cure using the checked BEAM algebra. The
compiler does not recognize an FSM as a special object class.

`Std.Fsm` declares two `fsm` macros over one callback floor. Both require
`use Std.Fsm`. A bare lifted-module name is relative to its lexical owner
(`Main` at top level), while a dotted name is absolute within the Cure source
namespace. Source never needs to spell the emitter-owned `Cure.` prefix.

The structured surface declares the callback state type with `state` and
maps event constructors to `FsmAction` values under `events`:

```cure
use Std.Fsm

fsm Ticker
  state Int
  events
    Tick -> :keep_state_and_data
```

Undeclared event constructors are collected into an `Event` enum owned by
the generated machine (`Ticker.Event`), alongside its `State`. Companion
types live inside the machine, not beside it, so the surrounding module
neither sees nor collides with them.

`states`, `initial` and `event_type` name the state and event types
instead of deriving them — that is how the enclosing module gets a name it
can use. `states` requires `initial`:

```cure
use Std.Fsm

type CounterState = Idle | Counting
type CounterEvent = Start | Bump

fsm Counter
  state Int
  states CounterState
  initial Idle
  event_type CounterEvent
  events
    Start -> Next(Counting(), data)
    Bump  -> Keep(data + 1)
```

The transition-table surface, `fsm <Name> with <Data>`, is an ordinary
macro over the same floor. It catalogs the rows into nominal `State` and
`Event` types and compiles the graph to a total `decide/3`:

```cure
use Std.Fsm

fsm TrafficLight with Int
  Red    --Timer-->     Green
  Green  --Timer-->     Yellow
  Yellow --Timer-->     Red
  *      --Emergency--> Red
```

Reachability, deadlock freedom, terminal-state validity, duplicate rows,
and payload consistency are checked during expansion; a violation is a
compile error. See [`FSM_GUIDE.md`](FSM_GUIDE.md) for the full surface.

The generated module implements the standard `gen_statem` behavior. The
`actor`, `sup`, and `app` macros use the same transparent callback and
algebra vocabulary. None of this is an alternate compiler parser or a
hidden FSM lowering path: expansion runs from the inside out into the
same checked algebra and BEAM behavior declarations as any user macro.

## Actors and Supervisors (v0.25.0)

Typed supervision trees are standard-library macros (`Std.Actor`,
`Std.Supervisor`) over the checked BEAM algebra; a unit that declares an
`actor` or `sup` must `use` the owning module. See `docs/SUPERVISION.md` for
the authoritative reference. They expand to generic lifted modules, not
compiler-owned object classes.

### The Melquiades Operator `<-|` / `✉`

`pid <-| message` is ordinary operator sugar for
`Std.Otp.tell(pid, message)`. The Unicode envelope `✉` is an interchangeable
alias. Both meanings are defined by `Std.Otp`, use its indexed
`RawPid(message, reply, kind)` checking, and return `Effect(Unit)`. They do not
restore the retired raw-process send node or expose Erlang's returned message.
Binding power is one notch below `|>` and is non-associative.

```text
pid <-| Ping()
pid ✉  Ping()
request
|> encode()
|> worker_pid <-| _
```

### `actor`

```text
use Std.Actor

actor Counter
  state Int
  initial 0
  on_message
    Inc -> state + 1
```

`actor` emits ordinary `gen_server` callbacks. `state T` shares a module-local
`State` alias, and callback results use erased `Effect(...)` types so pure and
effectful bodies follow one checked path. See [Actors](/actors) and
`docs/SUPERVISION.md` for the full grammar (`on_message`, `on_call` queries,
the raw `handle_cast`/`handle_info` form, and so on).

### `sup`

```cure
use Std.Supervisor

sup Root
  strategy OneForOne()
  children
    worker Counter as counter
      restart Permanent()
      shutdown Timeout(5000)
```

Child policies use closed `Restart`, `Shutdown`, and `ChildType` values from
`Std.Supervisor`; intensity and period use `Nat`. The generated `init/1` and
`start_link/0` are ordinary checked declarations.

### Links, monitors

`Std.Process` is a compatibility facade over a slice of `Std.Otp`'s typed
process algebra: `self/0`, `link/1`, `unlink/1`, `monitor/2` (takes the closed
`MonitorKind` and returns a `MonitorRef`), `demonitor/1`, `is_alive/1`. Their
process/reply-type parameters are implicit. `Std.Otp` itself additionally has
`exit/2` for sending an exit signal built from `Std.ExitReason`; the current
stdlib has no `trap_exit` wrapper.

### Typed sends

The type checker has a dedicated clause for `{:send, ...}` that
unifies the message type against `Pid(m)` and emits a normal elaboration error
on conflict. `beam_ops tell` and `beam_ops call` are standard-library macros
over the same typed operations.

## Applications (v0.26.0)

The `app` macro creates a transparent lifted OTP application. It lives in
`Std.App`, so a unit that declares one must `use` it. `root` names the
supervisor the application starts, and is the container's only clause -- start
phases and the dependency list come from `cure.toml`. See `docs/APP.md` for the
authoritative reference.

```cure
use Std.App

app MyApp
  root Root
```

The `phase` form accepts one delayed body and the `phases` form dispatches a
flat list of phase/result atoms. Root startup uses `beam_ops start_supervisor`.
All lifecycle results use erased `Effect(...)` contracts. Project discovery
consumes lifted application metadata and enforces one application module per
project.

`cure release` (also `mix cure.release`) packages the compiled
application as a bootable BEAM release under
`_build/cure/rel/<name>/`; a missing project file, build failure, or
release-assembly error surfaces as an operational `E098` (command failure)
or `E100` (artifact) diagnostic. From Cure source,
`Std.App` offers `ensure_all_started`, `start`, `stop`, `get_env`,
`put_env`, `which_applications`, `loaded_applications`, and
`start_phase` as thin wrappers over `:application`.

## Pattern Matching
The `match` construct is specified normatively at version 1.0.0 in
[`docs/MATCH.md`](MATCH.md), which covers grammar, the full pattern
sub-grammar, static / dynamic / operational semantics, formatter
conformance, the Maranget-style exhaustiveness algorithm, refinement
narrowing, the diagnostic catalogue, and a soundness proof sketch.
This section is an informal overview; for any conflict, `MATCH.md`
is the authority.

`match` (and `let`) support deep destructuring across every structural
form in the language. As of v0.18.0 the supported pattern shapes are:
### Literals and variables
```text
match x
  0      -> "zero"
  n      -> "nonzero"
  _      -> "never reached"
```
`_` is the wildcard. A name starting with `_` (for example `_unused`)
is an ordinary binding; the convention signals an intentionally-unused
value (the compiler does not currently emit an unused-variable warning
to silence).
### Tuples and lists
```text
match pair
  %[a, b]        -> a + b
  %[a, b, _rest] -> a + b

match xs
  []             -> "empty"
  [h | t]        -> "non-empty"
  [a, b | rest]  -> "at least two"
  [a, b, c]      -> "exactly three"
```
`[h | t]` binds `h` to the head and `t` to the tail. Multi-head cons
`[a, b, ... | rest]` is desugared at parse time into right-associated
cons cells (`[a | [b | rest]]`). Matching against a literal-length list
(`[a, b, c]`) requires the list to have that exact length.
### Maps
```text
match request
  %{method: "GET", path: p}    -> fetch(p)
  %{method: m, path: _}        -> reject(m)
```
Map keys in pattern position must be literal values. A map pattern
matches if every listed key is present in the subject; keys not
mentioned are ignored (open matching, like Elixir's `%{...}`).
### Records and field punning
```text
match person
  Person{name, age}                    -> salute(name, age)
  Person{name, address: Address{city}} -> greet(name, city)
```
A bare identifier inside a record pattern is shorthand for
`name: name` (field punning). Record patterns compile to map patterns
with a `__struct__ := :tag` guard, so they only match values built
with the same record type.
### ADT constructors
```text
match result
  Ok(v)         -> v
  Error(reason) -> default

match option
  Some(x) -> x
  None    -> 0
```
Nullary constructors may be written bare (`None`) or with explicit empty
parentheses (`None()`). A bare PascalCase name is resolved against the
scrutinee type's constructors; lowercase bare names remain variable bindings.
### The pin operator `^x`
```text
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```
`^x` compares against a previously-bound value rather than binding
fresh. Lowered by the compiler to a guard `V_fresh =:= V_x`.
### Repeated variables
```text
match pair
  %[x, x] -> :equal
  _       -> :different
```
A name that appears twice in the same pattern binds on its first
occurrence and is turned into an equality guard at every later
position (so the pattern only matches when all occurrences hold the
same value).
### Nested destructuring
Any combination of the above can be nested:
```text
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name: n, address: Address{city: c, zip: _}} when c == "Madrid" ->
    greet(n)
```
### Exhaustiveness
The compiler checks pattern exhaustiveness. Missing constructors -- at the
top level or inside a tuple position -- are reported under code `E118`
(Pattern Coverage).

## Conditional Dispatch (`pickup`)

Cure has no `if` / `elif` / `else` chain. Predicate dispatch goes
through the `pickup` construct, specified normatively at version
1.0.0 in [`docs/PICKUP.md`](PICKUP.md). The mental model is one
sentence: *`pickup` walks the clauses and picks up the first one
whose guard is true.* Each block lists boolean guards in source
order and terminates in a mandatory `else -> e` clause that makes
the construct total by construction. Guards must type to `Bool`
(no truthy / falsy coercion); evaluation short-circuits at the
first `true`. The legacy `if`/`elif` shape is removed; the
`cure rewrite if-to-pickup` tool migrates surviving sources.

```text
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  status >= 300 -> :redirect
  status >= 200 -> :ok
  else          -> :informational
```

For the full diagnostic catalogue, formatter rules, refinement
context-strengthening, tail-position guarantee, and migration story,
see `docs/PICKUP.md`.

## Control Flow

### If/else

Legacy `if`/`else` is removed; see
[`docs/PICKUP.md`](PICKUP.md) for the canonical replacement. The
shape historically rendered as `if x > 0 then "positive" else
"non-positive"` is now written:

```text
pickup
  x > 0 -> "positive"
  else  -> "non-positive"
```

### Let bindings

```text
let x = 42
let y = x * 2
```

**In-place destructuring (v0.21.0).** `let` bindings support the same
pattern grammar as `match` arms: ADT constructors, tuples, cons
cells, record field punning, maps, and binary segments. Each bound
variable carries the narrowed scrutinee type.

```text
let Ok(x)         = parse(input)       # ADT constructor
let %[a, b]       = pair                # tuple destructure
let [h | _rest]   = xs                  # cons destructure
let Point{x, y}   = p                   # record punning
let <<b, _::binary>> = buf              # binary destructure
```

Pattern-valued `let` uses the same typed pattern elaborator as `match`.
Bindings receive their narrowed types and become visible to subsequent
expressions in the block. Impossible or non-matching patterns produce a
structured diagnostic rather than being silently weakened into an unchecked
assignment.

### Binary patterns

Binary literals are written between `<<` and `>>`. The parser accepts the
full Erlang-style segment grammar (`value [:: specifier_chain]`, covering
type, signedness, endianness, `size(expr)`, and `unit(n)`), but the current
elaborator only lowers plain 8-bit byte segments, plus a single trailing
unsized `rest::binary` (or `::bytes`/`::bitstring`/`::bits`) tail in pattern
position. A sized or typed segment (`x::16`, `x::float`, `x::utf8`, ...) is
rejected under `E093` as a deferred rich-bit-syntax case rather than
silently mislowered. See `docs/BINARIES.md` for the authoritative reference.

```text
let header       = <<42, 1, 2, 3>>
let <<tag, _::binary>> = buffer

match frame
  <<tag, len, _::binary>> -> len
  <<>>                    -> 0
```

Binary matches desugar to guarded byte-offset reads rather than an
inductive case split, so they are open by construction: a binary `match`
must end in a wildcard/variable catch-all, or the compiler rejects it under
code `E119` (Pattern Structure).

### Binary comprehension generators

```text
[byte for <<byte <- "abc">>]       # [97, 98, 99]
```

A binary comprehension generator (v0.22.0) wraps the whole generator
in `<<...>>`: pattern segments, the `<-` arrow, and the source
expression all live between `<<` and `>>`. The generator segment itself
must be a bare, unsized, untyped binder (e.g. `byte`); it desugars to an
ordinary list generator over the source's byte view. Sized or typed
segment specifiers on the generator pattern (`::size(n)`, `::utf8`, ...)
are a deliberate unsupported extension until their runtime representation
exists.

### Lambda block bodies

Anonymous functions (`fn (params) -> body`) accept four body shapes:

```cure
# Single expression (v0.12.0+).
fn (x) -> x + 1

# Indented block (v0.19.0+). Only usable where the lexer emits
# `:indent`/`:dedent`, i.e. at top level or inside block-forming
# constructs.
fn (x) ->
  let y = x + 1
  y * 2

# Brace-delimited (v0.22.0). Statements separated by `;`; the final
# expression is the body's result. Works anywhere, including inside
# argument lists where newlines are suppressed.
map(xs, fn (x) -> { let y = x + 1; y * 2 })

# end-terminated (v0.22.0). A single `end` keyword closes the body.
# Statement separator is `;` (or newline when newlines are emitted).
map(xs, fn (x) -> let y = x + 1; y * 2; end)
```

All four shapes produce the same `{:block, meta, exprs}` AST node.
The `:block_shape` meta key (`:brace` or `:end`) lets the algebra
formatter round-trip the author's chosen form. `end` is a reserved
keyword from v0.22.0.

An unclosed brace or missing `end` surfaces as `E035 Lambda Block
Unterminated`.

### Pipe operator

```text
5 |> double |> add(1)
# desugars to: add(double(5), 1)
```
