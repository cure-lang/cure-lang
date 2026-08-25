%{
  title: "Language Guide",
  description: "Complete syntax reference for the Cure programming language.",
  order: 2
}
---
Cure is an indentation-structured, expression-oriented language that compiles to BEAM bytecode. Blocks are delimited by indentation level -- no `do`/`end`, no braces. The last expression in a block is its value.

## Modules

Every Cure source file contains one module. The module name follows Elixir/Erlang dot-separated conventions:

```text
mod MyApp.Math
  fn add(a: Int, b: Int) -> Int = a + b
  fn sub(a: Int, b: Int) -> Int = a - b
```

All functions inside a module are public by default. Use `local fn` for private functions:

```cure
mod MyApp.Internal
  fn public_api(x: Int) -> Int = helper(x) + 1

  local fn helper(x: Int) -> Int = x * 2
```

## Functions

### Single-expression body

When the body is a single expression, write it after `=` on the same line:

```text
fn add(a: Int, b: Int) -> Int = a + b
fn greet(name: String) -> String = "Hello, " <> name <> "!"
fn identity(x: T) -> T = x
```

### Multi-expression body

For multiple expressions, put `=` at the end of the signature line, then indent the body:

```cure
fn compute(x: Int) -> Int =
  let y = x * 2
  let z = y + 1
  z
```

The last expression (`z`) is the return value.

### Multi-clause functions

Pattern match on arguments using `|` clauses:

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)

fn describe(x: Int) -> String
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"

fn fibonacci(n: Int) -> Int
  | 0 -> 0
  | 1 -> 1
  | n -> fibonacci(n - 1) + fibonacci(n - 2)
```

### Guards

Guards restrict when a function clause or pattern applies. Use `when` after the parameter list or after the pattern:

```cure
fn abs(x: Int) -> Int when x >= 0 = x

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

Guards can use comparison operators (`>`, `<`, `>=`, `<=`, `==`, `!=`), boolean operators (`and`, `or`, `not`), and arithmetic.

### Effect annotations

Functions can declare their side effects after the return type using `!`:

```text
fn read_file(path: String) -> String ! Io
fn risky(x: Int) -> Int ! Exception
fn complex(x: Int) -> Int ! Io, Exception
```

Effect kinds: `Io`, `State`, `Exception`, `Spawn`, `Extern`. When no `!` annotation is present, effects are inferred from the body.

### Type annotations

Every parameter must have a type annotation. Return types are declared after `->`:

```text
fn process(name: String, count: Int) -> String = name <> "!"
```

Polymorphic functions use lowercase type variables:

```cure
fn identity(x: t) -> t = x
fn apply(f: a -> b, x: a) -> b = f(x)
```

## Keywords

The current declaration and expression vocabulary includes:

`fn`, `mod`, `rec`, `fsm`, `actor`, `interface`, `implementation`, `type`,
`typealias`, `primitive`, `let`, `pickup`, `else`, `match`, `with`, `when`,
`local`, `use`, `return`, `throw`, `try`, `catch`, `finally`, `for`, `in`,
`true`, `false`, `nil`, `and`, `or`, `not`, `quote`, and `unsafe`.

Earlier-edition words such as `proto`, `impl`, `if`, `then`, and `elif`
remain recognizable so `cure migrate` can rewrite them.

## Comments

Single-line comments start with `#`:

```cure
# This is a comment
fn add(a: Int, b: Int) -> Int = a + b  # inline comment
```

Doc comments start with `##` and are attached to the following definition. They are extracted by `cure doc` to generate HTML documentation:

```cure
## Returns the absolute value of an integer.
##
## Examples:
##   abs(-5)  # => 5
fn abs(x: Int) -> Int
  | x when x >= 0 -> x
  | x -> -x
```

## Operators

Ordered from lowest to highest precedence:

| Precedence | Operator(s) | Associativity | Description |
|---|---|---|---|
| 1 | `\|>` | left | pipe |
| 2 | `or` | left | boolean or |
| 3 | `and` | left | boolean and |
| 4 | `==` `!=` `<` `>` `<=` `>=` | non-assoc | comparison |
| 5 | `..` `..=` | non-assoc | range (exclusive, inclusive) |
| 6 | `<>` | right | string concatenation |
| 7 | `+` `-` | left | additive |
| 8 | `*` `/` `%` | left | multiplicative |
| 9 | `-` `not` | prefix | unary negation, boolean not |
| 10 | `.` | left | field access |

Examples:

```text
fn double(x: Int) -> Int = x * 2
fn add(a: Int, b: Int) -> Int = a + b

fn pipe_example() -> Int =
  5 |> double |> add(1)

# Pipe chains
# desugars to: add(double(5), 1)

# Boolean
fn bounded(x: Int) -> Bool = x > 0 and x < 100 or x == -1

# String concat
fn greeting() -> String = "hello" <> " " <> "world"

# Range
fn range_example() -> List(Int) = [1, 2, 3]

# Field access
rec Point
  x: Int
  y: Int

fn point_sum(point: Point) -> Int = point.x + point.y
```

## Literals

### Integers

```cure
42
0xFF
0b1010
1_000_000
```

### Floats

```cure
3.14
0.001
```

### Strings

Double-quoted, with interpolation via `#{}`:

```text
"hello"
"hello #{name}"
"result: #{compute(42)}"
```

### Booleans

```cure
true
false
```

### Atoms

Prefixed with `:`:

```cure
:ok
:error
:my_atom
```

### Empty list

```text
[]
```

### Chars

Single-quoted:

```cure
'a'
'Z'
```

### Lists

```text
[1, 2, 3]
["a", "b", "c"]
[]
```

Cons syntax for head/tail decomposition:

```cure
fn first(xs: List(Int)) -> Int =
  match xs
    [h | _t] -> h
    [] -> 0
```

Since v0.19.0, multi-head cons patterns desugar to right-associated
cons cells and work in both pattern and construction position:

```cure
fn first_three(xs: List(Int)) -> Int =
  match xs
    [a, b, c | _rest] -> a + b + c
    _ -> 0
```

is equivalent to `[a | [b | [c | rest]]]`.

### Tuples

Prefixed with `%`:

```text
%[1, "hello"]
%[x, y, z]
```

### Maps

Prefixed with `%`:

```text
%{name: "Alice", age: 30}
%{key: value}
```

### Binary literals and bitstring segments

Since v0.20.0, binary literals use the full Elixir-style segment
grammar. Each element inside `<<...>>` may carry type, size,
endianness, signedness, and unit specifiers, chained with `-`:

```text
<<tag::utf8, size::16, payload::binary-size(size), rest::binary>>
```

`::` introduces the specifier chain; type atoms are `integer`,
`float`, `bits`, `bitstring`, `bytes`, `binary`, `utf8`, `utf16`,
`utf32`; `big` / `little` / `native` select the endianness;
`signed` / `unsigned` the signedness; `size(n)` and `unit(u)` the
width. A bare integer is shorthand for `size(n)`:

```text
<<x::8>>             # same as <<x::size(8)>>
<<x::32-signed>>     # 32-bit signed big-endian integer
<<x::float-little>>  # 64-bit little-endian float
```

Defaults mirror Erlang:
`integer-unsigned-big-size(8)-unit(1)`, with `utf8` / `utf16` /
`utf32` providing their own implicit size. The same segment
grammar works in pattern position.

## Let bindings

Introduce local variables with `let`:

```cure
fn compute(x: Int) -> Int =
  let doubled = x * 2
  let offset = 10
  doubled + offset
```

`let` bindings are immutable. Each `let` introduces a new binding; there is no reassignment.

## Conditional dispatch

`pickup` is the canonical conditional expression:

```cure
fn abs(x: Int) -> Int =
  pickup
    x > 0 -> x
    else  -> 0 - x

fn sign(x: Int) -> String =
  pickup
    x > 0 -> "positive"
    x < 0 -> "negative"
    else  -> "zero"
```

Conditions are tested top-to-bottom and `else` is the fallback.

## Match expressions

Pattern match on values with `match`. Since v0.18.0 patterns
destructure arbitrary nesting across tuples, lists (cons and fixed),
maps, records, and ADT constructors.

### ADT constructors and cons

```text
fn unwrap(opt: Option(Int)) -> Int =
  match opt
    Some(v) -> v
    None -> 0

fn describe_list(xs: List(Int)) -> String =
  match xs
    [] -> "empty"
    [h | t] -> "starts with " <> Std.String.from_int(h)

fn handle(r: Result(Int, String)) -> Int =
  match r
    Ok(v) -> v
    Error(_) -> -1
```

Nullary constructors may be bare (`None`) or use empty parentheses (`None()`).
Bare PascalCase names resolve against the scrutinee type's constructors;
lowercase bare names remain variable bindings.

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

### Maps

```text
match request
  %{method: "GET", path: p} -> fetch(p)
  %{method: m, path: _}     -> reject(m)
```

Map keys in patterns must be literal. Open matching: unmentioned keys
are ignored.

### Tuples and nested destructuring

Any combination of the above nests:

```text
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  %[Ok(v), Error(_)]              -> v
  _                               -> default
```

### The pin operator `^x`

`^x` compares against an already-bound variable rather than binding
fresh. The compiler lowers it to a synthetic equality guard.

```text
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```

### Repeated variables

A name that occurs more than once in the same pattern must match the
same value at every position:

```text
match pair
  %[x, x] -> :equal
  _       -> :different
```

### Exhaustiveness

The compiler checks pattern exhaustiveness. Shallow coverage gaps are
reported as `E004`; nested gaps in tuple scrutinees (e.g. `%[Ok(_)]`
but no `%[Error(_)]`) are reported as `E025` with a concrete missing
witness.

See the dedicated [Patterns reference](https://github.com/cure-lang/cure-lang/blob/main/docs/PATTERNS.md)
for the full AST-to-Erlang mapping.

## Pipe operator

The pipe operator `|>` passes the result of the left expression as the first argument to the function on the right:

```cure
fn process(xs: List(Int)) -> Int =
  xs
  |> Std.List.filter(fn(x) -> x > 0)
  |> Std.List.map(fn(x) -> x * 2)
  |> Std.List.sum()
```

## ADTs (algebraic data types)

Define sum types with `type`:

```cure
type Color = Red | Green | Blue

type Option(T) = Some(T) | None

type Result(T, E) = Ok(T) | Error(E)

type Shape = Circle(Float) | Rectangle(Float, Float) | Point
```

Use constructors as regular functions:

```text
fn wrap(x: Int) -> Option(Int) = Some(x)
fn nothing() -> Option(Int) = None()
fn make_color() -> Color = Red()

fn safe_divide(a: Int, b: Int) -> Result(Int, String) =
  if b == 0 then Error("division by zero") else Ok(a / b)
```

Destructure ADTs with `match`:

```cure
fn unwrap_or(opt: Option(Int), default: Int) -> Int =
  match opt
    Some(v) -> v
    None() -> default
```

## Records

Records are named product types. They compile to BEAM maps and are
fully type-checked: the compiler tracks field names and types for
each `rec` definition.

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

All field types must be named. `Any` is accepted as an escape hatch but
forfeits field-level type checking for that field.

### Parameterized records

Records can take type parameters:

```cure
rec Pair(A, B)
  first: A
  second: B
```

Type parameters are erased at runtime but used by the type checker.

### Construction

Use `TypeName{field: expr, ...}` to build a record value:

```text
fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
fn origin() -> Point = Point{x: 0, y: 0}
fn make_person(name: String, age: Int) -> Person =
  Person{name: name, age: age}
fn make_pair(a: Any, b: Any) -> Pair(Any, Any) = Pair{first: a, second: b}
```

Fields can appear in any order. The type checker verifies each value type
against the declared field type.

### Field access

Dot notation `record.field` looks up a field at runtime via `maps:get/2`:

```text
fn x_coord(p: Point) -> Int = p.x
fn y_coord(p: Point) -> Int = p.y
fn person_name(p: Person) -> String = p.name
fn area(r: Rectangle) -> Int = r.width * r.height
```

Nested access chains multiple `.` operations:

```text
fn rect_origin_x(r: Rectangle) -> Int = r.origin.x
```

### Record update

Produce a modified copy using `TypeName{base | field: val, ...}`.
Only the listed fields change; all others are preserved unchanged:

```text
# Single-field update
fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}

# Multi-field update
fn translate(p: Point, dx: Int, dy: Int) -> Point =
  Point{p | x: p.x + dx, y: p.y + dy}
fn move(p: Point, nx: Int, ny: Int) -> Point =
  Point{p | x: nx, y: ny}
```

The type name before `{` is required. The base expression must have the same
record type. The compiler checks each override value against its declared
field type and returns the same named type.

Record update compiles to the BEAM map-update instruction (`Map#{key := val}`),
which copies the map and overwrites only the specified keys. The `__struct__`
field is preserved automatically.

### Records in computations

```text
fn distance_squared(a: Point, b: Point) -> Int =
  let dx = b.x - a.x
  let dy = b.y - a.y
  dx * dx + dy * dy

fn midpoint(a: Point, b: Point) -> Point =
  Point{x: (a.x + b.x) / 2, y: (a.y + b.y) / 2}

fn older_of(a: Person, b: Person) -> Person =
  pickup
    a.age > b.age -> a
    else          -> b

fn greet(p: Person) -> String = "Hello, " <> p.name
```

## Interfaces

Interfaces provide ad-hoc polymorphism. Define with `interface`, implement
with `implementation`, and state generic obligations with `requires`:

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

implementation Show for Bool
  fn show(x: Bool) -> String =
    pickup
      x    -> "true"
      else -> "false"

implementation Show for String
  fn show(x: String) -> String = x

fn display(x: t) -> String requires Show(t) = show(x)
```

Resolution is compile-time and uses canonical interface and implementation
identities. See the dedicated [Interfaces](/docs/protocols) guide.

## Imports

Import modules with `use`:

```cure
mod MyApp
  use Std.List
  use Std.Core

  fn double_all(xs: List(Int)) -> List(Int) =
    Std.List.map(xs, fn(x) -> x * 2)
```

Import multiple modules from the same namespace:

```cure
use Std.{List, Core, Math}
```

## FFI (Foreign Function Interface)

Call Erlang/OTP functions with the `@extern` attribute:

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int

@extern(:math, :sqrt, 1)
fn sqrt(x: Float) -> Float

@extern(:erlang, :integer_to_binary, 1)
fn int_to_string(n: Int) -> String

@extern(:io, :put_chars, 1)
fn print(s: String) -> Atom
```

The three arguments are the Erlang module atom, the function atom, and the arity. The compiler generates a wrapper that delegates to the Erlang function.

## Lambdas

Anonymous functions use `fn` without a name:

```cure
fn double_all(xs: List(Int)) -> List(Int) =
  Std.List.map(xs, fn(x) -> x * 2)

fn apply_twice(f: Int -> Int, x: Int) -> Int = f(f(x))

fn make_adder(n: Int) -> Int -> Int = fn(x) -> x + n
```

Lambdas with multiple arguments:

```text
Std.List.foldl(xs, 0, fn(x) -> fn(acc) -> acc + x)
```

Note: curried style -- each `fn` takes one argument and returns the next function.

## String interpolation

Embed expressions inside strings with `#{}`:

```cure
fn greet(name: String, age: Int) -> String =
  "Hello, #{name}! You are #{Std.String.from_int(age)} years old."
```

Any expression can appear inside `#{}`.

## Invariants and dependent types

The `{x: t | predicate}` refinement former elaborates to a dependent pair
(`Sigma(t, predicate)`) that the kernel checks like any other type. A value
whose obligation reduces to a closed, true proposition is accepted with no
explicit proof term; an obligation that depends on a bound parameter is
discharged by proof search over in-scope hypotheses and `@lemma`-tagged
theorems. Guards still narrow branches and drive coverage diagnostics; the
separate Z3-backed `GuardLint` checks guard coverage and shadowing as a lint
outside the trusted kernel and plays no part in refinement discharge.

See the [Type System](/pages/type-system) page for indexed families,
quantitative binders, and kernel-checked equality.

## User-defined syntax

Macros declare surface grammar with `syntax ... becomes`. Holes are typed,
repeatable, and hygienic:

```text
syntax beam_ops tell <dest: Code> <message: Code>
  becomes Std.Otp.tell(dest, message)
```

`quote` builds syntax and `$(...)` splices values into it:

```text
let ast = quote %[:ok, $(payload)]
```

`computed by` invokes a typed elaborator for expansions that cannot be
expressed as a template. `Std.Syntax` provides lossless reflection. Expanded
declarations keep invocation and definition provenance and enter the same
canonical module interface as authored declarations.

## Editions and migration

`@edition` and `[project].edition` select a project's grammar. Use
`cure migrate` to cross editions:

```bash
cure migrate --check src
cure migrate --print src/old.cure
cure migrate --strict src
```

Migration rewrites retired keywords, conditional syntax, type-variable casing,
decorator placement, and renamed modules to the current surface.

## FSMs (Finite State Machines)

`fsm` is a macro from `Std.Fsm`, brought into scope with `use Std.Fsm`. A
transition table derives its state and event types from the rows themselves;
states and events are capitalised constructors.

```cure
use Std.Fsm

fsm TrafficLight with Int
  Red    --Timer-->     Green
  Green  --Timer-->     Yellow
  Yellow --Timer-->     Red
  *      --Emergency--> Red
```

See the [Finite State Machines](/pages/finite-state-machines) page for the full guide.

## Comments

Line comments start with `#`:

```cure
# This is a comment
fn add(a: Int, b: Int) -> Int = a + b  # inline comment
```

## Complete example

```text
mod MyApp.Math
  use Std.{Result, Option}

  type Sign = Positive | Negative | Zero

  fn factorial(n: Int) -> Int
    | 0 -> 1
    | n -> n * factorial(n - 1)

  fn classify(x: Int) -> Sign
    | x when x > 0 -> Positive
    | x when x < 0 -> Negative
    | _             -> Zero

  fn safe_divide(a: Int, b: {x: Int | x != 0}) -> Int = a / b

  fn sum(xs: List(Int)) -> Int =
    Std.List.foldl(xs, 0, fn(x) -> fn(acc) -> acc + x)

  fn main() -> Int = factorial(10)
```
