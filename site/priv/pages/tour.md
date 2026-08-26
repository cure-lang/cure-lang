%{
  title: "Language Tour",
  description: "A short tour of Cure's syntax, types, and BEAM foundations.",
  order: 2
}
---
# A tour of Cure

Cure is a typed language for building reliable systems on the BEAM. This tour
is deliberately short: each example introduces one idea and points to the
guide where you can keep going.

## 1. Start with typed functions

A Cure module is a named collection of declarations. Functions state the
types they accept and return:

```cure
mod Tour.Greetings

fn greet(_name: String) -> String = "Hello, Cure!"

fn main() -> String = greet("Cure")
```

The compiler checks the call before generating BEAM code. Try the complete
workflow in [Getting Started](/getting-started).

## 2. Give data a shape

Algebraic data types describe the values a function can receive. Pattern
matching then handles each shape explicitly:

```cure
mod Tour.Shapes

type Shape = Circle(Float) | Rectangle(Float, Float)

fn area(shape: Shape) -> Float =
  match shape
    Circle(radius) -> 3.14159 * radius * radius
    Rectangle(width, height) -> width * height
```

When a case is missing, Cure reports it while you are writing the program.
Read the [pattern matching guide](/match) for nested patterns, guards, and
exhaustiveness.

## 3. Put an invariant in the type

Refinement types let a function state a condition that must hold for its
inputs:

```cure
mod Tour.SafeArithmetic
  use Std.Proof.IntMath

  type NonZero = {x: Int | x != 0}

  fn safe_divide(value: Int, divisor: NonZero) -> Int = value / divisor
```

The division function does not need a runtime zero check. A caller must first
provide a value that satisfies `NonZero`, and the compiler checks that proof.
The [type system guide](/type-system) explains refinements, dependent types,
and implicit arguments in more detail.

## 4. Build for the BEAM

Cure's concurrency model is designed around OTP. Actors, supervisors,
applications, and finite-state machines are language-level building blocks,
compiled to the same BEAM runtime used by Erlang and Elixir.

- [Finite State Machines](/finite-state-machines)
- [Actors and supervision](/actors)
- [Applications and releases](/applications)

## Keep exploring

- [Getting Started](/getting-started) for installation and the CLI loop
- [Language Guide](/language-guide) for the complete syntax
- [Standard Library](/stdlib) for source-generated API documentation
- [REPL](/repl) for interactive local exploration
