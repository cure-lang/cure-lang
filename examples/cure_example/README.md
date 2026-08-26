# CureExample

A simple Elixir/Mix application demonstrating interoperability with
[Cure](https://github.com/Oeditus/cure) -- a dependently-typed language
that compiles to BEAM bytecode.

## Project Structure

```
cure_example/
  cure_src/            -- Cure source files (.cure)
    greeter.cure       -- String-based greeting functions
    calculator.cure    -- Arithmetic, pattern matching, guards, Result types
  lib/
    cure_example.ex    -- Elixir module that calls into compiled Cure modules
  test/
    cure_example_test.exs
```

## How It Works

1. Cure compiles `.cure` files to `.beam` bytecode (just like Erlang or Elixir).
2. A `mod Calculator` in Cure becomes the BEAM module `:calculator`.
3. Functions are callable with the standard Erlang-style `:module.function(args)` syntax.
4. The `mix compile` alias runs `mix cure.compile` first, then the standard Elixir compiler.

## Usage

```bash
# Fetch dependencies (pulls in cure)
mix deps.get

# Compile everything (cure sources + elixir)
mix compile

# Run the demo
mix run -e "CureExample.demo()"

# Run tests
mix test
```

## Cure Language Highlights

Pattern matching with multi-clause functions:

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

Guards:

```cure
fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

Result types:

```cure
fn safe_divide(a: Int, b: Int) -> Result(Int, String) =
  pickup
    b == 0 -> Error("division by zero")
    else -> Ok(a / b)
```

These compile to standard BEAM tuples (`{:ok, value}` / `{:error, reason}`)
that Elixir can pattern match on directly.
