%{
  title: "Getting Started",
  description: "Install Cure and run your first typed BEAM program.",
  order: 1
}
---
## Before you begin

Cure currently builds from source. You will need:

- **Elixir** 1.18 or later and a compatible **Erlang/OTP** installation
- **Git**
- **Z3**, optional, for the compiler's SMT-backed checks

If you already have Elixir and Git, you can be running Cure in a few minutes.

## Install Cure

Clone the repository and build the compiler:

```bash
git clone https://github.com/cure-lang/cure-lang.git
cd cure-lang
mix deps.get
mix compile
mix cure.escript
```

The last command creates a `cure` executable in the project root. Put it on
your `PATH` if you want to use it from other projects:

```bash
cp cure ~/.local/bin/
cure version
```

## Write a program

Create `hello.cure`:

```cure
mod Hello

fn greet(_name: String) -> String = "Hello, Cure!"

fn main() -> String = greet("Cure")
```

Every Cure source file declares a module. Functions have explicit parameter
and result types, and the final expression is the function's result.

## Check, compile, and run

Start with a type check. This validates the program without writing BEAM
output:

```bash
cure check hello.cure
```

Compile and run it:

```bash
cure compile hello.cure
cure run hello.cure
```

Compilation runs the full pipeline and publishes a verified artifact generation
under `_build/cure/project/ebin/`.

`cure run` compiles the source, loads the resulting BEAM module, and calls
`main/0`. You should see:

```text
"Hello, Cure!"
```

The compiler reports parse errors, type errors, warnings, and their error
codes in one place. When an error code is unfamiliar, ask Cure for its full
explanation:

```bash
cure explain E093
```

## Try the standard library

The standard library is written in Cure and ships with the repository. Browse
the generated reference at [/stdlib](/stdlib), or compile it locally:

```bash
cure stdlib
```

The same source comments power the website and the local documentation build:

```bash
cure doc lib/std -o _build/cure/doc
```

Open `_build/cure/doc/index.html` to browse the local copy.

## Explore Cure by intent

- [Language Guide](/language-guide) for syntax, functions, modules, and pattern matching
- [Type System](/type-system) for refinements and dependent types
- [Finite State Machines](/finite-state-machines) for verified state transitions
- [Actors](/actors) for typed supervision trees and BEAM processes
- [Applications](/applications) for OTP application structure and releases
- [Standard Library](/stdlib) for source-generated module and API documentation

## Choose your tools

The compiler includes a terminal REPL, an LSP, and an MCP server for editor
and assistant integrations. The [Tooling guide](/tooling) covers installation
and configuration without interrupting this first-run path.

For an interactive introduction, take the [Language Tour](/tour), then use
the local REPL for open-ended exploration.

## Build something larger

Once the hello-world loop feels familiar, try one of the repository examples:

```bash
cure run examples/dependent_types.cure
cure check examples/match_showcase.cure
```

Then follow the [type system guide](/type-system) or the [actors guide](/actors)
to see how Cure's static checks scale from one function to a supervised BEAM
system.
