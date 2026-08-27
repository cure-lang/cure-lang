# Getting Started

This document takes a new Cure project from an empty directory to a compiled,
running, tested program. The worked example is a four-function calculator; it
ships as [`examples/cure_calc/`](../examples/cure_calc) and every command and
transcript below was produced by running it.

Nothing here assumes prior Cure knowledge. It does assume a working Erlang/OTP
and Elixir installation, because Cure's compiler is an Elixir application and
its output is BEAM bytecode.

Contents:

1. [Installing the toolchain](#1-installing-the-toolchain)
2. [How the compiler finds the standard library](#2-how-the-compiler-finds-the-standard-library)
3. [Creating a project](#3-creating-a-project)
4. [The project manifest](#4-the-project-manifest)
5. [Writing the calculator](#5-writing-the-calculator)
6. [Type-checking](#6-type-checking)
7. [Compiling](#7-compiling)
8. [Running](#8-running)
9. [Testing](#9-testing)
10. [Formatting, documentation, and the REPL](#10-formatting-documentation-and-the-repl)
11. [Dependencies](#11-dependencies)
12. [Applications and releases](#12-applications-and-releases)
13. [Troubleshooting](#13-troubleshooting)
14. [Where to go next](#14-where-to-go-next)

## 1. Installing the toolchain

Cure has no installer yet: you build the compiler from a checkout and use the
resulting escript.

```bash
git clone https://github.com/cure-lang/cure-lang.git cure
cd cure
mix deps.get
mix compile
mix escript.build
```

`mix compile` also compiles the self-hosted standard library (79 modules under
`lib/std/`) into `_build/cure/ebin/`. `mix escript.build` produces a single
executable `cure` in the repository root:

```bash
./cure version
```

```text
Cure 0.34.0
```

Put it on your `PATH` for the rest of this document. The recommended form
exports `CURE_HOME` as well, because that is what lets the escript resolve the
standard library from any working directory:

```bash
export CURE_HOME=/path/to/cure
alias cure=$CURE_HOME/cure
```

Run `cure help` for the full subcommand list. The commands used below are
`new`, `check`, `compile`, `run`, `test`, `fmt`, `doc`, `deps`, `repl`, and
`doctor`. Every one of them has a Mix-task twin inside the Cure checkout
(`mix cure.compile`, `mix cure.release`, ...), which is what CI uses.

### Verify the installation

```bash
cure doctor
```

`cure doctor` reports the environment, the project (if the current directory has
a `Cure.toml`), and per-file source health:

```text
Cure Doctor report
========================================
[ ok ]  DOC-ENV-01
     Elixir 1.20.3 / OTP 29

[ ok ]  DOC-ENV-Z3
     Z3 at /usr/bin/z3
...
OK -- nothing to fix.
```

Z3 is optional. It backs untrusted SMT diagnostics only; the trusted dependent
kernel never asks a solver for permission.

## 2. How the compiler finds the standard library

Cure resolves `use Std.List` from **source**, and loads `Cure.Std.List.beam`
at **run time**. Those are two separate lookups, and knowing the order saves an
afternoon:

Source directories, in search order:

1. `Application.get_env(:cure, :stdlib_source_dir)`
2. `<priv_dir>/std` -- the bundled copy inside the compiled `:cure` application
3. `$CURE_HOME/priv/std`, then `$CURE_HOME/lib/std`
4. `lib/std` relative to the current directory

BEAM directories, in search order:

1. `Application.get_env(:cure, :stdlib_beam_dir)`
2. `_build/cure/ebin` of the checkout that contains the running compiler
3. `<priv_dir>/ebin`
4. `$CURE_HOME/priv/ebin`, then `$CURE_HOME/_build/cure/ebin`
5. `_build/cure/ebin` relative to the current directory

A project can override the BEAM location explicitly, which is the escape hatch
when several Cure checkouts coexist:

```toml
[compiler]
stdlib_path = "/path/to/cure/_build/cure/ebin"
```

`$CURE_LIB` does the same thing from the environment. `cure new` prints the
resolution it detected, so a fresh scaffold tells you where its stdlib will come
from.

## 3. Creating a project

```bash
cure new cure_calc
cd cure_calc
```

```text
Created Cure project `cure_calc`

Template: **lib** (`cure new --lib`).

Files written
- `cure_calc/Cure.toml`
- `cure_calc/.gitignore`
- `cure_calc/README.md`
- `cure_calc/lib/main.cure`
- `cure_calc/test/main_test.cure`

Next steps

    cd cure_calc
    cure deps
    cure run lib/main.cure
    cure test
```

It also prints the stdlib resolution it detected, so a fresh scaffold tells you
which checkout its `Std.*` modules will come from.

The scaffold is deliberately thin:

    cure_calc/
      Cure.toml              project manifest
      .gitignore             ignores /_build/, /Cure.lock, *.beam
      README.md
      lib/main.cure          mod Cure_calc with hello/0 and main/0
      test/main_test.cure    mod Cure_calc.Test with one assertion

`cure new` accepts a template selector: `--lib` (the default, above), `--app`
for a project with an `app` container and a root supervisor, and `--fsm` for one
with a starter state machine. `cure init <name>` is an alias for
`cure new <name> --lib`.

A scaffolded project runs and passes its own test immediately:

```bash
cure run lib/main.cure
```

```text
hello from cure_calc
```

```bash
cure test
```

```text
  PASS test/main_test.cure: test_hello
1 passed, 0 failed
```

### Creating a project by hand

`cure new` writes no magic. A directory is a Cure project when it contains a
`Cure.toml`; everything else is convention:

```bash
mkdir -p cure_calc/lib cure_calc/test
cd cure_calc
cat > Cure.toml <<'TOML'
[project]
name = "cure_calc"
version = "0.1.0"
edition = "2026"
TOML
```

## 4. The project manifest

`Cure.toml` is parsed by a deliberately small TOML subset: scalar strings,
booleans, integers, string arrays, and nested tables such as
`[application.env]`. The full surface a project may declare:

```toml
[project]
name         = "cure_calc"
version      = "0.1.0"
edition      = "2026"          # language edition; see below
source_paths = ["lib"]         # where the project's own .cure modules live

[dependencies]
# utils = { path = "../shared/utils" }
# json  = { git = "https://github.com/someone/json.cure", tag = "v1.0.0" }
# http  = { version = ">= 1.2.0" }

[compiler]
type_check   = false
optimize     = false
# stdlib_path = "/path/to/cure/_build/cure/ebin"

[doc]
title = "cure_calc"
main  = "Calc"

[application]                  # only for projects with an `app` container
name         = "cure_calc"
vsn          = "0.1.0"
description  = ""
applications = ["logger"]
start_phases = []

[application.env]
# port = 4000

[release]
name         = "cure_calc"
vsn          = "0.1.0"
include_erts = false
```

Two fields deserve attention.

**`edition`** pins the language surface the project is read against. Editions
are calendar-named (`"2026"` is the only one so far, and the current default).
Omitting it is legal but warned about on every command:

```text
[warning] no `edition` declared in Cure.toml -- add `edition = "2026"` under
[project] to pin the language surface this project reads against
```

A single file can override the project with a leading `@edition("2026")`
pragma. Precedence is pragma, then manifest, then compiler default. An unknown
edition is an error, not a silent downgrade.

**`source_paths`** is how the compiler knows which directories hold the
project's own modules. It defaults to `["lib"]`. Import resolution searches
these roots by *declared module name*, not by filename, so
`lib/calculator_core.cure` may declare `mod Calc` and `use Calc` will still find
it. The example project takes advantage of this: `lib/calc.cure` declares
`mod Calc`, and `lib/main.cure` declares `mod Calc.Demo`.

## 5. Writing the calculator

Replace the scaffolded `lib/main.cure` with two modules: the calculator itself
and a small entry point. The complete sources are in
[`examples/cure_calc/`](../examples/cure_calc); the parts worth explaining
follow.

### The data model

```cure
mod Calc
  use Std.Result

  type Op =
    | OpAdd
    | OpSub
    | OpMul
    | OpDiv

  type Expr =
    | Lit(Float)
    | Neg(Expr)
    | Bin(Op, Expr, Expr)

  fn eval(e: Expr) -> Result(Float, String) =
    match e
      Lit(x)        -> Ok(x)
      Neg(a)        -> negate(eval(a))
      Bin(op, a, b) -> apply_op(op, eval(a), eval(b))

  local fn negate(r: Result(Float, String)) -> Result(Float, String) =
    match r
      Ok(x)    -> Ok(0.0 - x)
      Error(m) -> Error(m)

  local fn apply_op(op: Op, left: Result(Float, String), right: Result(Float, String)) -> Result(Float, String) =
    match left
      Error(m) -> Error(m)
      Ok(x) ->
        match right
          Error(m) -> Error(m)
          Ok(y)    -> compute(op, x, y)

  fn compute(op: Op, x: Float, y: Float) -> Result(Float, String) =
    match op
      OpAdd() -> Ok(x + y)
      OpSub() -> Ok(x - y)
      OpMul() -> Ok(x * y)
      OpDiv() -> safe_div(x, y)

  fn safe_div(x: Float, y: Float) -> Result(Float, String) =
    pickup
      y == 0.0 -> Error("division by zero")
      else     -> Ok(x / y)
```

- `mod Calc` opens a module. Cure is indentation-structured: the module body is
  everything indented under it, and there is no closing delimiter.
- `use Std.X` imports a standard-library module. Imports are not ambient: `Ok`
  and `Error` come from `Std.Result`, and a missing `use` is reported as an
  unknown constructor, not as a mysterious arity error.
- `type` declares an algebraic data type. The multi-line form with a leading
  `|` on each variant is equivalent to the single-line
  `type Op = OpAdd | OpSub | ...`.
- `Expr` mentions itself, so an expression is a tree. Recursive families are
  checked for strict positivity by the kernel, which is what makes recursion
  over them certifiable.
- `fn name(args) -> Type = body` is a function. The return type is mandatory on
  public functions and is what the bidirectional checker checks the body
  against.
- `match` scrutinises a value. Every constructor of `Expr` (and, inside
  `compute/3`, of `Op`) has an arm; leaving one out is a compile-time error
  rather than a runtime `badmatch`.
- `pickup` is guarded branching: the first true guard wins, and `else` is the
  fallback. It is an expression, so it is the function's body.
- Division by zero is a `Result` value. Nothing in the evaluator can raise, so
  `eval/1` is total -- and the totality checker can see that it recurses only
  into strictly smaller sub-trees.
- `local fn` (`negate/1` and `apply_op/3` here) is private to the module.

### Reaching another module

This is an excerpt from `lib/main.cure` in the full example -- shown as `text`
here because it depends on `Calc` from the sibling file above, which this
document cannot compile in isolation:

```text
mod Calc.Demo
  use Std.Io
  use Calc

  ## Print a short transcript.
  fn main() -> Atom =
    let _: Unit = Std.Io.println(Calc.explain(sum_and_product()))
    :ok

  local fn sum_and_product() -> Expr =
    Calc.add(Calc.lit(2.0), Calc.mul(Calc.lit(3.0), Calc.lit(4.0)))
```

- `use Calc` imports a *project* module exactly the way `use Std.List` imports a
  standard-library one. It is resolved from source through the project's source
  roots; nothing is registered anywhere.
- `main/0` is what `cure run` calls. Returning `:ok` prints nothing extra; any
  other value is inspected by the runner.
- `let _: Unit = ...` is an annotated binding. `Std.Io.println/1` is effectful
  (`-> Unit ! Io`), and the checker asks for the expected type when it cannot
  synthesise one for a discarded initializer. A bare `let _ = println(...)` is
  rejected with a message that says exactly that.
- `##` comments are documentation. `cure doctor` flags a public function without
  one, and `cure doc` renders them.

### Talking to Erlang

```cure
  ## Fixed-point rendering of a float: `14.0` prints as `14.0000`.
  fn show(f: Float) -> String = Std.String.from_characters(float_to_cl(f, [%[:decimals, 4]]))

  @extern(:erlang, :float_to_list, 2)
  local fn float_to_cl(f: Float, opts: List(Tuple(Atom, Int))) -> List(Char)
```

`@extern(module, function, arity)` declares a foreign function: a typed head
with no body. `%[:decimals, 4]` is a tuple literal, so the option list is
Erlang's `[{decimals, 4}]`.

Note the conversion. Cure's `String` is a nominal type stored as a list of code
points, not a BEAM binary, so an extern that returns a charlist is adapted with
`Std.String.from_characters/1`. An extern typed as returning `String` while
actually returning a binary compiles and then fails at run time inside
`Std.String`. See [`docs/FFI.md`](FFI.md).

## 6. Type-checking

`cure check` runs the front end and the dependent elaborator and stops: no Core
is erased, no BEAM is written, nothing is loaded.

```bash
cure check lib/calc.cure
```

```text
lib/calc.cure: OK
```

It resolves the project's other modules the same way a real compile does, so
checking a file that imports a sibling works, as does checking a test module:

```bash
cure check lib/main.cure
cure check test/calc_test.cure
```

Diagnostics are structured, carry a stable code, and point at the offending
span. A missing `use Std.Result`, for instance:

```text
-- UNKNOWN CONSTRUCTOR [E091] ----------------------------------- lib/probe.cure

`Ok` is not available in this constructor namespace.

The matched type provides `Ok`, `Error`.

at lib/probe.cure:9:7
9 |       Ok(v)    -> "= " <> Std.String.from_float(v)
  |       ^^ `Ok` was not found

Hint: Did you mean `Ok`?
```

`cure explain E091` prints the long-form explanation of any code, and
`cure explain` with no argument lists them all.

For an editor loop, `cure watch lib/ --action check` re-checks on every save.
`cure lsp` starts the language server.

## 7. Compiling

```bash
cure compile lib/
```

```text
  -> Cure.Calc
  -> Cure.Calc.Demo
```

`cure compile` accepts files or directories. Each `.cure` module becomes one
BEAM module whose name is the declared module prefixed with `Cure.`: `mod Calc`
loads as `:"Cure.Calc"`. That prefix is what keeps Cure modules from colliding
with Erlang, Elixir, or OTP modules in the same VM.

Output goes to `_build/cure/project/ebin` by default (`--output-dir` overrides
it). The directory is content-addressed rather than a flat pile of `.beam`
files:

```text
_build/cure/project/ebin/
  current                                  <- digest of the live generation
  .cure_generations/<digest>/
    Cure.Calc.beam
    Cure.Calc.Demo.beam
    Calc.cureinterface                     <- checked module interface
    Calc.Demo.cureinterface
    .cure_manifest
  .cure_interface_cache/                   <- imported interfaces, incl. stdlib
```

A generation is only published when the whole set verifies, and the `.beam`
files are loaded through that manifest rather than by adding the directory to
the Erlang code path. Two consequences worth knowing:

- Recompilation is incremental. Only modules whose interface or body hash
  changed are rebuilt; `--verbose` prints the reason each one was.
- To load the output in a plain `erl` or `iex` session, point the code path at
  the live generation, not at the `ebin` root:

```bash
erl -pa "_build/cure/project/ebin/.cure_generations/$(cat _build/cure/project/ebin/current)" \
    -pa "$CURE_HOME/_build/cure/ebin" -noshell \
    -eval "io:format(\"~p~n\", ['Cure.Calc':eval('Cure.Calc':lit(2.5))]), init:stop()."
```

```text
{ok,2.5}
```

In practice `cure run`, `cure test`, and `cure release` do this for you, and
Elixir projects consume Cure output through `mix cure.compile` instead.

The pipeline behind that one line of output is:

```text
.cure source
  -> Lexer            tokens, indentation, interpolation
  -> Parser           MetaAST 3-tuples (Metastatic format)
  -> Elab.Program     dependent elaboration, imports, totality
  -> Core.Kernel      trusted validation of dependent Core
  -> Elab.Erase       erase proofs and index arguments by usage grade
  -> Elab.Emit        Erlang abstract forms
  -> BeamWriter       .beam
```

Every stage emits structured events through `Cure.Pipeline.Events`, which is how
the LSP, profilers, and `cure top` observe a build in progress.

## 8. Running

```bash
cure run lib/main.cure
```

```text
cure_calc -- a four-function calculator in Cure

(2.0000 + (3.0000 * 4.0000)) = 14.0000
((7.0000 + 8.0000) / 2.0000) = 7.5000
-(10.0000 - 4.0000) = -6.0000
(1.0000 / 0.0000) ! division by zero
```

`cure run` does four things: loads the standard library and any dependency
artifacts, compiles and loads the project's own `lib/`, compiles the file it was
given, then calls its `main/0`. The third step matters for multi-module
projects -- `lib/main.cure` calling into `lib/calc.cure` needs `Cure.Calc`
loaded, not merely resolvable.

A file with no `main/0` is reported rather than silently doing nothing:

```text
Module Cure.Calc compiled (no main/0 function)
```

Outside a project (no `Cure.toml` anywhere above the file), `cure run` is a
single-file script runner. That is how the loose examples work:

```bash
cure run examples/hello.cure
```

## 9. Testing

`cure test` compiles and loads `lib/`, then compiles every `test/**/*.cure` and
calls each exported zero-arity function whose name starts with `test`. A test
passes when it returns and fails when an assertion raises.

Another excerpt, this time from `test/calc_test.cure`, again shown as `text`
because it depends on `Calc`:

```text
mod Calc.Test
  use Std.Test
  use Std.Result
  use Calc

  fn test_addition() -> Unit =
    Std.Test.assert_eq(Calc.eval_or(Calc.add(Calc.lit(1.0), Calc.lit(2.0)), 0.0), 3.0)

  fn test_division_by_zero_is_a_value() -> Unit =
    let e = Calc.ratio(Calc.lit(1.0), Calc.lit(0.0))
    Std.Test.assert(Std.Result.is_error(Calc.eval(e)))
```

```bash
cure test
```

```text
  PASS test/calc_test.cure: test_addition
  PASS test/calc_test.cure: test_precedence_is_explicit_in_the_tree
  PASS test/calc_test.cure: test_subtraction_and_negation
  PASS test/calc_test.cure: test_division
  PASS test/calc_test.cure: test_division_by_zero_is_a_value
  PASS test/calc_test.cure: test_errors_short_circuit
  PASS test/calc_test.cure: test_rendering
  PASS test/calc_test.cure: test_explain_reports_failures
8 passed, 0 failed
```

The assertion helpers return `Unit`, so a test's declared return type is `Unit`.
`Std.Test` also provides `assert_ne`, `assert_gt`, `assert_lt`, and
property-based testing with `forall`, `forall_default`, and the shrinking
variants `forall_shrunk` / `forall_shrunk_default`; generators live in
`Std.Gen`. `examples/test_showcase.cure` exercises all of them.

Useful flags:

- `cure test --filter division` runs only matching test names.
- `cure test --doctests` also runs the `## ```cure` fences in `lib/**/*.cure`.
- `cure test --cover` writes `_build/cure/cover/index.html`.
- `cure bench` runs `bench/**/*.cure` benchmarks (`bench*`-prefixed functions).

A non-zero exit status on failure makes all of this usable directly in CI.

## 10. Formatting, documentation, and the REPL

```bash
cure fmt lib/ test/          # rewrite in place (algebra formatter)
cure fmt --check lib/ test/  # report unformatted files, exit non-zero
```

```text
All files are formatted
```

```bash
cure doc lib/
```

```text
Generating documentation for 2 files
Documentation written to _build/cure/doc/ (2 modules, 0 extras)
```

`cure doc` builds an ExDoc-like two-pane site from `##` comments, driven by the
`[doc]` table in `Cure.toml` (`title`, `main`, `extras`, groups). See
[`docs/DOC.md`](DOC.md).

The REPL evaluates expressions, accepts top-level declarations, and answers
questions about types:

```bash
cure repl
```

```text
Cure REPL v0.34.0  (type :help for commands, :quit to exit)
cure(1)> 1 + 1
=> 2
cure(2)> :t 42
42 : Int
cure(2)> fn twice(x: Int) -> Int = x + x
defined twice/1
cure(3)> twice(21)
=> 42
cure(4)> :quit

Bye.
```

`:t` shows a type, `:effects` an effect row, `:holes` the open holes, `:fmt`
formats, `:ast` dumps the parse, `:bench` times an expression, `:load` compiles
a file into the session, and `:help` lists everything. History persists in
`~/.cure_history`.

One current limitation is worth knowing before you go looking for the mistake in
your own code: `:load lib/calc.cure` reports `loaded lib/calc.cure -> Cure.Calc`,
but the loaded project module's functions are not yet reachable as `Calc.eval`
from the prompt -- the reference is rejected with `UNKNOWN VALUE [E091]`. Drive
project code through `cure run` and `cure test` for now, and use the REPL for
expressions, declarations, and type queries. See [`docs/REPL.md`](REPL.md).

## 11. Dependencies

Declare dependencies in `Cure.toml` and resolve them with `cure deps`:

```toml
[dependencies]
utils = { path = "../shared/utils" }
json  = { git = "https://github.com/someone/json.cure", tag = "v1.0.0" }
http  = { version = ">= 1.2.0" }
```

```bash
cure deps         # resolve, compile, and write Cure.lock
cure deps update  # re-resolve git dependencies
cure deps tree    # print the dependency tree
```

With none declared:

```text
No dependencies declared in Cure.toml; lockfile is up to date.
```

Path dependencies compile from their own `lib/`; git and registry dependencies
are installed under `_build/deps/`. Each is compiled under *its own* edition,
never the consumer's. `Cure.lock` pins the resolved set and belongs in version
control. `cure search`, `cure info`, and `cure publish` talk to the package
registry; see [`docs/PACKAGE_REGISTRY.md`](PACKAGE_REGISTRY.md) and
[`docs/PUBLISHING.md`](PUBLISHING.md).

## 12. Applications and releases

A calculator needs no supervision tree. When a project grows into a long-running
system, the next steps are an `app` container, a root `sup`, and typed actors:

```text
use Std.App
use Std.Supervisor

sup Root
  strategy OneForOne()
  children
    worker Counter as counter

app Demo
  root Root
```

The compiler allows exactly one `app` container per project and cross-checks its
name against `[application].name` in `Cure.toml`. `cure release` (or
`mix cure.release`) packages the output as a bootable BEAM release under
`_build/cure/rel/<name>/`.

The example above is shown as `text`, not `cure`: `app`, `sup`, and `actor` are
computed macros, and driving their expansion outside a Mix build is a known gap
(see the troubleshooting entry below). These containers are macros from the
standard library, and the fully worked projects are the reference:
`examples/cure_forge/` for an application and supervision tree,
`examples/cure_colony/` for actors and supervisors, and
`examples/cure_turnstile/` for an FSM with a GenServer wrapper. Those packages
build through Mix (`mix cure.compile`), which is the supported path for
`app`-bearing projects today. Read
[`docs/SUPERVISION.md`](SUPERVISION.md), [`docs/APP.md`](APP.md), and
[`docs/FSM_GUIDE.md`](FSM_GUIDE.md) before reaching for them.

## 13. Troubleshooting

**`no edition declared in Cure.toml`**
Add `edition = "2026"` under `[project]`. It is a warning, not an error, but it
means your project has no pinned language surface.

**`UNKNOWN CONSTRUCTOR [E091]` / `UNKNOWN VALUE [E091]`**
A missing `use`. `Ok`/`Error` need `Std.Result`, `Some`/`None` need
`Std.Option`, `<>` needs `Std.Semigroup`, and a project module needs
`use ThatModule`. If the name looks right, check that the module is under a
declared `source_paths` root.

**`REPEATED BINDING NEEDS A TYPE [E093]`**
An untyped `let _ = <effectful call>`. Annotate it: `let _: Unit = ...`.

**`EXPRESSION CANNOT BE LOWERED AS A DEPENDENT INDEX [E093]`**
Usually a function type written in a parameter position as
`f: fn(A, B) -> C`. Cure's arrow types are curried: write `f: a -> b -> c`.

**`function :"Cure.X".f/1 is undefined`**
The module compiled but was not loaded. Inside a project this should not happen
-- `cure run` and `cure test` load `lib/` first. Outside a project, either move
the file into a project or merge the modules.

**`DUPLICATE MODULE IDENTITY`**
Two files declare the same `mod` name. Module identity comes from the
declaration, not the filename, so split them into distinct modules.

**`could not read file: module_identity_missing` on a file holding only
`app`/`actor`/`sup`**
`cure compile` cannot yet drive those macro containers on its own; build such
projects through `mix cure.compile` as `examples/cure_forge/` does.

**Anything else**
`cure explain <code>` for the long form, `cure doctor` for project health, and
`cure john` for a full panoramic report (VM, tooling, project, logs) that is the
right thing to paste into a bug report.

## 14. Where to go next

- [`docs/TUTORIAL.md`](TUTORIAL.md) -- fourteen short chapters across the whole
  language
- [`docs/LANGUAGE_SPEC.md`](LANGUAGE_SPEC.md) -- syntax, keywords, operators,
  every construct
- [`docs/TYPE_SYSTEM.md`](TYPE_SYSTEM.md) and
  [`docs/DEPENDENT_TYPES.md`](DEPENDENT_TYPES.md) -- dependent checking,
  indexed families, quantitative binders, erasure
- [`docs/PATTERNS.md`](PATTERNS.md) and [`docs/MATCH.md`](MATCH.md) --
  destructuring, guards, pins, exhaustiveness
- [`docs/STDLIB.md`](STDLIB.md) -- the standard-library API reference
- [`docs/FFI.md`](FFI.md) -- `@extern` in depth
- The `examples/` directory -- from one-file demos to full projects
