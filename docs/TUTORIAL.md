# Cure Tutorial
A guided tour of Cure for newcomers. Fourteen short chapters take
you from an empty directory to a working project that uses
dependent types, deep destructuring, binary parsing, FSMs, a typed
supervision tree, a full OTP application, the REPL, the type
checker as a writing tool, and finally a browsable documentation
site produced from your own `.cure` sources.
## 1. Hello, Cure
Install Cure (from the repo root):
```bash
mix deps.get
mix compile
mix escript.build
```
Now you have a `cure` binary in the project root. Add it to your PATH
and run:
```bash
cure version
```
Create a project:
```bash
cure new hello
cd hello
cure run lib/main.cure
```
You should see the project's hello message.
## 2. The compilation pipeline
Cure compiles `.cure` source through five stages: lex, parse, type
check, optimise, codegen. Every stage emits structured events you
can subscribe to from Elixir for tooling work.
Run `cure check lib/main.cure` to type-check without producing BEAM
output. Use it in your editor; you will see this command run on every
save once you turn on `cure watch lib/ --action check`.
## 3. Functions, records, ADTs
```cure
mod MyApp.Math
  type Sign = Positive | Negative | Zero

  fn classify(x: Int) -> Sign
    | x when x > 0 -> Positive
    | x when x < 0 -> Negative
    | _             -> Zero

  rec Point
    x: Int
    y: Int
```
- `fn` defines a function. Multiple clauses use `|`.
- `type` defines an ADT (sum type).
- `rec` defines a record (named product type).
## 4. Destructuring in `match`
Cure matches on structure, not just tags. Any combination of tuples,
lists, maps, records, and constructors can appear in a pattern and is
decomposed on the way in:
```cure
mod MatchExamples
  type Value = Number(Int) | Person(String)

  fn example(value: Value) -> Int =
    match value
      Number(value) -> value
      Person(_name) -> 0
```
Key shortcuts:
- `Point{x, y}` field punning -- equivalent to `Point{x: x, y: y}`.
- `^target` pin operator -- compare against a previously-bound value
  instead of binding fresh.
- Repeated variable names on the same pattern imply equality:
  `%[x, x]` matches only when both slots are equal.
Cons is single-head, so `[a, b | rest]` is not supported directly.
Use nested matches or `Std.Match.first_two/2`. See
`docs/PATTERNS.md` for the complete reference and
`examples/destructuring.cure` for a tour.
## 5. The REPL
```bash
cure repl
```
Try:
```
cure(1)> 1 + 1
=> 2
cure(2)> :t 42
42 : Int
cure(3)> :effects println("hi")
println("hi") :: ! Io
cure(4)> :load examples/recursion.cure
loaded examples/recursion.cure -> Cure.Recursion
```
Type `:help` for the full meta-command list. History is persisted to
`~/.cure_history`.
## 6. Refinement types (removed)
Refinement types (predicate-constrained base types such as
`{x: Int | x != 0}`) and their stdlib aliases have been removed for now,
pending SMTCoq-style proof reconstruction. Until they return, use a plain
base type and enforce the invariant with a guard or a runtime check.
## 7. Path-sensitive refinement (removed)
Path-sensitive refinement (narrowing a variable's type along an `if`/`match`
branch) was part of the same removed feature; see section 6.
## 8. Sigma types
A Sigma type pairs a value with a type that may depend on it:
```cure
rec Sized
  length: Nat
  values: List(Int)
```
Use Sigma when a piece of data must carry the index it parametrises.
The type checker keeps `n` connected to the vector length through
the rest of the program.
## 9. Pi types and dependent return
```text
use Std.List

fn append(xs: List(Int), ys: List(Int)) -> List(Int) =
  xs <> ys
```
The return type references the parameter names. At the call site, Cure
substitutes the actual values, normalises the resulting Core term, and compares
it by definitional equality. This means
`append(threeVec, threeVec)` is checked against `Vector(T, 6)`.
## 10. Holes and totality
While writing a function you don't yet know how to finish, leave a
hole:
```cure E014
fn safe_head({t: Type}, xs: List(t)) -> t = ?body
```
Compile, and Cure tells you the goal type and the local context.
Add `@total true` above a function to require totality:
```cure
@total true
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```
The totality checker classifies functions by coverage and structural
recursion. `factorial` is total because every recursive call shrinks
its structural argument (`n` -> `n - 1`).
## 11. Binary parsing
Cure supports full Erlang-style binary pattern matching in
`match` arms, multi-clause function heads, and `let` bindings.
Every segment is `value [:: specifier_chain]`; the specifier chain
is hyphen-joined and covers `integer`, `float`, `utf8`/`utf16`/`utf32`,
`binary`/`bytes`/`bitstring`/`bits`, signedness, endianness,
`size(expr)`, and `unit(n)`.
```text
fn first_byte(buf: Bitstring) -> Int =
  match buf
    <<b, _rest::binary>> -> b
    <<>>                 -> 0
```
The dependent coverage checker reports `E031` when a set of arms does not cover every inhabitant
of the scrutinee. A match with at least one wildcard, or with both
an empty-binary arm (`<<>>`) and an open-ended tail arm
(`<<_, _rest::binary>>`), is exhaustive.
`let` bindings accept the same binary patterns:
```text
fn parse_header(buf: Bitstring) -> Int =
  let <<tag, _rest::binary>> = buf
  tag
```
A non-exhaustive `let` emits `E034` as a warning; the binding still
compiles and Erlang's `=` raises at runtime on a failed match.
See `docs/BINARIES.md` for the authoritative reference and
`examples/binary_destructuring.cure` for an end-to-end walk-through.
## 12. FSMs
`fsm` is an auto-preluded macro that creates a transparent lifted
`gen_statem` module:
```text
fsm Turnstile
  state Int
  events
    Coin -> :keep_state_and_data
```
Each event branch is checked as an `FsmAction` (`Keep`, `Next`, or `Stop`).
Transition tables are a library-level macro over the same generated
`gen_statem` substrate rather than compiler syntax.
## 13. Documenting your modules
`cure doc` produces a browsable, ExDoc-like documentation site from
your `.cure` sources. The layout has a persistent left sidebar with
every module (optionally grouped) and any orphan pages you want to
ship, and a right pane that renders the selected page with a local
table of contents plus anchored entries for every public function,
type, and protocol.

### `##` doc comments
`##` comments on the line above a `mod`, `fn`, `type`, `rec`, or
`interface` definition attach as its docstring. Consecutive `##` blocks
separated by blank lines are merged into a single paragraph-separated
body, so you can write a docstring the way you would write regular
prose:
```cure
mod Std.List
  ## Eager, persistent, singly-linked lists.
  ##
  ## Every operation recurses over cons cells; there are no runtime
  ## arrays underneath.
```

### `## Examples` blocks
Convention: end a module-level (or important function-level) docstring
with an `## Examples` section containing fenced `cure` code. The
Markdown renderer syntax-highlights the block via Makeup, and the
examples themselves round-trip through `mix cure.compile_stdlib` --
something the Cure stdlib under `lib/std/` now enforces across every
shipped module.
```cure
mod MyApp.Math
  ## Right-to-left function composition.
  ## `compose(f, g)(x)` is `f(g(x))`.
  ##
  ## ## Examples
  ##
  ## ```cure
  ## let add1 = fn(x: Int) -> Int = x + 1
  ## let neg  = fn(x: Int) -> Int = 0 - x
  ## compose(neg, add1)(3)             # => -4
  ## ```
  fn compose({a: Type}, {b: Type}, {c: Type}, f: b -> c, g: a -> b) -> (a -> c) =
    fn(x) -> f(g(x))
```

### `Cure.toml [doc]` configuration
The `[doc]` table drives the generated layout. None of its keys are
required; adding them progressively enhances the output.
```toml
[project]
name    = "my_lib"
version = "0.1.0"

[doc]
main       = "README"
title      = "My Library"
extras     = ["README.md", "CHANGELOG.md"]
source_url = "https://github.com/you/my_lib"
source_ref = "main"

[doc.groups_for_modules]
"Core"        = ["MyLib.Core"]
"Accessories" = ["MyLib.Json", "MyLib.Http"]
```
- `main` picks the landing page. It can be either a module name
  (`MyLib.Core`) or an extra slug (`README` matches `README.md`).
- `extras` paths resolve relative to the directory that contains
  `Cure.toml`, so the same configuration keeps working from any
  sub-directory.
- `source_url` / `source_ref` attach GitHub "View source" links to
  every module page.
- `[doc.groups_for_modules]` groups the sidebar. Modules not listed
  in any group fall into a trailing `"Other"` bucket so nothing is
  silently dropped.

Every CLI flag overrides the corresponding key per invocation:
```bash
cure doc --title "Release Preview" \
         --main MyLib.Core \
         --extras CHANGELOG.md
```
`--extras` is repeatable.

### Placeholder interpolation
Inside `##` blocks and extras, the strings `{{cure_version}}` and
`{{cure_vversion}}` are substituted for the current Cure version and
its `v`-prefixed form. Useful when a docstring wants to pin itself to
the compiler that produced it.

### Running it
```bash
cure doc                         # document everything under lib/
cure doc lib/my_lib/ -o docs/    # document a sub-tree to a custom path
cure doc --main MyLib.Core       # pick a landing module
```
The output is a self-contained HTML tree (HTML + one CSS + one JS
file), so you can zip it up or host it from any static server. The
REPL's `:doc` command pulls the same sources through
`Cure.REPL.Markdown` for ANSI output.

See `docs/DOC.md` for the authoritative reference.

## Where to next
- `docs/LANGUAGE_SPEC.md` -- syntax reference.
- `docs/TYPE_SYSTEM.md` -- type checker details.
- `docs/DEPENDENT_TYPES.md` -- the v0.17.0 dependent-typing layer.
- `docs/FSM_GUIDE.md` -- FSM mechanics in depth.
- `docs/SUPERVISION.md` -- typed actors, transparent `sup` modules, the
  Melquiades Operator `<-|` (v0.25.0).
- `docs/APP.md` -- transparent `app` modules, `Cure.toml` `[application]` /
  `[release]` sections, and the `cure release` subcommand (v0.26.0).
- `docs/DOC.md` -- `cure doc` pipeline, `[doc]` config, placeholder
  interpolation, Makeup highlighting, REPL Markdown renderer (v0.29.0).
- `docs/STDLIB.md` -- standard library API.
- `docs/PACKAGE_REGISTRY.md` -- design notes for the eventual Cure registry.
