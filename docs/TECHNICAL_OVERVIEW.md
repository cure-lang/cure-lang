# Cure Language — Technical Overview

Cure is a **dependently-typed programming language for the BEAM virtual
machine** with a single kernel-checked compiler pipeline and first-class OTP
concurrency. It compiles `.cure` source files to standard BEAM bytecode, so
Cure programs run natively on the Erlang VM alongside Erlang and Elixir code.

This document is a technical deep-dive into the language, its type system, its
compiler architecture, and its tooling, grounded in the actual source tree.

---

## 1. Design Philosophy

Cure occupies a deliberately unusual niche: it marries the *verification
power* of a proof assistant (Agda / Idris / Lean lineage) with the *runtime
pragmatism* of the BEAM and OTP. The design is driven by a few principles:

1. **One trusted pipeline.** There is no "classic" unchecked code path. Every
   source file passes through the dependent elaborator, the trusted Core
   validator, erasure, and the BEAM emitter. The pre-0.34 classic
   checker/code-generator has been deleted.
2. **Everything is a first-class OTP citizen.** FSMs, actors, supervisors, and
   applications are *not* special compiler object classes — they are
   transparent standard-library macros that expand into ordinary checked Cure
   code over the BEAM algebra (`gen_statem`, `gen_server`, `Supervisor`,
   `:application`).
3. **Soundness by construction.** The kernel (the trusted computing base) is
   kept deliberately small so it can be audited. The SMT solver (Z3) is *never*
   trusted — it only produces untrusted lint warnings. Holes typecheck but
   block codegen.
4. **Indentation-structured, expression-oriented.** Blocks are delimited by
   indentation level, not `do`/`end` or braces. Every construct is an
   expression; the last expression in a block is its value.

---

## 2. The Compiler Pipeline

The compiler orchestrator lives in `lib/cure/compiler.ex`. The full pipeline
is:

```
.cure source
   │  Cure.Compiler.Lexer          (tokenization, indentation tracking)
   ▼
Token stream
   │  Cure.Compiler.Parser         (Pratt / precedence-climbing → MetaAST)
   ▼
MetaAST  {type, meta, children}    (Metastatic 3-tuples)
   │  Cure.Elab.Program            (module-level dependent elaboration)
   ▼
Checked dependent Core
   │  Cure.Core.Kernel             (trusted validation boundary)
   │  Cure.Elab.Erase              (proof/index argument erasure)
   │  Cure.Elab.Emit               (lower to Erlang abstract forms)
   ▼
Erlang Abstract Forms
   │  Cure.Compiler.BeamWriter     (:compile.forms/2 → .beam)
   ▼
BEAM bytecode
```

Every stage emits structured events through `Cure.Pipeline.Events`, a
PubSub-style system backed by an Elixir `Registry`. External tools (LSP,
profilers, IDE plugins) can subscribe to observe compilation in real time.

### 2.1 Internal AST — MetaAST

Cure uses Metastatic's **MetaAST 3-tuple** format as its internal AST:

```elixir
{type_atom, keyword_meta, children_or_value}
```

For example `{:literal, [subtype: :integer], 42}`. This provides a
well-defined, layered AST and interoperability with Metastatic's cross-language
analysis tooling. `Cure.quote/1` parses a string into MetaAST and
`Cure.quoted_to_string/1` (via `Cure.Compiler.Printer`) round-trips it back.

### 2.2 Front end

- **Lexer** (`lib/cure/compiler/lexer.ex`, ~73 KB) — tokenizes the full Cure
  syntax: keywords, operators, literals, indentation (`:indent`/`:dedent`),
  string interpolation, FSM transitions, and both single-line (`##`) and
  fenced (`###...###`) doc comments. The active keyword set is edition-aware.
- **Parser** (`lib/cure/compiler/parser.ex`, ~550 KB) — a Pratt
  (precedence-climbing) parser, indentation-aware, producing MetaAST. Handles
  functions, modules, records, types, protocols/interfaces, implementations,
  imports, and FSMs. Operator binding powers live in
  `Cure.Compiler.Parser.Precedence`.
- **Editions & migration** (`Cure.Edition`, `Cure.Migrate`) — `@edition` /
  `[project].edition` select a grammar/keyword edition. `cure migrate`
  rewrites deprecated syntax (`proto`/`impl` → `interface`/`implementation`,
  legacy `if` → `pickup`, uppercase type vars → lowercase).

### 2.3 Middle end — elaboration, validation, erasure

- **`Cure.Elab.Program`** — module-level dependent elaboration, declaration
  grouping, import/interface loading, totality checks, and canonical
  definition identity.
- **`Cure.Elab.Elaborator`** (~663 KB) — bidirectional elaboration from
  surface MetaAST into dependent `Cure.Core` terms.
- **`Cure.Core.Kernel`** (~110 KB) — the trusted validation boundary that
  re-checks everything the elaborator produces and trusts nothing it says.
- **`Cure.Elab.Erase` / `Cure.Elab.Emit`** — erase proof/index arguments and
  lower the remaining Core to Erlang abstract forms.

### 2.4 Back end

- **`Cure.Compiler.BeamWriter`** — compiles Erlang abstract forms to BEAM
  bytecode via `:compile.forms/2` and writes `.beam` files.
- **`Cure.App.Resource`** — emits the OTP `<name>.app` resource file.
- **`Cure.Release`** — builds a bootable BEAM release under
  `_build/cure/rel/<name>/` (`.rel`/`start.boot` assembly via `:systools`,
  `sys.config`/`vm.args`, and a POSIX `bin/<name>` runner).

---

## 3. The Dependent Type System

Cure uses **one bidirectional dependent type checker**. The classic checker was
deleted; all programs elaborate to dependent Core, which the kernel validates.

### 3.1 Core terms

Core terms (`lib/cure/core/term.ex`) are plain tagged tuples using **de Bruijn
indices** for variables (`{:var, 0}` = nearest enclosing binder), so there are
no names and no capture bugs. The grammar is textbook dependent type theory:

| Node | Meaning |
|------|---------|
| `{:type, l}` | universe; fixed hierarchy `Type 0 : Type 1 : Type 2` |
| `{:pi, grade, dom, cod}` / `{:lam, grade, dom, body}` / `{:app, f, a}` | graded dependent functions |
| `{:let, grade, type, value, body}` | graded, definitionally transparent local binding |
| `{:data, name, params, indices}` | inductive family applied to params + indices |
| `{:ctor, name, args}` | constructor application |
| `{:case, scrut, motive, branches}` | dependent eliminator |
| `{:global, name}` | reference to a global definition |
| `{:int_type}` / `{:int_lit, n}`, `{:float_type}` / `{:float_lit, f}` | numeric facade/literal nodes |
| `{:binary_type}`, `{:atom_type}` / `{:atom_lit, a}` | BEAM primitive homes |
| `{:effect_type, t}` / `{:effect_pure, a}` / `{:effect_bind, e, k}` | inert effect terms |
| `{:hole, name}` | a typed gap: checks against anything, blocks codegen |

The universe ceiling is hard (`Cure.Core.Universe`, `@ceiling 2`); `Type 3` is
not even well-formed. Note that `Bool` and `Nat` are **not** primitives — they
are genuine inductive families seeded through the builtin-inductive registry
(`Cure.Core.Builtins.seed`), eliminated by the same `{:case, ...}` machinery as
any user datatype, and erased to native BEAM booleans/ints at emit time.

### 3.2 Bidirectional elaboration

Elaboration alternates between **infer** (synthesize a Core term and its type)
and **check** (elaborate an expression against an expected type). Expected
types flow into lambdas, constructors, holes, blocks, and local bindings.
Implicit constraints may be postponed until later explicit arguments reveal
enough information, so typability does not depend on argument order.

### 3.3 Key features

- **Pi types (dependent functions).** Return types may mention parameter
  values. `fn append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a,m),
  ys: Vector(a,n)) -> Vector(a, plus(m,n))`. The checker substitutes
  call-site arguments and compares resulting Core terms by normalization and
  definitional equality.
- **Sigma types (dependent pairs).** `Sigma(name: T1, T2)` pairs a value with
  a type that may depend on it — "there exists."
- **Indexed inductive families.** `indices` separates uniform parameters from
  constructor-varying indices. Constructor-index equations refine each match
  branch; `impossible` arms and forced (`.`) patterns make proofs explicit.

  ```cure
  type Vector(a: Type) indices (n: Nat)
    empty   : Vector(a, Z)
    prepend : a -> Vector(a, n) -> Vector(a, S(n))
  ```

- **Cumulative universes.** `Type 0 : Type 1 : Type 2`, predicative and
  cumulative (small types are also big types).
- **Quantitative types.** Core binders carry a grade in `{0, 1, ω}`:
  `@erased` (0), `@linear` (1), `@affine` (≤1), and unrestricted (ω). The
  kernel rejects using erased data in runtime computation and rejects
  duplicating/dropping a linear value.
- **Definitional vs. propositional equality.** Definitional equality
  normalizes both terms and compares normal forms (automatic, no proof
  object); `Equivalent(a, x, y)` is propositional equality via the kernel-
  recognized inductive identity family, with `reflexive`, `sym`, `trans`, and
  `cong` as checked Cure functions.
- **Implicit arguments.** `fn id({t: Type}, x: t) -> t = x` — parameters in
  `{...}` are solved by dependent elaboration; they cost nothing at runtime.
- **Holes.** `?name` / `?_` trigger a `:hole_goal` event reporting the goal
  type and local context. Holes block codegen.
- **Union / top / bottom types.** `A | B` in any type position; `Never` is
  bottom, `Any` is top. Widening propagates only through safe covariant
  positions.
- **Interfaces & implementations** (ad-hoc polymorphism). `interface` /
  `implementation`, explicit `requires` constraints, canonical cross-module
  instance lookup, and structural derivation.

### 3.4 Type equality is computation

The kernel decides definitional equality by **normalization by evaluation**
(NbE): `eval.ex` evaluates terms into a semantic value domain (closures for
functions, "neutral" values for stuck terms like `plus(n, 2)` where `n` is a
variable), and `conv.ex` compares values structurally. So
`Vector(Nat, plus(2,3))` and `Vector(Nat, 5)` are the same type.

One crucial twist: **evaluation may only unfold a global function (δ-reduction)
if that function has been certified total.** Otherwise a looping definition
would make the type checker itself loop.

### 3.5 The dependent kernel

The kernel (`lib/cure/core/`, ~9,200 lines) is the trusted dependent-type
checker. Its key components:

- **`kernel.ex`** — bidirectional `infer`/`check`.
- **`inductive.ex`** — family declaration with universe checks and **strict
  positivity** (the family name may not appear to the left of an arrow in a
  field type). The positivity walk is **nested** — it descends through
  intermediate wrapper datatypes, mirroring Agda/Idris.
- **`certificate.ex`** — **size-change termination** (Lee–Jones–Ben-Amram,
  ported from Idris's `Core/Termination/SizeChange.idr`), covering structural
  recursion and mutual recursion.
- **`eval.ex` / `conv.ex` / `normalise.ex`** — NbE and conversion.
- **`serialize.ex`** — every checked term has a total, reversible JSON-able
  encoding (terms carry no PIDs/references/closures), the basis for
  proof-carrying artifacts.

### 3.6 Dependent case: index unification

When matching on an indexed family, the kernel checks a
`{:case, scrut, motive, branches}` node. The **motive** states the type of the
whole expression *as a function of the scrutinee*. For each constructor, the
branch unifier compares the scrutinee's type indices with the constructor's
result index terms:

- **Solution** — `?x ~ t` for a flexible variable → record substitution,
  refining the branch body.
- **Injectivity** — `S(t) ~ S(u)` reduces to `t ~ u`.
- **Deletion** — syntactically identical sides → discard.
- **Clash** — `S(...) ~ Z` → `:impossible` (the branch is impossible).
- **Cycle** — `x ~ S(x)` (strongly rigid occurrence) → `:impossible`.
- Anything undecidable (e.g. `plus(n,m) ~ Z`) → `:undecided`, requiring the
  branch conservatively.

This one mechanism drives coverage checking, impossible-branch discharge, and
in-branch type refinement.

### 3.7 Trusted computing base exclusions

Two deliberate exclusions keep the TCB honest:

- **The SMT solver (Z3) is never trusted.** It runs only as an untrusted lint
  over refinement obligations; its verdicts can surface warnings but can never
  certify a kernel judgement.
- **Holes are firewalled, not trusted.** A `{:hole, name}` term typechecks
  against any expected type but blocks codegen.

---

## 4. Language Surface

### 4.1 Syntax overview

Cure is **indentation-structured** (no closing delimiters). Literals include
integers (`42`, `0xFF`, `0b1010`), floats, strings with interpolation
(`"hello #{name}"`), booleans, atoms (`:ok`), chars (`'a'`), lists
(`[1,2,3]`, `[h|t]`), tuples (`%[a, b]`), and maps (`%{key: value}`).

**Operators** (by precedence, low→high):

```
|>  <-|/✉  or  and  == != < > <= >=  .. ..=  <>  + -  * / %  - not  .
```

### 4.2 Modules & functions

```cure
mod MyApp.Math
  use Std.Result
  use Std.Option

  type Sign = Positive | Negative | Zero

  fn double(n: Int) -> Int = n + n

  local fn helper() -> Int = 42          # private
```

Functions support single-expression bodies, indented multi-expression blocks,
multi-clause pattern-matching heads, guards (`when`), and `@extern` FFI
bindings. The `!` suffix is reserved for effects/FSM hard events; `?` marks a
predicate (Elixir convention).

### 4.3 Records

Records are named, typed product types that compile to BEAM maps with a
`__struct__` discriminator key (nominal identity):

```cure
rec Point
  x: Int
  y: Int

let p = Point{x: 1, y: 2}
p.x                          # field access → maps:get
Point{p | x: new_x}          # functional update → map_field_exact
```

Construction uses `map_field_assoc` (`:=>`); update uses `map_field_exact`
(`:=`), giving a `bad_key` error at runtime if the base has an incompatible
shape.

### 4.4 Pattern matching

The `match` construct is normatively specified in `docs/MATCH.md`. It supports
deep destructuring across all structural forms: literals, variables, tuples,
lists and cons cells (`[h|t]`, multi-head `[a,b|rest]`), maps (open matching),
records with field punning, ADT constructors, the pin operator `^x`, repeated
variables (turned into equality guards), and nested combinations. Exhaustiveness
is checked (Maranget-style); missing constructors are reported under `E118`
(Pattern Coverage).

### 4.5 Conditional dispatch — `pickup`

Cure has **no `if`/`elif`/`else`**. Predicate dispatch goes through `pickup`,
which walks clauses and picks the first whose guard is `true`, terminating in a
mandatory `else`:

```cure
let status = 500
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  else          -> :informational
```

Guards must type to `Bool` (no truthy/falsy coercion). Specified normatively in
`docs/PICKUP.md`.

### 4.6 ADTs & refinement types

```cure
type Option(t) = Some(t) | None
type Result(t, e) = Ok(t) | Error(e)

type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

ADTs support multi-line layout (v0.21.0) and function-type payloads. The
classic `{x: T | predicate}` refinement former has been retired from the
trusted dependent pipeline — structural invariants are expressed with indexed
families and proof arguments. (Note: `examples/dependent_types.cure` still
demonstrates an older `{x: Int | phi}` surface reflecting into `IsTrue(phi)`.)

### 4.7 Effects

`Effect(T)` marks direct-style computations while keeping the effect former
visible to dependent checking. Effect terms are **inert** in Core
(`{:effect_type, t}` / `{:effect_pure, a}` / `{:effect_bind, e, k}`).

### 4.8 Proof authoring

The proof surface is ordinary kernel-checked Cure terms (not a separate
language): `have name [: Proposition] = expression`, `proof chain` with
`because`, `rewrite [backwards] using proof [at n] [in hypothesis]`,
`simplify`, and structural `induction` with
`case Constructor(fields, induction_hypotheses) =>`. Proof commands are
elaboration-only and never appear in runtime Core or BEAM output.

---

## 5. OTP Concurrency: FSMs, Actors, Supervisors, Applications

A defining architectural decision: **all OTP concurrency is implemented as
transparent standard-library macros** over the checked BEAM algebra, not as
compiler-owned object classes. This keeps the compiler surface small while
giving every concurrency construct full dependent typing.

### 5.1 FSMs (`fsm`)

`Std.Fsm` declares `fsm` macros (both require `use Std.Fsm`). Two surfaces:

- **Structured** — declares the callback state type with `state` and maps
  event constructors to `FsmAction` values under `events`:

  ```cure
  use Std.Fsm
  fsm Ticker
    state Int
    events
      Tick -> :keep_state_and_data
  ```

- **Transition table** — `fsm <Name> with <Data>` catalogs rows into nominal
  `State`/`Event` types and compiles the graph to a total `decide/3`:

  ```cure
  use Std.Fsm
  fsm TrafficLight with Int
    Red    --Timer-->     Green
    Green  --Timer-->     Yellow
    Yellow --Timer-->     Red
    *      --Emergency--> Red
  ```

Reachability, deadlock freedom, terminal-state validity, duplicate rows, and
payload consistency are checked at expansion time. The generated module
implements the standard `gen_statem` behavior. Finitomata-inspired `!`/`?`
event suffixes, inline `on_transition` handlers, and lifecycle callbacks
(`on_enter`, `on_exit`, `on_failure`, `on_timer`) are supported.

### 5.2 Actors (`actor`) and Supervisors (`sup`)

```cure
use Std.Actor
actor Counter
  state Int
  initial 0
  on_message
    Inc -> state + 1
```

`actor` emits ordinary `gen_server` callbacks; `state T` shares a module-local
`State` alias, and callback results use erased `Effect(...)` types. `sup`
builds `Supervisor` modules with compile-time checks on strategy / intensity /
period / child-id uniqueness / restart / shutdown. The generated actor module
exposes `start`, `start_link`, `send`, `request`, and `stop`.

### 5.3 The Melquiades Operator `<-|` / `✉`

`pid <-| message` is library-defined sugar for `Std.Otp.tell(pid, message)`
(Unicode alias `pid ✉ message`). It checks the message against the indexed
process handle and returns `Effect(Unit)`. Binding power is one notch below
`|>` and non-associative.

### 5.4 Applications (`app`) and releases

```cure
use Std.App
app MyApp
  root Root
```

The `app` container declares the project's OTP `Application` callback in Cure
source with `vsn`, `description`, `root`, `applications`, `env`,
`on_start`, `on_stop`, and `on_phase :name` clauses. The compiler rejects
projects with more than one `app` container. `cure release` packages the
compiled output as a bootable BEAM release. `Std.App` exposes
`ensure_all_started`, `stop`, `env_*`, and start-phase wrappers.

---

## 6. Standard Library

The standard library is **self-hosted** — written in Cure itself under
`lib/std/` (68 `.cure` modules), compiled with `mix cure.compile_stdlib`.
Highlights:

- **`Std.Core`** — identity, composition, application, foundational combinators.
- **`Std.List`** (29 funcs), **`Std.Math`** (18), **`Std.String`** (34),
  **`Std.Tuple`**, **`Std.Map`**, **`Std.Set`**, **`Std.Optic`** (lenses).
- **`Std.Option` / `Std.Result`** — canonical inductives.
- **`Std.Equivalent`** — the inductive identity type and its kernel-checked
  `reflexive`/`sym`/`trans`/`cong` proofs.
- **`Std.Show` / `Std.Equatable` / `Std.Comparable`** — comparison interfaces.
- **`Std.Io` / `Std.System`** — I/O and system access.
- **`Std.Actor` / `Std.Process` / `Std.Supervisor` / `Std.App` / `Std.Otp`** —
  the OTP concurrency surface.
- **`Std.Fsm`** — the FSM macros.
- **`Std.Json` / `Std.Http` / `Std.Time` / `Std.Regex` / `Std.CRDT` /
  `Std.Vector`** — richer data and protocol modules.
- **`Std.Syntax`** — lossless syntax reflection for macros.
- Numerous `proof_*.cure` modules — arithmetic, integer order, boolean
  reflection, directed extraction, linear arithmetic semantics.

---

## 7. Tooling & CLI

The escript entry point is `Cure.CLI` (`lib/cure/cli.ex`). Available
subcommands:

```
compile  run  check  lsp  stdlib  version  help  audit  bench  deps  doc
doctor   draw  explain  fix  fmt  info  init  john  keys  lib  lifted
migrate  name  new  publish  release  repl  replay  run  search  snap
story  test  trace  verify  version  watch  why
```

Notable tools:

- **`cure repl`** — a readline-grade REPL with live Makeup syntax
  highlighting, persistent history, Tab completion, a vi mode, and meta-
  commands (`:t`, `:effects`, `:load`, `:fmt`, `:holes`, `:bench`, `:ast`,
  `:theme`, ...).
- **`cure doc`** — an ExDoc-like two-pane documentation site driven by
  `[doc]` in `Cure.toml`.
- **`cure john`** — a single panoramic diagnostic (Cure / BEAM / system /
  project / runtime state) rendered as Markdown-to-ANSI.
- **`cure bless`** — a Socratic type-error assistant.
- **`cure story`** — a narrative architecture generator
  (`apps -> supervisors -> actors -> FSMs -> types`) with optional Mermaid
  FSM diagrams.
- **`cure snap`** — REPL session snapshots.
- **`cure verify`** — proof-carrying package verification.
- **`cure export_types`** — cross-language ADT export to proto3.
- **`cure trace` / `cure top` / `Cure.OTel`** — observability.
- **`Cure.Temporal`** — an LTL bounded model checker over FSM graphs.
- **`Cure.Protocol`** — session-typed binary protocols.
- **`cure test`** — test runner with `Std.Test` and property-based testing.
- **`cure watch`** — incremental recompile on change.
- **LSP server** (`cure lsp`) — inlay hints, rename, semantic tokens,
  code actions, definitions.

### 7.1 Diagnostics

Diagnostics are structured and machine-readable, with authored source ranges,
canonical definition identities, error codes (e.g. `E056`, `E057`, `E086`,
`E093`, `E098`, `E100`, `E115`, `E118`, `E119`), related spans, and safe code
actions. They flow through `Cure.Diagnostic.Registry`, `Cure.Diagnostic.Adapter`,
and `Cure.Diagnostic.Sink` for terminal, JSON, and editor (LSP) consumers.

---

## 8. Project Layout

```
lib/
  cure.ex                 # root module, version, quote/1, quoted_to_string/1
  cure/
    compiler.ex           # pipeline orchestrator
    compiler/             # lexer, parser, printer, formatter, beam_writer,
                          # macro_*, module_*, artifacts, dep_graph, ...
    core/                 # THE KERNEL: kernel, inductive, conv, eval,
                          # normalise, certificate, totality_certificate, ...
    elab/                 # elaborator, program, declarations, emit, erase,
                          # unify, induction, proof_search, interface, ...
    cli.ex                # escript entry, all subcommands
    repl/                 # REPL implementation
    lsp/                  # Language Server
    smt/                  # Z3 solver process management
    otp/                  # OTP bridge (Std.Otp runtime)
    doc/                  # documentation tooling
    temporal/             # LTL bounded model checker
    protocol/             # session-typed binary protocols
    project/              # Cure.toml, package registry, proof
    export_types/         # proto3 export
    audit/                # dependency/security audit
    story/                # narrative architecture generator
    pipeline/             # events (Registry-backed PubSub)
    diagnostic/           # structured diagnostics
    antigen/              # property-based metatheory testing
  std/                    # self-hosted standard library (.cure)
  std_deps/               # stdlib dependencies
examples/                 # full example projects and standalone .cure files
docs/                     # authoritative documentation
test/                     # ExUnit test suite
```

The standard library is also bundled under `priv/std/` (sources) and
`priv/ebin/Cure.Std.*.beam` (compiled BEAMs) so the embedded REPL can call the
stdlib at runtime.

---

## 9. Quality & Verification

- **`mix test`** — ExUnit suite; warnings are treated as errors.
- **`mix check`** — compiles the stdlib and runs the example regression suites.
- **`mix format`, `mix credo --strict`, `mix dialyzer`** — code quality gates.
- **Antigen** (`lib/antigen/`) — property-based *metatheory* testing: dozens
  of assays (branch unification, conversion, erasure, indexed families, kernel
  laws, positivity, reflexivity, totality closure, universes, ...) that
  generate random Core terms / environments and check kernel invariants.
- **Proof-carrying artifacts** — checked Core terms serialize losslessly, so an
  independent checker can re-validate them (`cure verify`).

---

## 10. Release History Highlights

- **v0.34.0** — dependent macro surface (`actor`/`sup`/`app` as source macros),
  self-proving `example`/`explain`, `Std.Syntax`.
- **v0.32.0** — proof-carrying packages, proto3 ADT export, REPL snapshots,
  `cure story`.
- **v0.30.0** — `cure john` panoramic diagnostic.
- **v0.28.0** — parser error recovery, `cure bless`, `@record` + `cure replay`
  FSM time-travel.
- **v0.26.0** — `app` containers and `cure release`.
- **v0.25.0** — typed supervision trees, Melquiades Operator, `actor`/`sup`.
- **v0.24.0** — the REPL.
- **v0.17.0** — dependent pairs / Pi / propositional equality, totality
  checker, REPL, LSP.
- **v0.12.0** — complete rewrite from Erlang to Elixir.
- **v0.10.0** — project bootstrap, lexer, Pratt parser, BEAM codegen.

---

## 11. Summary

Cure is a serious dependently-typed language that targets the BEAM. Its
distinctive contribution is the fusion of a proof-assistant-grade type system
(dependent functions, indexed inductive families, quantitative types,
propositional equality, size-change-termination-gated evaluation) with
first-class, fully-typed OTP concurrency delivered through transparent macros.
The single kernel-checked pipeline, the deliberately small trusted computing
base, the untrusted SMT layer, and the self-hosted standard library make it a
coherent and auditable system for writing verified concurrent software that
runs natively on the Erlang VM.
