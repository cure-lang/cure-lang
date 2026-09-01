# Cure Language — Formal Description

This document is a formal, comprehensive description of the Cure language at
version 0.34.1. It is written in the style of a language specification:
precise, structural, and machine-checkable in intent. Where a behaviour is
normatively pinned down in another document (pattern matching, `pickup`, the
kernel, macros, protocol session types), this document states the rule and
cross-references the authority rather than duplicating it.

**Scope.** Cure is a *dependently-typed programming language for the BEAM
virtual machine* with a single kernel-checked compiler pipeline and first-class
OTP concurrency. `LANGUAGE_SPEC.md` is the syntax reference; `TECHNICAL_OVERVIEW.md`
is the implementation tour; `KERNEL.md` / `TYPE_SYSTEM.md` are the type-theory
guides. This document is the *formal* companion: it gives the grammar, the
typing system, the semantics, the concurrency model, and the guarantees as
rules.

**Conventions.** `Type 0` is written `Type`; universes are cumulative
(`Type i <: Type i+1`). Binder grades are written `erased` (0), `linear` (1),
`affine` (≤1), and `unrestricted` (ω). A judgement `Γ ⊢ e : A` reads “under
context `Γ`, expression `e` has type `A`.” A `⊳` suffix on a computation
judgement records a postcondition (see §5, Effects).

---

## 1. Overview

Cure is a dependently-typed, indentation-structured, expression-oriented
language that compiles to BEAM bytecode and runs natively on the Erlang VM
alongside Erlang and Elixir. Its defining properties:

1. **One trusted pipeline.** Every source file passes through the dependent
   elaborator, the trusted Core validator, erasure, and the BEAM emitter.
   There is no unchecked “classic” path.
2. **Dependent types.** Types may mention values. `Vector(Nat, plus(2,3))` is
   the same type as `Vector(Nat, 5)` because type equality is computation.
3. **First-class OTP concurrency.** FSMs, actors, supervisors, and applications
   are *not* compiler object classes; they are transparent standard-library
   macros over the checked BEAM algebra.
4. **A small trusted computing base.** The kernel re-checks everything the
   elaborator produces and trusts nothing it says. The SMT solver (Z3) is never
   trusted; holes typecheck but block code generation.

## 2. Lexical Structure

### 2.1 Character set and layout

Source is UTF-8. Layout is indentation-structured: blocks are delimited by
indentation level (`:indent` / `:dedent` tokens), not by `do`/`end` or braces.
The last expression in a block is its value.

### 2.2 Comments and docstrings

- `# ...` — line comment.
- `## text` — single-line doc comment attached to the following definition.
  Consecutive blocks separated by blank lines merge into one docstring.
- `### ... ###` — fenced multi-line doc comment; common leading indentation is
  stripped.

Docstring bodies are Markdown, with `{{cure_version}}` / `{{cure_vversion}}`
substituted before rendering.

### 2.3 Keywords and soft keywords

The active keyword set is edition-aware. Reserved words include: `fn`, `mod`,
`rec`, `fsm`, `actor`, `interface`, `implementation`, `type`, `typealias`,
`primitive`, `let`, `pickup`, `else`, `match`, `with`, `when`, `local`, `use`,
`return`, `throw`, `try`, `catch`, `finally`, `for`, `in`, `true`, `false`,
`nil`, `and`, `or`, `not`, `spawn`, `send`, `receive`, `after`, `unsafe`,
`quote`, `syntax`, `becomes`, `computed`, `by`, `end`, `do`.

Contextual / soft keywords are dispatched only at statement-prefix position and
remain ordinary identifiers elsewhere:

- `requires` — interface obligations in function/implementation signatures.
- `where` — declaration-local definition blocks (former constraint spelling).
- `sup` — supervisor container (v0.25.0).
- `app` — application container (v0.26.0).

### 2.4 Identifiers

- A trailing `?` marks a predicate (Elixir convention): `even?`.
- `!` is reserved for effect annotations and FSM hard events.
- PascalCase names are constructors/types; lowercase names are variables and
  functions; `_` is the wildcard; a leading `_` signals an intentionally
  unused binding.

### 2.5 Literals

| Literal | Examples |
|---|---|
| Integer | `42`, `0xFF`, `0b1010` |
| Float | `3.14` |
| String (interpolated) | `"hello"`, `"hi #{name}"` |
| Boolean | `true`, `false` |
| Atom | `:ok`, `:error` |
| Nil | `nil` |
| Char | `'a'` |
| List | `[1,2,3]`, `[h \| t]` |
| Tuple | `%[a, b]` |
| Map | `%{key: value}` |
| Binary | `<<42, 1, 2, 3>>` |

A numeral infers as `Int` without an expected type; in a checking position it
may resolve via `ExpressibleByNaturalLiteral(t)` / `ExpressibleByIntegerLiteral(t)`
(total conversions that can reject out-of-range literals).

### 2.6 Operators (by precedence, low → high)

```
|>                       pipe (left)
<-|  ✉                   Melquiades send (non-assoc; one notch below |>)
or                       boolean or (left)
and                      boolean and (left)
== != < > <= >=          comparison (non-assoc)
.. ..=                   range (non-assoc)
<>                       string concat (right)
+ -                      additive (left)
* / %                    multiplicative (left)
- not                    unary prefix
.                        field access (left)
```

---

## 3. Grammar (abstract syntax)

The parser is a Pratt (precedence-climbing) parser producing MetaAST 3-tuples
`{tag, meta, children}`. The grammar below is the abstract syntax the parser
accepts; indentation is represented by `:indent`/`:dedent` tokens. The full
concrete grammar, keyword list, and every construct are in `LANGUAGE_SPEC.md`;
this section is the formal skeleton.

### 3.1 Modules and declarations

```
Program      := (Module)*
Module       := 'mod' QualName (Decl)*
Decl         := Function | TypeDecl | Record | Interface | Implementation
              | Macro | Fsm | Actor | Supervisor | App | Use | Attribute
Function     := ('local')? 'fn' Head '=' Body
              | ('local')? 'fn' Head (Clause)*        -- multi-clause
Head         := Name '(' Param (',' Param)* ')' ('->' Type)? ('requires' Constraint)*
              | Name '(' Param (',' Param)* ')' 'when' Guard '=' Body
Param        := '{' Name ':' Type '}'                  -- implicit
              | '@grade'? Name ':' Type                -- typed, graded
              | '@linear' Name ':' Type
Clause       := '|' Pattern ('when' Guard)? '->' Body
TypeDecl     := 'type' Name ('(' TypeParam ')')? '=' SumType
              | 'type' Name ('(' TypeParam ')')? 'indices' '(' Index ')'  -- indexed family
Record       := 'rec' Name ('(' TypeParam ')')? (Field)*
Interface    := 'interface' Name ('(' TypeParam ')')? (Method)*
Implementation := 'implementation' Name 'for' Type (Method)*
Use          := 'use' QualName
Attribute    := '@' Name '(' (Expr)* ')'
```

### 3.2 Expressions

```
Body         := Expr | Block
Block        := (Expr (NEWLINE Expr)*)                  -- last is the value
Expr         := Literal | Variable | Call | Match | Pickup | Let
              | Lambda | Tuple | List | Map | RecordBuild | RecordAccess
              | RecordUpdate | Binary | Pipe | Unary | BinaryOp | Hole
              | Quote | Splice | Have | ProofChain
Call         := Expr '(' (Expr (',' Expr)*)? ')'
Match        := 'match' Expr (NEWLINE MatchArm)*
MatchArm     := Pattern ('when' Guard)? '->' Body
Pickup       := 'pickup' (NEWLINE Guard '->' Body)* NEWLINE 'else' '->' Body
Let          := 'let' Pattern '=' Expr
Lambda       := 'fn' '(' Params ')' '->' Body        -- + brace / end forms
Hole         := '?' Name | '?' '_'
```

### 3.3 Patterns

Patterns are specified normatively in `docs/MATCH.md` (v1.0.0). The supported
shapes are: literals, variables, `_` wildcard, tuples `%[a, b]`, lists and cons
`[h | t]` / multi-head `[a, b | rest]`, maps `%{k: v}` (open matching), records
with field punning `Person{name, age}`, ADT constructors `Ok(v)`, the pin
operator `^x`, repeated variables (compiled to equality guards), and arbitrary
nesting. Exhaustiveness is checked (Maranget-style) under `E118`.

### 3.4 Conditional dispatch

Cure has **no** `if`/`elif`/`else`. Predicate dispatch is the `pickup`
construct, specified normatively in `docs/PICKUP.md`. `pickup` evaluates the
boolean guards in source order and selects the first whose guard is `true`; a
mandatory `else -> e` makes it total by construction. Guards must type to
`Bool` (no truthy/falsy coercion).

---

## 4. The Type System

Cure uses one bidirectional dependent type checker. The pre-0.34 classic
checker is deleted; all programs elaborate to dependent Core, which the kernel
validates. This section states the formal rules; `TYPE_SYSTEM.md` and
`KERNEL.md` give the expository treatment.

### 4.1 Core terms

Core terms use **de Bruijn indices** for variables (`{:var, 0}` = nearest
enclosing binder). The grammar is textbook dependent type theory:

| Core node | Meaning |
|---|---|
| `{:type, l}` | universe; fixed hierarchy `Type 0 : Type 1 : Type 2` |
| `{:pi, grade, dom, cod}` | graded dependent function |
| `{:lam, grade, dom, body}` | graded lambda |
| `{:app, f, a}` | application |
| `{:let, grade, type, value, body}` | graded, definitionally transparent let |
| `{:data, name, params, indices}` | inductive family |
| `{:ctor, name, args}` | constructor application |
| `{:case, scrut, motive, branches}` | dependent eliminator |
| `{:global, name}` | global definition reference |
| `{:int_type}` / `{:int_lit, n}` | integer facade/literal |
| `{:float_type}` / `{:float_lit, f}` | float facade/literal |
| `{:binary_type}`, `{:atom_type}` / `{:atom_lit, a}` | BEAM primitive homes |
| `{:effect_type, t}` / `{:effect_pure, a}` / `{:effect_bind, e, k}` | inert effect terms |
| `{:hole, name}` | typed gap; checks against anything, blocks codegen |

### 4.2 Universes

Universes are predicative and cumulative: `Type i : Type i+1` and
`Type i <: Type j` for `i ≤ j`. The ceiling is hard at `Type 2`
(`Cure.Core.Universe`, `@ceiling 2`); `Type 3` is not a well-formed term.
`Bool` and `Nat` are **not** primitives — they are genuine inductive families
seeded through the builtin-inductive registry and eliminated by the same
`{:case, ...}` machinery as user datatypes.

### 4.3 Bidirectional typing

Elaboration alternates between **infer** (synthesize a term and its type) and
**check** (elaborate against an expected type). Expected types flow into
lambdas, constructors, holes, blocks, and local bindings; implicit constraints
may be postponed until later explicit arguments reveal enough information.

### 4.4 Definitional equality is computation

The kernel decides definitional equality by **normalization by evaluation**
(NbE): terms evaluate into a semantic value domain (closures for functions,
neutral values for stuck terms), and conversion compares values structurally.
Thus `Vector(Nat, plus(2,3)) ≡ Vector(Nat, 5)`. A crucial gate: evaluation may
only unfold a global function (δ-reduction) if that function has a **totality
certificate**; otherwise a looping definition would make the checker loop.

### 4.5 Inductive families and dependent case

`indices` separates uniform parameters from constructor-varying indices:

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

Matching on an indexed family checks a `{:case, scrut, motive, branches}` node;
the motive states the branch result type as a function of the scrutinee. The
branch unifier compares scrutinee indices with constructor result indices via:
**Solution** (`?x ~ t`), **Injectivity** (`S(t) ~ S(u) ⇒ t ~ u`), **Deletion**
(identical sides), **Clash** (`S(...) ~ Z` ⇒ impossible), **Cycle**
(`x ~ S(x)` strongly rigid ⇒ impossible), and **undecided** (e.g. `plus(n,m) ~ Z`
⇒ branch required). This drives coverage, impossible-branch discharge, and
in-branch refinement in one mechanism.

### 4.6 Quantitative types (QTT)

Every binder carries a grade in `{erased, linear, affine, unrestricted}`
(`{0, 1, ≤1, ω}`). The usage rule:

- `erased` (0) — used zero times at runtime; erased.
- `linear` (1) — used exactly once.
- `affine` (≤1) — used at most once; may be dropped.
- `unrestricted` (ω) — the default.

The kernel rejects using erased data in runtime computation and rejects
duplicating or dropping a linear value. `add`/`mul` form a semiring over grades
(`Cure.Core.Grade`).

### 4.7 Equality

- **Definitional equality** — settled silently by NbE; produces no proof object.
- **Propositional equality** — `Equivalent(a, x, y)`, the kernel-recognised
  inductive identity family with its sole constructor `reflexive`. `sym`,
  `trans`, `cong` are checked Cure functions. `Equivalent` is distinct from the
  `Equatable(t)` interface (which computes a runtime `Bool`).

### 4.8 Implicit arguments and holes

- Implicit parameters `{t: Type}` are solved by dependent elaboration from
  explicit-argument types; they cost nothing at runtime.
- `?name` / `?_` are typed holes that report the goal type and local context;
  they block code generation (firewalled, not trusted).

### 4.9 Subtyping, union, top and bottom

- `Never` is bottom; `Any` is top.
- Widening propagates only through safe covariant positions: `List(Int)`
  satisfies `List(Any)`; function inputs stay contravariant; invariant or
  dependent positions reject widening that would lose an index or permit an
  unsafe write; `Pid(inbox)` is covariant in its accepted-message type.
- `A | B` is permitted in any type position; discrimination is ordered.

### 4.10 Interfaces and implementations

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: t) -> String = Std.String.from_int(x)

fn display(x: t) -> String requires Show(t) = show(x)
```

The compiler checks implementation signatures, required superinterfaces,
coherence, and method bodies. Resolution is compile-time and canonical; a
missing dictionary is a structured diagnostic. A constraint head may occur only
in a result type (e.g. `Std.Json.decode_as`), with the head obtained from the
expected result type.

### 4.11 Totality

Type checking may unfold only definitions backed by a validated **size-change
termination** certificate (Lee–Jones–Ben-Amram, ported from Idris), covering
structural recursion and mutual recursion. `@total true` requires certification
at the declaration. An uncertified definition may exist but stays opaque during
conversion.

---

## 5. Effects

Cure has a first-class effect former `Effect(T)`. Effect terms are **inert** in
Core (`{:effect_type, t}`, `{:effect_pure, a}`, `{:effect_bind, e, k}`): they
mark direct-style computations while keeping the effect former visible to
dependent checking. Every BEAM side-effecting operation in `Std.Otp` returns
`Effect(T)`; an effectful `let` sequences operations.

The effect discipline forbids duplicating, dropping, or reordering an
*operation* — a statement about the program's effect sequence. `Effect(T)`
does **not** claim BEAM delivery guarantees: a `tell` to a dead process
silently succeeds, and the BEAM orders signals only pairwise between one
sender and one target.

```cure
use Std.Otp
fn ping(pid: Pid(Atom)) -> Effect(Unit) = pid <-| :coin
```

## 6. Concurrency (OTP)

Cure's concurrency model is BEAM concurrency made typed. All OTP concurrency
is implemented as transparent standard-library macros over the checked BEAM
algebra — there are no compiler-owned object classes. The typed process
algebra lives in `Std.Otp`.

### 6.1 Typed process handles

| Handle | Meaning |
|---|---|
| `Pid(m)` | a plain BEAM process accepting messages of type `m` (raw send) |
| `GenServer(q, r)` | a `gen_server` taking requests `q`, replying `r` |
| `ActorServer(m, q, r)` | actor with independent async `m` and sync `q → r` codes |
| `DepActorServer(m, q, rep)` | actor whose reply type is `rep(q) : Type` per request |
| `FsmPid(event, state, data)` | a generated `gen_statem`; `event` is the accepted code |
| `SupervisorHandle` | an OTP supervisor pid |
| `Subject(m)` | a typed message address `{owner_pid, tag}` (Gleam-style) |
| `Selector(p)` | typed selective receive over several subjects |
| `Name(m)` | a registered atom carrying a phantom message-type claim |

These are opaque phantom carriers erased to raw `erlang:pid()` at runtime; the
type indices exist purely to make using a process at the wrong message/reply
type a **compile** error.

### 6.2 The Melquiades Operator

`pid <-| message` (Unicode alias `pid ✉ message`) is library-defined sugar for
`Std.Otp.tell(pid, message)`. It checks the message against the indexed process
handle and returns `Effect(Unit)`. Binding power is one notch below `|>` and
non-associative.

### 6.3 FSMs

`fsm` is a transparent standard-library macro (`Std.Fsm`) expanding to a lifted
`gen_statem` module. Two surfaces:

- **Structured** — declares the callback state type with `state` and maps event
  constructors to `FsmAction` values under `events`.
- **Transition table** — `fsm <Name> with <Data>` catalogs rows into nominal
  `State`/`Event` types and compiles the graph to a total `decide/3`.

Reachability, deadlock freedom, terminal-state validity, duplicate rows, and
payload consistency are checked during expansion; a violation is a compile
error. `FsmAction(state, data) = Keep(data) | Next(state, data) | Stop(ExitReason, data)`
and `action_to_beam` is the single lowering point to `gen_statem`'s tuple
vocabulary. Finitomata-inspired `!`/`?` suffixes, `on_transition`, and lifecycle
callbacks (`on_enter`, `on_exit`, `on_failure`, `on_timer`) are supported. See
`docs/FSM_GUIDE.md`.

### 6.4 Actors

`actor` (`Std.Actor`) emits ordinary checked `gen_server` callbacks. `state T`
shares a module-local `State` alias; callback results use erased `Effect(...)`
types. The generated module exposes `start`, `start_link`, `send`, `request`,
and `stop`. Queries (`on_call`) derive typed call branches; cast-only actors
receive a total default `handle_call/3` floor. See `docs/SUPERVISION.md`.

### 6.5 Supervisors

`sup` (`Std.Supervisor`) builds `Supervisor` modules with compile-time checks
on strategy / intensity / period / child-id uniqueness / restart / shutdown.
Child policies use closed `Restart`, `Shutdown`, and `ChildType` values. See
`docs/SUPERVISION.md`.

### 6.6 Applications and releases

`app` (`Std.App`) declares the project's OTP `Application` callback in Cure
source; the compiler rejects projects with more than one `app` container. `cure
release` packages the output as a bootable BEAM release. See `docs/APP.md`.

### 6.7 Session-typed protocols and temporal verification

Cure ships a session-typed `protocol` container (`Cure.Protocol`, v0.27.0) and a
bounded **LTL model checker** (`Cure.Temporal`). A protocol declares a sequence
of message steps between named roles; the compiler projects it onto each role
as an FSM-style transition list and verifies role usage, role membership, and
per-role reachability (error `PROTO001`). The temporal checker consumes the
projected model to assert `always`/`eventually`/`until`/`next` properties. See
`docs/PROTOCOL.md` and `docs/TEMPORAL.md`.

## 7. Macros

`macro` is Cure's **one** frontend extension point. `fsm`, `actor`, `sup`,
`app`, unit literals, and regex literals are all ordinary macros defined in
`lib/std/*.cure`. A macro is a module member whose body is an indented block of
`syntax` rules, `literal` rules, `syntax family` declarations, `accepts`,
`expands with`, `explain`, `fail`, and `open`.

### 7.1 Rule tiers

1. **`literal`** — a numeric/literal token juxtaposed with a registered suffix
   (`5 tick`).
2. **`becomes`** — a hygienic template rule: `syntax twice <n: Code> becomes n + n`.
3. **`computed by`** — a rule expanded by a compile-time (pure) function over
   `Std.Syntax` values, returning `MacroResult = Expanded(Syntax) | Rejected(List(Diagnostic))`.

### 7.2 Holes and kinds

A hole `<name: Kind>` is both the capture in the rule and the splice in the
template. Only `Name`, `ModuleName`, `Type`, `Parameters`, `Int`, `Float`,
`Atom`, `Bool`, and `Code` change matching; any other kind parses an ordinary
expression. `...` means zero-or-more; `( … )?` is an optional group. `is
<Category>` names a rule category; `open <Category>` allows extension.
`contextual` marks a rule that only fires where its expansion makes sense.

### 7.3 Structured macros — `syntax family`

`syntax family <Name>` describes an indented body shape; `accepts <Family>`
parses the macro's body as it; `expands with <fn>` turns the parsed family into
syntax. Each family auto-derives a record (`<Name>Syntax`) whose fields are
reachable by name. Cardinalities `optional`/`repeated`/`one_or_more` wrap fields
in `Option`/`List`; `includes <Family>` splices another family. This is what
powers `fsm`, `sup`, and `app`.

### 7.4 The quoted-AST API — `Std.Syntax`

`Std.Syntax` is the compile-time surface, reflecting the parser's
`{tag, meta, third}` node as `Node(Atom, List(Attr), List(Syntax)) | Leaf(...) | Raw(...) | Quoted(...) | Failure(...)`. It offers inspection, construction,
quoting (`quote <expr>` with `$(e)` single-splice and `$(e ...)` list-flatten
splice), and module emission (`lift_module`, `lift_module_isolated`).

### 7.5 Self-proving macros

`example <use> expands <pin>` pins a worked example checked at compile time
(`E092`); `explain` gives per-failure-point messages and turns on the full
contract (every rule pinned, every failure point explained). Expansion is
fuel-bounded and pure, keeping builds deterministic. See `docs/MACROS.md`.

## 8. The Compiler Pipeline

The orchestrator (`Cure.Compiler`) runs:

```
.cure source
  → Cure.Compiler.Lexer            (tokenization, indentation)
  → token stream
  → Cure.Compiler.Parser           (Pratt → MetaAST)
  → MetaAST {type, meta, children}
  → Cure.Elab.Program              (module-level dependent elaboration)
  → checked dependent Core
  → Cure.Core.Kernel               (trusted validation boundary)
  → Cure.Elab.Erase                (proof/index erasure)
  → Cure.Elab.Emit                 (lower to Erlang abstract forms)
  → Erlang Abstract Forms
  → Cure.Compiler.BeamWriter       (:compile.forms/2 → BEAM bytecode)
  → .beam
```

Every stage emits structured events through `Cure.Pipeline.Events` (a
Registry-backed PubSub) so external tools can observe and react to compilation
in real time. `Cure.quote/1` parses a string to MetaAST; `Cure.quoted_to_string/1`
round-trips it back.

---

## 9. Guarantees and the Trusted Computing Base

### 9.1 What the language guarantees

- **Type safety.** A well-typed program cannot send or receive an unexpected
  message, use a process at the wrong message/reply type, or index a
  length-indexed structure out of bounds.
- **Termination (when certified).** `@total true` definitions provably
  terminate (size-change termination); the checker unfolds only certified
  definitions during conversion.
- **Pattern exhaustiveness.** `match` must cover every constructor
  (`E118`); binary `match` must end in a catch-all (`E119`).
- **Totality of `pickup`.** A mandatory `else` makes it total by construction.
- **Coherence.** At most one implementation exists for a given interface + type.
- **Deterministic builds.** Compile-time macro expansion is pure and
  fuel-bounded.

### 9.2 The trusted computing base

The kernel (`Cure.Core`, ~9,200 lines) is the small set of files whose
correctness everything rests on. Two deliberate exclusions keep it honest:

- **The SMT solver (Z3) is never trusted.** It runs only as an untrusted lint
  over refinement obligations; its verdicts can surface warnings but can never
  certify a kernel judgement.
- **Holes are firewalled, not trusted.** A `{:hole, name}` term typechecks
  against any expected type but blocks code generation.

`@extern` FFI declarations are **axioms** — their signatures are believed, not
verified — and `believe_me` is an unchecked coercion. `cure audit trust` lists
every such escape hatch.

### 9.3 Proof-carrying artifacts

Core terms carry no PIDs, references, or closures, so every checked term has a
total, reversible JSON-able encoding. An independent checker can re-validate the
same Core terms — the basis of proof-carrying packages (`cure verify`). See
`docs/PROOF_CARRYING.md`.

## 10. Standard Library

The standard library is **self-hosted** — written in Cure under `lib/std/`,
compiled with `mix cure.compile_stdlib`. Notable modules: `Std.Core`
(combinators), `Std.List`, `Std.Math`, `Std.String`, `Std.Tuple`, `Std.Map`,
`Std.Set`, `Std.Optic`, `Std.Option`, `Std.Result`, `Std.Equivalent`,
`Std.Show`/`Std.Equatable`/`Std.Comparable`, `Std.Io`, `Std.System`,
`Std.Actor`, `Std.Process`, `Std.Supervisor`, `Std.App`, `Std.Otp`, `Std.Fsm`,
`Std.Json`, `Std.Http`, `Std.Time`, `Std.Regex`, `Std.CRDT`, `Std.Vector`, and
`Std.Syntax` (macro reflection). Numerous `proof_*.cure` modules (arithmetic,
integer order, boolean reflection, linear arithmetic) provide kernel-checked
lemmas. See `docs/STDLIB.md`.

## 11. Tooling

The escript entry point is `Cure.CLI`. Subcommands include `compile`, `run`,
`check`, `repl`, `lsp`, `test`, `fmt`, `doc`, `john`, `bless`, `story`,
`snap`, `verify`, `export_types`, `trace`, `top`, `release`, `watch`,
`migrate`, `audit`, `bench`, and `doctor`. The REPL is a readline-grade loop
with live syntax highlighting, history, Tab completion, and meta-commands
(`:t`, `:effects`, `:load`, `:fmt`, `:holes`, `:bench`, `:ast`, `:theme`,
...). The LSP server provides inlay hints, rename, semantic tokens, code
actions, and definitions. See `docs/REPL.md`.

## 12. Normative Cross-Reference

| Topic | Authority |
|---|---|
| Concrete syntax, keywords, operators | `docs/LANGUAGE_SPEC.md` |
| Pattern matching (v1.0.0) | `docs/MATCH.md` |
| `pickup` conditional dispatch (v1.0.0) | `docs/PICKUP.md` |
| Dependent type theory | `docs/DEPENDENT_TYPES.md`, `docs/TYPE_SYSTEM.md` |
| The dependent kernel (TCB) | `docs/KERNEL.md` |
| Proof authoring | `docs/PROOFS.md` |
| Pattern grammar | `docs/PATTERNS.md` |
| Binaries | `docs/BINARIES.md` |
| FFI (`@extern`) | `docs/FFI.md` |
| Macros | `docs/MACROS.md` |
| FSMs | `docs/FSM_GUIDE.md` |
| Actors & supervision | `docs/SUPERVISION.md` |
| Applications & releases | `docs/APP.md` |
| Session-typed protocols | `docs/PROTOCOL.md` |
| Temporal (LTL) verification | `docs/TEMPORAL.md` |
| Observability | `docs/OBSERVABILITY.md` |
| Implementation tour | `docs/TECHNICAL_OVERVIEW.md` |

---

*Cure — dependently-typed programming for the BEAM. One kernel-checked
pipeline. First-class OTP concurrency.*
