# Cure 0.34 — Idris Parity

0.34 replaces the simply-typed "classic" pipeline with a full dependent
type theory. The classic checker + codegen are **deleted**; every program
now flows through one dependent kernel with Idris/Lean-style metatheory
(NbE conversion, cumulative universes, indexed families, strict
positivity, quantitative grades, inductive equality, machine-checkable
totality certificates).

Value-surface Cure (strings, lists, tuples, records, lambdas, matches,
FSMs, actors) is preserved — it just runs through the dependent pathway
now. What's new below is what the surface gained.

---

## 1. Dependent types on the surface

**Indexed families (GADTs).** `indices` visually separates *parameters*
(uniform across constructors) from *indices* (vary per constructor):

```cure
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

**Dependent function types** — the codomain may mention the argument:

```cure
fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = ...
```

**Brace-implicit parameters** — inferred, not passed at the call site:

```cure
fn spawn({m: Type}, thunk: () -> Unit) -> Effect(Pid(m)) = ...
```

**Empty / single-constructor types.** `= |` declares a type with no
constructors (the canonical `Void`); a lone constructor needs no `|`:

```cure
type Empty = |
type Wrapper = Wrap(Int)
```

**Bare nullary constructors** in patterns — the empty parens are now
optional (`None` and `None()` both parse):

```cure
match opt
  None -> 0        # None() still works too
  Some(x) -> x
```

**Impossible arms + forced (`.`) patterns** for provably-unreachable
cases:

```cure
match pf
  reflexive -> ...
  _         -> impossible
```

**`with`-abstraction** (Idris-style), including multiple binders,
refines the goal on an intermediate value:

```cure
match xs with view(xs)
  ...
```

**Union types** in any type position; discrimination is *ordered*, not
class-disjoint:

```cure
fn describe(v: Int | Bool | Atom) -> Int = match v ...
```

**`typealias`** — transparent synonyms — and **`primitive`** —
kernel-backed base types:

```cure
typealias Char = Bounded(1114112)
primitive Float
```

`rewrite` is now sugar over a single-branch inductive `case`; the
primitive `Eq`/`refl`/`rewrite` triple is retired in favour of an
inductive identity type (`Equivalent` / `reflexive`).

---

## 2. Value-surface additions

Smaller surface features, all now on the dependent pipeline:

- **Multi-clause function heads** — several `fn f(pat) = …` clauses
  desugar to one `match`.
- **First-class functions** — function types, lambdas, HOFs, and
  chained application `f(x)(y)`.
- **Records** — omitted fields fill from declared defaults.
- **Char / string literals** — `'a'`, multi-byte UTF-8 (`'😀'` → 128512),
  `"…"` is `List(Char)`, and interpolation `"a#{x}b"`.
- **Comprehensions** — list comprehensions and byte/binary
  comprehensions (`for <<b <- bin>>`).
- **Map literals & patterns** — heterogeneous maps included.
- **Integer ranges** — `a..b` / `a..=b`.
- **Pin patterns** — `^x` matches against an existing binding.
- **Unary negation** `-x`, structured tail-position early `return`, and
  `assert_type e : T` ascription:

```cure
fn asserted() -> Int = assert_type 42 : Int
```

- **N-ary tuples** — flat `Tuple(T1, …, Tn)` surface with positional
  `.i` projection and `element(t, i)` (compile-time bounds-checked).
- **Contextual integer literals** — a numeral defaults to `Int`, but in a
  checking position `ExpressibleByNaturalLiteral` /
  `ExpressibleByIntegerLiteral` may construct the expected type and reject an
  invalid finite-domain value at compile time.

---

## 3. Quantitative types (QTT)

Every binder carries a usage grade from the `{0, 1, ω}` semiring (with
`affine` built in). Grades on parameters and `let`:

```cure
fn f(@linear c : Box) -> Widget = let x = c in consume(x)
```

`0` = erased (compile-time only, erased from the BEAM output),
`@linear` = used exactly once, `ω` = unrestricted. The kernel
rejects returning, scrutinising, or re-applying an erased binder.

---

## 4. Typeclasses → `interface` / `implementation`

Idris2-style surface replaces the old `proto` / `impl`. Coherence is
global, with named instances and structural `deriving`:

```cure
interface Show(t)
  fn show(x: t) -> String

implementation Semigroup for List(t)
  fn combine(x: List(t), y: List(t)) -> List(t) = ...
```

Operators are the surface: `<>` and non-numeric `+` dispatch through
`Std.Semigroup.combine`; `<`/`>`/`<=`/`>=` on non-primitives through
`Std.Comparable`. Renames: `Ord → Comparable`, `Eq → Equatable`,
identity type `→ Equivalent` / `reflexive`.

**User-defined operator fixity propagates across modules.** A module's
precedence table includes its own declarations, the transitive closure of
every module it `use`s, and user `@prelude` providers discovered by the build
driver. Conflicting operator/group declarations and precedence cycles are
rejected before authoritative parsing. An ambient user-prelude operator brings
both its syntax and its Cure definition into elaboration, so sibling modules
can compile and call it without an explicit `use`.

Fixity follows ordinary `use` edges, including transitively:

```cure
mod MathOps
  precedencegroup BetweenAddAndMul
    associativity: left
    higher_than: Additive
    lower_than: Multiplicative

  infix `<?>` : BetweenAddAndMul
  fn `<?>`(x: Int, y: Int) -> Int = x * x + y
end

mod Helpers
  use MathOps
end

mod Example
  use Helpers
  fn result() -> Int = 2 + 3 <?> 4 * 5
end
```

A project-local prelude makes an operator ambient to sibling modules; its
definition is imported along with its grammar:

```cure
@prelude
mod Project.Operators
  precedencegroup PipelineChoice
    associativity: left
    higher_than: Pipe

  infix choose : PipelineChoice
  fn choose(fallback: Int, chosen: Int) -> Int = chosen
end

mod Project.Main
  # No `use Project.Operators` is required in a multi-file project build.
  fn answer() -> Int = 0 choose 42
end
```

---

## 5. FFI & effects

**`@extern`** compiles to a direct Erlang remote call — the path to
AtomVM NIFs and OTP. A bodyless `@extern` is a typed FFI postulate
(totality-checking skips it), and it may return `Effect(<union>)`:

```cure
@extern(Elixir.Cure.Sup.Builtins, :sup_start, 1)
fn sup_start(spec: SupSpec) -> Effect(Pid(m))
```

**`@erases(<class>)`** declares an opaque carrier's runtime shape
(`:pid`, `:reference`, …) so the guard that recognises it survives
erasure.

**`Effect(T)`** is an inert type former in the kernel; effects lower
direct-style and **run end-to-end on AtomVM**. Erased `Effect`-typed
binders are rejected.

---

## 6. Proof & trust surface

- **Holes** in three positions — type, proof, and body — for
  incremental development.
- **`unsafe`** — an explicit raw namespace for escape-hatch syntax
  construction.
- **Trust ledger** — `postulate` / bodyless `@extern` / `believe_me`
  are tracked axioms. `cure audit trust <Module>` reports the axiom
  roots a module actually depends on (prelude-diff roots, own
  reachability, MFA identity).
- **`GuardLint`** — untrusted Z3 coverage/shadow queries surface
  guard-exhaustiveness and shadowing as *warnings* (Z3 is outside the
  trusted kernel).

---

## 7. User-defined syntax (macros)

A staged macro system (`SP1`–`SP5`). Declare surface grammar with
`syntax … becomes`; holes are typed (`<name: Kind>`), hygienic
(`<fresh Name>`), and repeatable:

```cure
syntax beam_ops tell <dest: Code> <message: Code>
  becomes Std.Otp.tell(dest, message)
```

**Quasiquotation** — `quote` builds AST, `$( )` splices:

```cure
let init_body = quote %[:ok, %[$(strategy), $(children)]]
```

**`computed by`** hands the matched syntax to an elaborator function for
Tier-3 expansion (`derive_actor`, `derive_fsm`, …), and
`to_syntax`/`from_syntax` give lossless reflection over `Std.Syntax`.
The entire OTP macro family (actor/fsm/supervisor/application) is now
authored this way, as is the reactive `view` / `flow` / `reducer` DSL —
whose FRP slice runs on BEAM under checked `{0, ω}` erasure.

---

## 8. Typed OTP concurrency

`Std.Otp` reframes BEAM processes as a **typed algebra** over a sealed
raw base, replacing untyped `spawn`/`receive`:

- `Pid(m)` — a process that accepts messages of type `m`.
- `GenServer(q, r)` — typed synchronous call: request `q`, reply `r`.
- **Linear reply capabilities** — `ReplyOf(req)` is consumed exactly
  once per callback (no lost/double replies, checked).
- Typed monitors (`DOWN`-as-message), links + `trap_exit`, timers
  (`send_after`/`cancel_timer`), and ordered selective receive.
- Typed supervision — restart preserves declared children; per-process
  heterogeneous routing.
- Metatheory: progress + preservation over Core Erlang reduction,
  FIFO-faithful mailbox ordering, and a decidable core of mailbox-type
  inference.

---

## 9. Standard library

Everything re-elaborates on the dependent pipeline. New / reshaped:

- **`Std.Optic`** — statically-typed lenses / affine / traversals
  (retires the `believe_me`-backed `Std.Access`).
- **`Std.Vector`** — length-indexed, Data.Vect parity (`take`/`drop`,
  full optic composition).
- **`Std.NonEmpty`**, **`Std.Decision`** (decidable props with
  evidence), **`Std.Sigma`**, **`Std.Tuple`**.
- **`Std.Equivalent` / `Std.Proof`** — genuine inductive
  `Equivalent`/`reflexive`; primitive equality tokens retired.
- `Option`/`Result` are real inductives; `Map(k, v)` is parameterised;
  `String = List(Char)`; `Char`/`Atom`/`Binary`/`Int`/`Float` get
  visible primitive homes.
- **`Std.Regex`** is now indexed by its extraction result and compiles to a
  direct pattern machine with typed evidence decoding; the old unindexed
  tree/suffix matcher and OTP-regex shim are gone.
- `@prelude` marks a stdlib item ambient without an explicit `use`.

---

## 10. Tooling

- **`cure fmt`** — the Printer is total and a byte-fixpoint over the
  whole corpus: it round-trips losslessly, preserving comments/blank
  trivia and applying a fixed blank-line policy. Unprintable nodes
  raise rather than silently mangle. `cure fmt` / `cure doc` degrade an
  unreadable file to a clean exit (and suggest `migrate`) instead of
  crashing.
- **`cure migrate`** — mechanically ports source across editions
  (check / print / strict, atomic batches). Rules: `proto`/`impl` →
  `interface`/`implementation`, `if`/`elif` → `pickup`, uppercase
  type-vars → lowercase (freshened), `@group` hoist, module
  rename/removal. Runs to a fixpoint under a reparse-equivalence guard;
  refuses a dirty git tree.
- **`cure audit trust <Module>`** — the axiom-ledger report (see §6).
- **Multi-file builds** — compiled in `DepGraph` topological order with
  new diagnostics: `W086` import cycle, `E087` duplicate module,
  `W088` unresolved import. CLI, project, and incremental `mix cure.compile`
  builds share user-`@prelude` discovery and provider-aware parsing/elaboration;
  ambient providers remain closure dependencies for sound incremental
  invalidation without introducing artificial compile-order cycles.
- **Headless front-end** for tooling / LSP.

---

## 11. Editions

`@edition` + `Cure.toml [project].edition` pin the keyword set and
surface grammar per project (identity, ordering, validation, precedence
resolution). This is what lets `cure migrate` cross editions safely and
keeps renamed keywords from breaking older sources.

---

## 12. General / internal work

Not user-facing, but the bulk of the branch. Summarised for reviewers.

**Kernel foundation.** Built from scratch: NbE value domain, evaluator
(β + projections), read-back, definitional-equality conversion; de
Bruijn shift/substitution; cumulative universe hierarchy; Sigma/pairs,
iota reduction, dependent case eliminator; strict positivity (including
nested/mutual, checked against an Idris oracle); serializable Core proof
terms for independent re-validation; kernel-revalidated totality
certificates (size-change termination, cross-function/mutual) that gate
δ-reduction. A `Validator.release_config` **Final-Core ratchet** rejects
retired nodes (`{:absurd}`, primitive `Eq`/`refl`, primitive `Sigma`).
Dialyzer adopted as a gate over precise `Term.t()`/`Value.t()` unions.

**Soundness audits.** A kernel audit landed fixes S1–S9; the QTT graded
binders (`{:pi,g,..}`/`{:lam,g,..}`/`{:let,g,..}`) forced a
walker-drift pass so Core.Term walkers fail closed rather than launder
grades; conversion failures now report both normal forms.

**Elaborator.** Bidirectional elaboration; Miller (higher-order pattern)
unification with metavariable types; implicit-argument postponement so
argument order no longer decides typability; anonymous-union
canonicalisation; a name-resolution layer (canonical owner-qualified
identity, collision re-keying across module slices, `E089`
ambiguous-name trichotomy); typeclass resolution (inline / dictionary /
erasure, plus higher-kinded `Functor`).

**Antigen — property-based metatheory engine.** Fuzzes the kernel
against its own laws: capture-avoiding β agrees with substitution,
elaborator `Subst.shift` matches kernel `Term.shift`, subject reduction,
progress, conversion reflexivity, lint-soundness. Live generators emit
well-formed indexed families, positivity witnesses, universes/Pi/Sigma
types, and dot-forcing catalogs. A **shape-coverage manifest** gates
assay cells (~98.6% reachable kernel lines); deliberate violations are
tagged as an "immune response." Ships with shrinking and a replay corpus
(`mix antigen`, `.merge`, prune-to-retirement-store).

**Differential oracle.** A separate `test(oracle)` harness pins concrete
dependent-typing scenarios (an elaboration ledger of ~30 rows —
higher-order/Miller inference, J-eliminator refl clusters, dependent
pairs, absurd-`Fin` discharge, impossible clauses, size-change totality)
at parity with **Idris** as the reference implementation.

**AtomVM validation.** The typed OTP macro families (actor / fsm /
supervisor / application) and the FRP slice are exercised end-to-end on
generic-unix AtomVM under checked `{0, ω}` erasure — not just unit-tested
in the compiler.

**Performance.** Memoized module slices and app/edition detection;
linear `infer` on deep constructor spines; linear code-hole scanning.

---

## Breaking changes

- **`start/0`** is the entry point (unchanged; noted for AtomVM).
- Classic pipeline gone — programs relying on the old checker/codegen
  must re-elaborate (mostly transparent; `cure migrate` covers the
  keyword-level breaks).
- `proto`/`impl`, `Ord`, `Eq`, and primitive identity spellings are
  renamed (see §4); migration rules provided.
- `Std.Access` removed → use `Std.Optic`.
- Primitive `Eq`/`refl`/`rewrite` and `bool_elim` retired in favour of
  `Equivalent`/`reflexive` and ordinary inductive definitions.
