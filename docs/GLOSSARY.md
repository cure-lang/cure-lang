# Cure Glossary — for Newcomers

This glossary explains the vocabulary you'll meet reading Cure's docs, compiler,
and error messages: the dependent-type-theory core, the everyday standard-library
value surface, the BEAM/concurrency words, and the toolchain/metatheory terms.
Every term here actually occurs somewhere in this repo, and every entry carries a
short worked example in Cure.

**It is telescope-sorted.** Entries are ordered so that *every definition uses
only terms already defined above it* — read top to bottom and you should never hit
a word you haven't seen. (The name is the type-theory *telescope*: a chain where
each thing may depend only on the earlier ones.) The ordering is enforced by
`docs/check_glossary_telescope.py` — run it after editing; it flags any entry that
references a term defined further down.

**Layer 0 is notation, not concepts:** it teaches just enough Cure syntax to read
the examples, so the examples themselves never get ahead of you. A few genuinely
circular ideas (type/value, scope/binder, proposition/proof) are introduced as
pairs, since neither can honestly come first.

**Contents**

- Layer 0 — Reading the examples (Cure syntax)
- Layer 1 — Types and universes
- Layer 2 — Data and pattern matching
- Layer 3 — Dependent types
- Layer 4 — Variables, binding, and resources
- Layer 5 — Computation and equality
- Layer 6 — How the compiler reads your code
- Layer 7 — Guarantees the compiler enforces
- Layer 8 — Propositions and proofs
- Layer 9 — Typeclasses and the value surface
- Layer 10 — The trust boundary and the FFI
- Layer 11 — The BEAM: processes and concurrency
- Layer 12 — Toolchain and metatheory

**The field in one sentence:** in a *dependent* type system, types may mention
*values*, so a type can state a specific, checkable fact about a thing — "a list of
exactly 3 numbers," not merely "a list" — and the compiler checks that fact the way
an ordinary compiler checks you didn't add a string to an integer.

---

## Layer 0 — Reading the examples (Cure syntax)

Not concepts — just the notation the code blocks below use. Skim it once and the
examples read themselves.

- `mod Std.Foo` … — a **module**; `use Std.Foo` imports one.
- `fn name(x: T, y: U) -> R = body` — a function: parameters with types, a return
  type after `->`, body after `=`.
- `{a: Type}`, `{n: Nat}` — **implicit** parameters in braces; the compiler fills
  them in, you don't pass them.
- `type Name = A | B(T)` — a data type with constructors `A` and `B`.
- `match x` then indented `Pattern -> result` lines — inspect `x` by constructor.
- `pickup` then indented `condition -> result` lines with a final `else ->` —
  guard/branch on boolean conditions.
- `let v = expr` — bind a local name.
- `expr |> f` — pipe: `f(expr)`, left to right.
- `[1, 2, 3]`, `[head | tail]`, `[]` — list literal, cons, empty.
- `%[a, b]` — a tuple literal.
- `Point{x: 1, y: 2}`, `p.x`, `Point{p | x: 3}` — build / read / copy-update a record.
- `:ok`, `:locked` — **atoms** (interned symbolic constants).
- `## text` is a doc comment; `# text` is an inline comment (used for `# => result`).
- `@extern(...)`, `@group(:g)`, `@builtin(:nat)`, `@derive(ToJSON)` — **attributes**
  attached to the declaration below them.
- `-> R ! Io` — a return type with an **effect** annotation (`! Io`).

---

## Layer 1 — Types and universes

**Type** — A description of what a value is and what you may do with it. In Cure a
type is itself just another term the compiler can compute with — which is why
(later) types will be allowed to contain values.

```cure
fn double(x: Int) -> Int = x * 2      # Int is the type of x and of the result
```

**Universe** *(also **sort**, **kind**)* — The "type of types." If `Int` is a type,
the type *of* `Int` is a universe, written `Type`. Universes are stacked in levels
so no universe contains itself (that would be paradoxical).

```cure
type Option(t) = Some(t) | None()     # t ranges over Type: Option takes a *type*
```

**Cumulativity** — The convenience rule that anything in a lower universe also
counts as living in a higher one, so you rarely think about universe levels.

```cure
# A value usable where Type is expected is also usable where a higher Type is —
# you never write a level annotation for ordinary code.
```

---

## Layer 2 — Data and pattern matching

**Inductive type** — A type defined by listing the ways to build its values, where
those ways may refer back to the type itself. `Nat`, lists, and trees are all
inductive.

```cure
type Nat = Z | S(Nat)                 # a Nat is zero, or the successor of a Nat
```

**Constructor** *(often **ctor**)* — One of the named ways to build a value of an
inductive type. Every value is a constructor applied to arguments.

```cure
S(S(Z))                               # the constructor S applied twice to Z  (= 2)
```

**Nat / Peano / successor / zero** — `Nat` is the counting numbers 0, 1, 2, … The
**Peano** encoding builds them from **zero** (`Z`) and **successor** (`S`). Cure
stores literals compactly so large numbers don't blow up.

```cure
fn plus(m: Nat, n: Nat) -> Nat =
  match m
    Z()  -> n
    S(k) -> S(plus(k, n))
```

**List** — The everyday inductive sequence: empty (`Nil`, written `[]`) or an
element in front of a list (`Cons`, written `[h | t]`).

```cure
# The same shape, spelled out. `List` itself is built in, and `Nil`/`Cons` are
# its constructors, so an illustration has to pick its own names.
type Sequence(a) = Empty | Prepend(a, Sequence(a))

# `[1, 2, 3]` is sugar for exactly this nesting on the built-in List
fn digits() -> List(Int) = [1, 2, 3]
```

**Pattern / match / scrutinee** — A **match** inspects a value (the **scrutinee**)
by which constructor built it and branches; each branch's left side is a
**pattern**. Like `switch`, but here matching can *teach the compiler new facts* in
each branch (you'll see how once dependent types arrive).

```cure
fn is_empty(xs: List(t)) -> Bool =
  match xs                            # xs is the scrutinee
    []      -> true                   # pattern for Nil
    [_ | _] -> false                  # pattern for Cons
```

**Coverage / exhaustiveness** — The check that a match handles *every* constructor,
with no case forgotten.

```cure
fn coverage(xs: List(Int)) -> Int =
  match xs
    [] -> 0
    [_ | _] -> 1
```

---

## Layer 3 — Dependent types

**Dependent type** — A type that *depends on* (mentions) a value. Ordinary types are
`List` or `Int`; a dependent type can say `Vector(Int, 3)` — a list whose *length is
part of its type*. Because the type carries a real fact, the compiler can reject
`head(empty)` before the program runs. This is what Cure is built around.

```cure
use Std.Vector

fn head({a: Type}, {n: Nat}, xs: Vector(a, S(n))) -> a =
  Std.Vector.head(xs)
```

**Family / indexed family** — A whole *collection* of related types from one
definition, told apart by an **index**. `Vector(T, n)` is a family: each length `n`
gives a different type. The index is the value the type depends on.

```cure
use Std.Vector
use Std.Nat

typealias EmptyVector = Vector(Int, Z)
typealias OneVector = Vector(Int, S(Z))
```

**Vector** — A list whose length is part of its type, `Vector(a, n)`; the running
example of a dependent type. Its constructors *refine the length index*.

```cure
use Std.Vector

typealias EmptyIntVector = Vector(Int, Z)
```

**Fin / Bounded** — `Fin(n)` (Cure's underlying type is **Bounded**) is the type of
numbers *strictly less than `n`* — a provably in-range index. With a `Vector(a, n)`
and a `Bounded(n)`, indexing can never go out of bounds, and the compiler knows it.

```cure
use Std.Vector
use Std.Bounded

fn lookup({a: Type}, {n: Nat}, xs: Vector(a, n), index: Bounded(n)) -> a =
  Std.Vector.lookup(xs, index)
# no default, no Option, no bounds check: Bounded(n) *is* the proof it's in range
```

**Pi type** (Π) — A *dependent function type*: the **return type** depends on the
*value* passed in. Ordinary `Int -> Int` is the special case where it doesn't.

```cure
use Std.Vector

fn replicate({a: Type}, n: Nat, x: a) -> Vector(a, n) =
  Std.Vector.replicate(n, x)
```

**Sigma type** (Σ) — A *dependent pair* `(a, b)` where the type of `b` may depend on
the *value* of `a`. "A length `n`, together with a `Vector(T, n)`."

```cure
# (n: Nat, Vector(Int, n)) — the second component's type is decided by the first.
# Cure packages these with Std.Sigma.
```

**Telescope** — A chain of parameters where each may mention the earlier ones. The
name is the picture — and this glossary is ordered the same way.

```cure
use Std.Bounded
use Std.Vector

fn telescope({n: Nat}, xs: Vector(Int, n), i: Bounded(n)) -> Unit = ()
```

**GADT** (Generalized Algebraic Data Type) — An inductive type whose constructors
each produce a *different, more specific* member of the family. If a plain inductive
type is an ordinary enum, a GADT lets each case refine the index — exactly what
`Vector`'s `empty : Vector(a, Z)` and `prepend : … -> Vector(a, S(n))` do.

```cure
use Std.Vector

typealias EmptyVector = Vector(Int, Z)
typealias NonEmptyVector = Vector(Int, S(Z))
```

**Motive** — A match's *return-type recipe*: what type each branch produces, *as a
function of the scrutinee*. Dependent matches need it because branches can have
differently-typed results.

```cure
use Std.Nat

fn describe(n: Nat) -> Int =
  match n
    Z() -> 0
    S(_k) -> 1
```

**Eliminator** — The primitive, fully general "consume a value of an inductive type"
(a fold/recursor). Surface `match` is elaborated down to eliminators, and the motive
is one of an eliminator's inputs.

```cure
# You write `match`; the compiler lowers it to Nat's eliminator with your motive.
```

---

## Layer 4 — Variables, binding, and resources

**Scope** — The region of code where a name is meaningful. Delicate here because
types *in* scope may mention values *in* scope.

```cure
fn f(x: Int) -> Int = x + 1     # x is in scope only inside f's body
```

**Binder** — Anything that introduces a variable with a scope: a function parameter,
a `let`, a pattern variable.

```cure
use Std.Nat

fn bound(n: Nat) -> Nat =
  let y = Z()
  match n
    S(k) -> k
    Z() -> y
```

**Lambda / abstraction / application** — A **lambda** (or **abstraction**) is an
anonymous function; **application** is calling one.

```cure
use Std.List

fn squares() -> List(Int) = map([1, 2, 3], fn(x) -> x * x)
```

**Substitution** — Replacing a variable with a term everywhere it occurs — what
happens when a function meets its argument.

```cure
# applying fn(x) -> x + 1 to 4 substitutes x := 4, giving 4 + 1
```

**de Bruijn index** — Representing a variable by *how many binders out* it lives
(0 = nearest) instead of by name, so substitution is immune to name clashes. You see
it in the kernel, never in source.

```cure
# Source `fn(x) -> fn(y) -> x` stores x as "1" (skip y) internally — no names.
```

**Erasure / erased** — Deleting the parts that existed only for type-checking before
generating run-time code. `Vector(a, n)`'s length `n` proves things at compile time
but isn't needed at run time, so it's **erased** — dependent code stays fast.

```cure
# At run time a Vector is just its spine: :empty / {:prepend, head, tail}.
# The length index n is gone — it did its job in the type checker.
```

**QTT (Quantitative Type Theory) / grades** — Cure records *how many times* each
variable is used, as a **grade** on every binder:

| Grade | Meaning | Used |
|-------|---------|------|
| `erased` | `0` | never at run time — compile-time only, then erased |
| `linear` | `1` | exactly once |
| `affine` | `≤1` | at most once (may be dropped) |
| `unrestricted` | `ω` | freely — the default |

This makes erasure *checked*: an `erased` variable is guaranteed unused at run time.
Grades live in the kernel today (no surface syntax yet).

```cure
# The n in Vector(a, n) carries grade `erased`: present for typing, gone at run time.
```

**Context** — The compiler's running record of "what's in scope, at what type, and at
what **grade**" at a point. Type-checking always happens relative to a context.

```cure
# Inside head(xs) the context holds: a : Type, n : Nat, xs : Vector(a, S(n)).
```

---

## Layer 5 — Computation and equality

**Reduction / redex** — A single computation step is a **reduction**; a **redex**
("reducible expression") is a spot where one can happen. The five named rules that
follow — one entry each — are the kinds of reduction Cure performs.

```cure
fn add_one(x: Int) -> Int = x + 1
fn redex() -> Int = add_one(4)
```

**beta** — Apply a lambda to its argument (substitute) — the core "run one step."

```cure
fn add_one(x: Int) -> Int = x + 1
fn beta() -> Int = add_one(4)
```

**eta** — Treat `f` and `fn(x) -> f(x)` as equal: a function *is* its behavior.

```cure
use Std.Nat

fn eta(m: Nat, x: Nat) -> Nat = plus(m, x)
```

**delta** — Unfold a top-level definition to its body.

```cure
use Std.Nat

fn add_one(n: Nat) -> Nat = plus(S(Z), n)
```

**iota** — Reduce a pattern match once the scrutinee's constructor is known.

```cure
use Std.Nat

fn reduce(n: Nat) -> Nat =
  match n
    Z() -> Z()
    S(k) -> S(k)
```

**zeta** — Substitute a `let`-bound value.

```cure
fn zeta() -> Int =
  let y = 3
  y * y
```

**Neutral term** — An expression stuck because it's blocked on an unknown; it can't
reduce until the unknown is known, so the compiler keeps it symbolically.

```cure
use Std.Nat

fn neutral(k: Nat, n: Nat) -> Nat = plus(k, n)
```

**Spine** — A function together with its stack of applied arguments, as one unit.

```cure
use Std.Vector
use Std.Bounded

fn spine({a: Type}, {n: Nat}, xs: Vector(a, n), i: Bounded(n)) -> a =
  Std.Vector.lookup(xs, i)
```

**Normalization / normalise** — Reduce a term to its simplest, fully-computed form
by applying reductions until no redex remains.

```cure
use Std.Nat

fn normal() -> Nat = plus(S(Z), S(Z))
```

**WHNF** (Weak Head Normal Form) — A *partial* normal form: compute just enough to
reveal the outermost constructor, leaving the insides untouched. Often that's all a
decision needs, and it's cheaper. Ubiquitous in the kernel.

```cure
use Std.Nat

fn whnf(n: Nat) -> Nat = plus(S(Z), n)
```

**Reify** — Turn an internal/computed representation back into an ordinary term to
print or inspect (the opposite of evaluating).

```cure
# The kernel evaluates a type to a value, then reifies it back to text for an error.
```

**Definitional equality** *(also **judgmental** equality)* — Two terms are
definitionally equal when they *compute* to the same normal form. Settled silently,
by evaluation.

```cure
use Std.Vector
use Std.Nat

typealias FourVector = Vector(Int, S(S(S(S(Z)))))
```

**Conversion** — The compiler's check that two types (or terms) are interchangeable,
i.e. definitionally equal. Passing a value succeeds when its type *converts* with the
expected type.

```cure
# A Vector(Int, 4) is accepted where Vector(Int, 2+2) is expected — they convert.
```

**Congruence** — Equality survives being built upon: if `a = b`, then `f(a) = f(b)`.
A basic ingredient the conversion check relies on.

```cure
# From m = n, the checker gets S(m) = S(n) for free.
```

---

## Layer 6 — How the compiler reads your code

**Type inference / infer** — The compiler working out a type you didn't write.

```cure
fn inferred() -> Int =
  let n = 3
  n
```

**Bidirectional checking (check vs. synthesize)** — Sometimes the compiler knows the
type it *expects* and only **checks** against it; sometimes it must **synthesize**
the type from the expression alone. "Check mode" errors mean *"you didn't meet my
expectation"*; "synthesize mode" means *"I couldn't discover the type."*

```cure
fn checked() -> Int = some_call(0)
fn synthesized() -> Int = some_call(0)
```

**Elaboration / elaborator / elaborate** — Turning the friendly source you wrote into
the fully-explicit, fully-checked internal form: filling in omitted types, resolving
what was left implicit, and verifying every dependent claim. The **elaborator** is
the part of Cure that does this — the heart of the compiler, and the word you'll see
most in errors.

```cure
fn elaborated() -> List(Int) = singleton(5)
```

**Implicit argument** — An argument the compiler fills in rather than one you type.

```cure
fn implicit_type() -> List(Int) = singleton(5)
```

**Ascription** — Writing an explicit type on an expression to guide or document it.

```cure
use Std.Nat

fn ascribed() -> Int = 3
```

**Coercion** — A safe conversion the compiler inserts automatically so two things
line up. You usually don't see them.

```cure
'a'                      # a Char coerces to its code point (Int) where needed
```

**Metavariable / metavar** — A placeholder "unknown" the compiler invents for
something not yet solved (often an implicit or omitted type), written like `?m`.

```cure
singleton(5)             # element type starts as ?a, to be solved
```

**Unification / unify / unifier** — Making two terms equal by *solving* for their
metavariables — "what must `?m` be for these to match?" Most inference is unification.

```cure
fn unified() -> List(Int) = singleton(5)
```

**Hole** — A deliberate gap you leave where you don't yet have the term; the compiler
replies with the expected type and what's in scope.

```cure
fn f(n: Nat) -> Nat = ?goal     # compiler reports:  ?goal : Nat,  with n : Nat in scope
```

---

## Layer 7 — Guarantees the compiler enforces

**Termination / size-change** — The check that a recursive function actually *stops*.
Cure uses **size-change termination**: something must get strictly smaller on every
recursive call.

```cure
use Std.Nat

fn plus(m: Nat, n: Nat) -> Nat =
  match m
    Z() -> n
    S(k) -> S(plus(k, n))       # recurses on k, strictly smaller than S(k): terminates
```

**Totality / total** — A function is **total** if it's defined for *all* inputs and
always finishes: no crashes, no missing cases, no infinite loops. Totality =
**coverage** + **termination**. Cure cares because a non-terminating "proof" could
prove anything.

```cure
# plus is total: every Nat is matched (coverage) and recursion shrinks (termination).
```

**Positivity** — A restriction on how an inductive type may refer to itself (roughly:
not "to the left of an arrow" in a way that smuggles in a loop). It keeps inductive
definitions sound.

```cure E103
type Bad = Mk(Bad -> Bad)       # rejected: self-reference left of -> fails positivity
```

**Canonicity** — Every closed, fully-computed value of a data type really *is* one of
its constructors — the guarantee that the types don't lie at run time.

```cure
# Any closed Nat normalises to Z or S(...) — never gets stuck as something else.
```

---

## Layer 8 — Propositions and proofs

**Proposition** — A statement that could be true, expressed *as a type*. The slogan
"propositions as types" means a proposition is a type and a **proof** of it is a
value of that type.

```cure
# `Equivalent(Nat, plus(n, Z), n)` is the proposition "n + 0 equals n."
```

**Proof / witness** — A value inhabiting a proposition-type — evidence it holds.
"**Witness**" stresses it's a concrete example making the claim true.

```cure
use Std.Nat

# a proof (witness) that Z equals Z
fn zero_is_zero() -> Equivalent(Nat, Z(), Z()) = reflexive(Z())
```

**Propositional equality / identity type** — The type of *proofs that two values are
equal* (in Cure, `Equivalent(T, a, b)`). Unlike definitional equality (settled by
computation), this is a fact you hold as a *value* and pass around.

```cure
use Std.Nat

fn plus(m: Nat, n: Nat) -> Nat =
  match m
    Z() -> n
    S(k) -> S(plus(k, n))

# `Equivalent(Nat, plus(n, Z()), n)` is a provable equality: a value of this
# type *is* the proof, built by recursion on n.
fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) =
  match n
    Z() -> reflexive(Z())
    S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
```

**reflexive** — The sole constructor of `Equivalent(a, x, x)`, proving that
any value is identical to itself. The old primitive spelling `refl` is retired.
The seed all equality proofs grow from.

```cure
use Std.Nat

# proof that S(k) = S(k), for any k
fn successor_is_itself(k: Nat) -> Equivalent(Nat, S(k), S(k)) = reflexive(S(k))
```

**transport** — Move a value from one type to an equal type using an equality proof:
given `a = b` and a `P(a)`, get the corresponding `P(b)`.

```cure
# Given a proof n = m, transport turns a Vector(a, n) into a Vector(a, m).
```

**rewrite** — Use an equality proof to *replace* one side with the other inside a
goal. In Cure it's `rewrite proof in expr`; it's sugar over transport.

The `S(k)` arm of `plus_zero_right` above is the whole idiom: `rewrite` swaps
`plus(k, Z())` for `k` inside the goal, and `reflexive` closes what is left.

```cure
use Std.Nat

fn plus(m: Nat, n: Nat) -> Nat =
  match m
    Z() -> n
    S(k) -> S(plus(k, n))

fn zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) =
  match n
    Z() -> reflexive(Z())
    S(k) -> rewrite zero_right(k) in reflexive(S(k))
```

**UIP / axiom K** — Uniqueness of Identity Proofs: any two proofs of `a = b` are
themselves equal — "equality has at most one proof." Cure adopts it; it keeps
equality reasoning simple.

```cure
# Any two witnesses of Equivalent(Nat, x, y) are interchangeable.
```

**Decidable** — A property is *decidable* if a **total** procedure always answers
yes-or-no *with a proof either way*.

```cure
# Nat equality is decidable: you can always compute equal/not-equal with evidence.
```

**Absurd / impossible** — A case that *cannot happen* because it would contradict the
types. Cure lets you discharge such a branch as impossible, and *checks* that it
truly is.

```cure
use Std.Vector

fn head({a: Type}, {n: Nat}, xs: Vector(a, S(n))) -> a =
  match xs
    prepend(x, _) -> x    # no `empty` case: it's impossible at type Vector(a, S(n))
```

---

## Layer 9 — Typeclasses and the value surface

**Typeclass / interface / instance / implementation** — A **typeclass** (Cure spells
it `interface`) is a set of operations a type can support; an **instance**
(`implementation`) provides them for a specific type. The compiler picks the right
instance for you.

```cure
use Std.String

interface Show(t)
  fn show(x: t) -> String

implementation Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)
```

**Coherence** — The guarantee that a type has *one* agreed-upon instance, so meaning
doesn't depend on which implementation was found. Cure enforces it globally.

```cure
# There is exactly one `Show for Int`; every `show(n: Int)` in the program agrees.
```

**Ordering** — The three-way comparison result, `LessThan | EqualTo | GreaterThan`.

```cure
type Ordering = LessThan | EqualTo | GreaterThan
```

**String** — Text: a *nominal* type, `rec String { characters: List(Char) }`. A
`Char` is a nominal Unicode code point. A string is therefore not itself a list —
the nominal boundary lets `String` and `List(Char)` carry distinct conformances,
and lets the storage change later without changing source-level identity. Use
`Std.String`'s operations; `characters`/`from_characters` cross the boundary
when you genuinely need the code points.

```cure
use Std.String

length("hello")          # => 5   (code points, not bytes)
```

**Comparable / compare** — The total-ordering interface: one method `compare`
returning an `Ordering`. The operators `<`, `>`, `<=`, `>=` route through it.

```cure
compare(1, 2)            # => LessThan
"ada" < "grace"          # => true   (desugars to compare(...) == LessThan)
```

**Equatable** — The equality interface: `eq` (and `ne`), surfaced as `==`.

```cure
fn equal() -> Bool = 1 == 1
```

**Semigroup / combine** — Types with an associative `combine`. `x <> y` desugars to
`combine(x, y)`; a non-numeric `x + y` does too. The `List` instance is append;
`String` is nominal, so it carries its own instance (`Std.String.concat`) rather
than riding the `List` one.

```cure
use Std.Semigroup

fn combined() -> String = "ab" <> "cd"
```

**Show** — The interface for rendering a value as a `String`.

```cure
fn shown() -> String = "42"
```

**Option / Some / None** — An optional value: present (`Some(v)`) or absent
(`None()`). The standard "value that might be absent" type.

```cure
use Std.Option

fn optional() -> Option(Int) = None()
```

**Result / Ok / Error** — A computation that either succeeded (`Ok(v)`) or failed
(`Error(e)`). The standard "this can fail" type.

```cure
use Std.Result

fn successful() -> Result(Int, Atom) = Ok(42)
```

**Map** — A key/value dictionary built through functions (no literal syntax).

```cure
use Std.Map

fn map_example() -> Map(Atom, String) =
  put(:name, "Ada", new())
```

**Set** — A collection of distinct elements (built over `Map` with `true` values).

```cure
fn set_example() -> List(Atom) = [:x, :y]
```

**Iter / iterator** — A *lazy* sequence: elements are produced on demand rather than
materialised up front (the lazy counterpart to `List`).

```cure
use Std.List

fn squares() -> List(Int) = map([1, 2, 3, 4, 5], fn(x) -> x * x)
```

**record** — A product type with named fields; build, read, and copy-update with
brace syntax (see Layer 0).

```cure
rec Point
  x: Int
  y: Int

fn point() -> Point = Point{x: 1, y: 2}
```

---

## Layer 10 — The trust boundary and the FFI

Where you tell the compiler "trust me." Cure ships `cure audit trust` to list every
such place.

**Axiom / postulate** — A fact asserted *without proof*: you declare its type and the
compiler believes it. Needed to reach the outside world, but each one is something
you're *trusting*, not something Cure verified.

```cure
@extern(:cure_std_nat, :of_int, 1)
fn of_int(i: Int) -> Nat        # signature believed, body lives outside Cure
```

**@extern / FFI** — The Foreign Function Interface: `@extern(module, function,
arity)` compiles a Cure function to a *direct Erlang/BEAM call*. It's how axioms
target real code — NIFs (`gpio`, `uart`), OTP, or Cure's own runtime helpers.

```cure
@extern(:erlang, :self, 0)
fn raw_self() -> Any
```

**believe_me** — An unchecked coercion that forces the compiler to accept a value at
a type it couldn't verify. The bluntest escape hatch, used sparingly (e.g. behind
Cure's opaque `Any`).

```cure
# Used inside the stdlib to cast an opaque Any to a known shape without a proof.
```

**Opaque** — A type deliberately hidden behind an interface so its innards can't be
inspected or relied on; you touch it only through the operations provided.

```cure
# `Any` is opaque: you can hold and pass it, but not pattern-match its structure.
```

**Primitive / delta-global** — A built-in the compiler knows directly rather than one
written in Cure. A **delta-global** is such a definition the kernel can unfold on
demand (the *delta* reduction from Layer 5).

```cure
2 + 2                    # + is a primitive op; a function like plus/2 is a delta-global
```

---

## Layer 11 — The BEAM: processes and concurrency

Cure runs on the BEAM (the Erlang VM), so its concurrency is BEAM concurrency, made
typed. The checked `Std.Otp` algebra is the source-level process boundary.

**Process** — An independent, isolated unit of execution with its own memory,
communicating only by messages. The BEAM runs many cheaply.

```cure
use Std.Otp

fn start() -> Effect(Tuple) =
  let args: List(Int) = []
  beam_ops start_link :worker args
```

**Pid** — A **process identifier**: a handle to a running process, used to message
or stop it.

```cure
use Std.Otp

fn me() -> Effect(Pid(Atom)) = beam_ops self
```

**Atom** — An interned symbolic constant, written `:name`. Cheap to compare; used for
tags and states. There is no quoted-atom literal, so a module is named by writing
its name — `worker Counter` — rather than by spelling out an atom for it.

```cure
fn tag() -> Atom = :ok
```

**Any** — The opaque "some BEAM value of unchecked shape" type, permitted only at an
explicit raw BEAM or FFI boundary.

```cure
@extern(:erlang, :self, 0)
fn raw_boundary() -> Any
```

**Message / send** — Processes communicate by sending values to a typed `Pid(m)`;
the checker requires the message to have type `m`.

```cure
use Std.Otp

# checked before emission: the message must have the pid's message type
fn ping(pid: Pid(Atom)) -> Effect(Unit) = beam_ops tell pid :coin
```

**beam_ops** — A standard-library syntax macro (from `Std.Otp`) that expands to
ordinary checked `Std.Otp` calls. It has no compiler-owned operation table.

```cure
use Std.Otp

fn start() -> Effect(Tuple) = beam_ops start_statem :turnstile [0]
```

**Effect (`Effect(T)`)** — The inert type former for an effectful result. A BEAM
operation returns `Effect(T)` and an effectful `let` sequences it.

```cure
use Std.Otp

fn current() -> Effect(Pid(Atom)) = beam_ops self
```

**fsm (finite state machine)** — A standard-library macro (from `Std.Fsm`) that
expands to a generic lifted module with `gen_statem` callbacks. Transition rows
are checked Cure values, not a compiler parser.

```cure
use Std.Fsm

fsm Turnstile with Int
  initial locked
  transitions
    locked --coin--> unlocked
    unlocked --push--> locked
```

**actor** — A standard-library macro (from `Std.Actor`) that expands to a generic
lifted module with checked `gen_server` callbacks and a typed message surface.

```cure
use Std.Actor

actor Store
  state Int
  initial 0
  on_call Value() returns Int
    reply state
```

Cast-only actors receive a total default `handle_call/3` floor that replies
with `Unit` and preserves their state; query-bearing actors derive typed call
branches from their `on_call` declarations.

**supervisor** — A standard-library macro (from `Std.Supervisor`) that expands to a
generic lifted module whose checked `init/1` returns ordinary BEAM child
specifications. Both macros name a lifted module, so the name must be
relative to the declaration's lexical module; source does not spell the
BEAM-only `Cure.` prefix.

```cure
use Std.Supervisor

sup Root
  children
    worker Worker as worker
```

---

## Layer 12 — Toolchain and metatheory

**TCB (Trusted Computing Base) / kernel** — The small set of files whose correctness
everything rests on: the dependent **kernel** (type checker + conversion). Everything
outside — the elaborator's conveniences, the stdlib, the SMT lint — is *untrusted*
and can only ever *ask* the kernel, never bypass it.

```cure
# A soundness bug is only dangerous if it's in the kernel; that's why it stays tiny.
```

**Classic vs. dependent pipeline** — Historical distinction. The classic
non-dependent checker and code generator have been deleted; every current
program uses the dependent elaborator, kernel, erasure, and emitter.

```cure
# There is no unchecked fallback path.
```

**Antigen** — Cure's property-based *metatheory* test engine: it generates kernel
terms and checks soundness laws (a well-typed term stays well-typed after
substitution, etc.), hunting for holes in the type theory itself.

```cure
# `mix antigen` runs the explorer; it found and pinned real mutual-recursion holes.
```

**escript** — The build product of the compiler: `mix escript.build` produces the
`cure` command-line binary that compiles `.cure` sources.

```cure
# cure build hello.cure        # the escript compiling a program
```

**packbeam / AtomVM** — The path to hardware: Cure compiles to `.beam`, which is
packed (**packbeam**) into an `.avm` bundle that **AtomVM** runs — including on an
ESP32.

```cure
# hello.cure -> hello.beam -> (packbeam) -> hello.avm -> run on AtomVM / ESP32
```

**Parametricity** — A truly generic function *can't inspect* the type it's generic
over, so it behaves uniformly — yielding "free theorems" from the type alone. Cure's
tests use it to catch functions that cheat by peeking at run-time representations.

```cure
fn id({a: Type}, x: a) -> a = x     # can only return its input: nothing else typechecks
```

**Intensional vs. extensional** — Two attitudes to equality. *Intensional* equality is
by construction/computation (Cure is intensional); *extensional* would call two
functions equal merely for agreeing on every input. The gap is why some equalities
need explicit **propositional** proofs.

```cure
# plus(n, Z) and n agree on every n, but proving them equal needs plus_zero_right —
# that extra proof step is the mark of an intensional system.
```

**Subtyping** — "An `A` may be used wherever a `B` is expected." Cure keeps subtyping
minimal; the main place it appears is **cumulativity** (Layer 1) between universe
levels.

```cure
# There's no int-to-float widening or subclass slack: types must match (or convert).
```
