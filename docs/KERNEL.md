# The Dependent Kernel

The kernel is Cure's trusted dependent-type checker: a small core
(`lib/cure/core/`, ~9,200 lines) that re-checks everything the elaborator
produces and trusts nothing it says. This guide explains what the kernel
does today and why each piece exists. For the surface-language view of the
same machinery see [DEPENDENT_TYPES.md](DEPENDENT_TYPES.md) and
[PROOFS.md](PROOFS.md); for the gap between this kernel and Idris/Agda see
[DEPENDENT_KERNEL_PEERNESS_ROADMAP.md](DEPENDENT_KERNEL_PEERNESS_ROADMAP.md).

## Glossary

Dependent type theory has a working vocabulary that its literature takes
completely for granted. If you program for a living but have never used
Agda, Idris, Lean, or Coq, read this first — every term below is used
without ceremony in the rest of the doc. The entries build on each other,
so they are in reading order, not alphabetical order. If you have used a
proof assistant, skip ahead.

### Dependent types

In mainstream languages, types and values live in separate worlds: types
are checked at compile time, values exist at run time, and no type can
mention a value. A *dependent* type system removes that wall.

In a dependent type system, types are ordinary expressions that may
contain values. `Vector(Nat, 5)` is a type (vectors of naturals whose
length is exactly 5), and the `5` in it is a genuine value, not an
annotation. `Vector(Nat, plus(2, 3))` is the same type, which already 
reveals the central consequence:

**To check types, the compiler must be able to run programs.**

Most of the kernel's machinery exists to make that safe.

### Propositions as types (Curry–Howard)

#### Why we tolerate the complexity

Once types can talk about values, a type can state a *claim*.
`Equivalent(Nat, plus(n, Z), n)` is the statement "n plus zero equals n".
A function returning that type, for every possible `n`, is a *proof* of
the statement.

**Checking the program is checking the proof.**

This correspondence (propositions are types, proofs
are programs) is why soundness holes matter so much here: in a language
where some trick produces a value of an impossible type, every
"theorem" becomes provable and the types stop meaning anything. Most of
the strange restrictions below (totality, positivity, universe levels)
exist solely to close such tricks.

### Pi types (dependent function types)

Written `(x: A) -> B(x)`: a function type where the *return type* may
mention the *argument value*. Ordinary function types are the special
case where `B` ignores `x`. Generics are another special case — Java's
`<T> List<T> f(T x)` is a Pi over types, `(T: Type) -> T -> List(T)`.
Full dependency goes further: `replicate : (n: Nat) -> a -> Vector(a, n)`
returns a *different type for every argument value*:
Pass 3, get a `Vector(a, 3)`.
Pass 5, get a `Vector(a, 5)`.
The name "Pi" comes from set theory: such a function is an element of
the *product* Π of all the types `B(x)`, one factor per possible input,
the way a tuple has one slot per position.

### Sigma types (dependent pairs)

Written `(x: A) ** B(x)`: a pair where the *second component's type*
depends on the *first component's value*. Ordinary pairs/structs are the
special case where `B` ignores `x`.

Picture a box with two compartments, where the label on the second
compartment is written by whatever you put in the first. Drop a `3` into
slot one of `(n: Nat) ** Vector(a, n)`, and slot two must now hold a
`Vector(a, 3)`. No exceptions, no negotiation.

Now, bundle a length together with a vector of exactly that length, and
what have you built? A vector of *some length or other* — a plain list.
That's the other reading of Sigma: **"there exists."** A value of
`(n: Nat) ** Vector(a, n)` is a walking existence proof — the witness
(`fst`, the length) stapled to the evidence (`snd`, the vector).

So the duo: Pi says "for all x, ...". Sigma says "there is an x — and
here it is."

### Universes (`Type 0 : Type 1 : Type 2`)

If types are first-class expressions, they need types of their own.
What's the type of `Nat`? `Type`. And the type of `Type`? The naive
answer `Type : Type` makes the logic *inconsistent*.

Imagine I gave you a box that contains all the boxes in the whole universe.
Putting aside the physical impossibility, how could I have even handed you that box?
It should be inside the box of all other boxes!

This is called Girard's paradox, a type-level cousin of Russell's "set of all sets".

But there's a way around this.
I'm instead going to hand you a hyperbox, which very much *does* contains all of the boxes in our universe.
Don't worry, I got it from the multiverse.

To ground this back down, `Nat` is a box, while `Type` is a hyperbox.

Ah, but what if you wanted a hyperbox of hyperboxes?
I'll have my crack team of multiverse-spanning box-thiefs get your new hyperbox of hyperboxes packed up in a jiffy, so long as you're okay with a `Type 1` hyperbox.

You see, `Type` (our hyperbox) is actually shorthand for `Type 0`.
But `Type 0` also needs a type, so its type is `Type 1`.
But `Type 1` also needs a type, so its type is `Type 2`.
In a universe polymorphic language, this goes on forever.
In Cure, we stop there for now.

Three type universes is enough for data, functions over data, and generic functions over types.

*Cumulativity* is the associated subtyping rule: something in `Type 0` may be used where `Type 1` is expected (small types are also big types).

### Telescopes

A telescope is a list of typed variables where each variable's type may
mention all the variables before it:

```
(a: Type, n: Nat, xs: Vector(a, n))
```

Look at `xs`: its type name-drops both `a` and `n`, two of its own
neighbors in the same parameter list. Try writing that in Java. (Don't
actually try writing that in Java.)

In dependent type theory this shape isn't exotic, it's *the* shape.
Function parameter lists? Telescopes.
Constructor arguments? Telescopes.
A family's parameters and indices? Also telescopes.

The name is de Bruijn's, and it's a good one: like a collapsible
telescope, each segment slides out of the one before it and means
nothing without it. `xs` only extends as far as `a` and `n` let it.

### Inductive families, parameters, and indices

Inductive families are the algebraic data types you already know
(Haskell `data`, Rust `enum`, Swift `enum`) after they've been to grad
school: the type's arguments may now *vary by constructor*.

The arguments come in two kinds, and the split matters everywhere in
this doc:

- **Parameters** are uniform. Every constructor of `Vector(a, n)`
  builds vectors of the same element type `a`, exactly like an
  ordinary generic.
- **Indices** are chosen per constructor — each one fills in the blank
  its own way. `empty` declares its result is `Vector(a, Z)`; `prepend`
  declares `Vector(a, S(n))`.

An index is a fact about the value, published in its type. Length, here.
That's how the checker can know "this vector is non-empty" without
running anything — the type already confessed.

(If you've met GADTs in Haskell or OCaml: those are the halfway point.
Full families let indices be arbitrary computed *values*, not just
types.)

### Scrutinee, motive, eliminator

Case analysis, but make it a courtroom.

The **scrutinee** is the value under scrutiny — the thing you're
matching on. The **eliminator** is the typed machinery conducting the
interrogation: pattern matching, as a primitive. And the **motive**,
well, every good case needs a motive.

Here's why it exists. In an ordinary language, every arm of a `switch` expression
returns the same type, end of story. In a dependent match, discovering
*which constructor* built the scrutinee teaches the checker things —
about the indices, about the scrutinee itself — so each branch may
return a differently-refined type. The motive is the formula they're all
instances of: **the result type, written as a function of the
scrutinee.** Feed it `empty`, get one type; feed it `prepend(x, rest)`,
get another; each branch is checked against its own instance.

### de Bruijn indices

Naming variables is asking for trouble: rename one and you're stuck
asking "are these two terms the same, up to renaming?" for the rest of
your life. So the kernel doesn't name variables at all.

It counts.

A variable is a number: how many binders do you walk past, heading
outward, before you reach the one that bound you? `λx. λy. x` becomes
`{:lam, {:lam, {:var, 1}}}` — from the body, skip one binder (`y`), land
on the second (`x`).

Street names change; "second door on the left" doesn't. Two terms are
now equal exactly when they're structurally identical — no renaming
court required — and substitution becomes mechanical.

The price: shift/lift bookkeeping every time a term moves under a
binder. Off-by-one country. Classic bug territory, and part of why the
kernel is kept small enough to stare at.

### Definitional vs. propositional equality

Two very different things wear the name "equals", and half this doc
turns on telling them apart.

**Definitional equality** is equality the checker settles in its own
head. Is `plus(2, 3)` the same as `5`? Run it. Done. Silent, automatic,
no paperwork.

**Propositional equality** is equality you argue for in writing.
`Equivalent(T, a, b)` is a *type* — the claim "a equals b" — and its
values are proofs. You need it the moment computing isn't enough:
`plus(n, Z) = n`
is true, but if `plus` recurses on its first argument, the checker can't
run its way there while `n` is unknown. Somebody has to do induction.

That somebody is you.

`reflexive` is the bridge between the two worlds: it constructs
`Equivalent(T, a, b)` precisely when `a` and `b` are already
*definitionally* equal. It's the proof that says: **"just look."**

### Normalization and neutral terms

How does the checker actually decide definitional equality? Run both
sides until nothing moves — that resting state is the **normal form** —
then compare what's left.

But under binders, evaluation runs into terms it can't finish.
`plus(n, 2)`, where `n` is a variable: which clause of `plus` fires
depends on `n`, and `n` isn't telling. The term is **stuck** — the
polite word is **neutral**. Not lazy. Blocked. Neutral terms get
compared structurally, piece by piece.

"Normalization by evaluation" (NbE) is the standard trick for doing all
this without drowning in syntax-shuffling: interpret terms into real
semantic values — actual host-language closures for functions, explicit
neutral values for the blocked stuff — then read the results back into
syntax. Let the host language's engine do the running.

### β-, δ-, and ι-reduction

Type theorists name their computation rules with Greek letters. Three of
them matter here:

- **β (beta)** — call the function: `(λx. body) arg` steps to `body`
  with `arg` plugged in.
- **δ (delta)** — inline the definition: replace the *name* `plus` with
  the *body* of `plus`.
- **ι (iota)** — the match fires: a case expression whose scrutinee is a
  constructor picks its branch.

Definitional equality is "equal after any amount of β, δ, and ι".

One of these is not like the others. β and ι always make progress; δ is
only as safe as the definition it unfolds. Unfold a looping definition
during type checking and it's the *checker* that loops. So in Cure, δ
has a bouncer: no unfolding without a totality certificate.

### Unification, rigid vs. flexible, the occurs check

Unification is solving little algebra problems on syntax: given
`S(?x) ~ S(Z)` with `?x` unknown, find the assignment (`?x := Z`) that
makes both sides identical. You've met it before — it's the engine
inside Hindley–Milner type inference. Here it runs on index expressions.

Terms come in two temperaments. A **flexible** term is an unknown, open
to suggestion. A **rigid** term has a constructor at its head and will
not negotiate: `S` is `S`, `Z` is `Z`, and no assignment to anything can
change that.

Which makes a *clash* — `S(...) ~ Z` — a beautiful thing. No assignment
in any universe makes those two equal, and that "no" is a theorem: the
case you were considering **cannot happen**. Impossible branches are
born right here.

The **occurs check** handles a subtler dead end: `?x ~ S(?x)`. Nothing
finite is its own successor. Rejected.

And equations that are neither solvable nor refutable — `plus(n, m) ~ Z`,
stuck on variables — are simply *undecided*. A sound checker shrugs and
plays it safe.

### Strict positivity

The rule: a datatype may not mention itself to the *left of an arrow*
in its own constructors. `MkBad : (Bad -> Nat) -> Bad` — rejected at the
door.

Harsh? Look at what that constructor actually is: a `Bad` built out of a
function that *consumes* `Bad`s. Feed the thing to itself, with a little
plumbing, and out comes a well-typed infinite loop — **with no recursion
written anywhere**. A perpetual-motion machine, assembled from one
suspicious datatype declaration.

Haskell accepts "negative" datatypes like this quite cheerfully. But
Haskell isn't trying to be a logic. In a proofs-as-programs language,
that loop inhabits any type you point it at — it "proves" `False` — so
the declaration itself has to be turned away. "Strictly positive" is the
technical name for "recursive occurrences only appear in places that
keep the datatype well-founded".

### Totality and structural recursion

Why on earth does a *type checker* care whether your function
terminates? Two reasons, both fatal:

1. The checker runs your functions during type checking (that's
   δ-reduction). A looping function hangs the compiler.
2. A function that never returns can claim any return type it likes —
   it will never be caught holding the wrong value. `loop : False`
   typechecks beautifully, provided `loop` never comes back.
   **A promise you never have to keep can promise anything.**

So functions the checker may unfold must provably terminate. The classic
decidable criterion is **structural recursion**: recursive calls only on
pieces you got by taking the input apart — `k`, from inside the branch
that matched `S(k)`. Real checkers layer cleverer analyses on top
(lexicographic orders, size-change termination), but every one of them
must stay conservative: better to reject some perfectly fine programs
than to ever, even once, accept a loop.

### Transport by identity elimination

You hold a proof of `Equivalent(T, x, y)`. So... now what? The checker
doesn't spontaneously care — a propositional proof is just a value in
your pocket until you eliminate it.

**Transport** is how you spend it: given the proof, convert something
whose type mentions `x` into the same type with `y` in its place.
Substituting equals for equals, as an explicit move. And it *has* to be
explicit: the only equality the checker applies on its own is the
definitional, run-the-programs kind — your `Eq` proof is precisely the
certificate for an equality that computation couldn't see.

`Equivalent` is an ordinary indexed family recognised by the kernel. Transport
is a single-branch dependent `case`: matching `proof` against `reflexive`
identifies `x` and `y`, after which the branch body checks at the transported
goal. The former primitive `{:rewrite, ...}` node is rejected from final Core.

## The Split: Elaborator vs. Kernel

Cure is split the same way Idris and Lean are. The **elaborator** handles
the friendly surface language — implicit arguments, pattern matching,
holes — and translates it into a tiny, fully explicit core language. The
**kernel** only ever sees that core language, and re-checks it from
scratch. If a soundness bug exists anywhere, it has to be inside the
kernel's few files — that is the trusted computing base (TCB).

Two deliberate exclusions keep the TCB honest:

- **The SMT solver is never trusted.** Z3 runs only as an *untrusted
  lint* over refinement obligations — its verdicts can surface warnings
  but can never certify a kernel judgement.
- **Holes are firewalled, not trusted.** A `{:hole, name}` term
  typechecks against any expected type (so development can proceed
  around it) but blocks codegen: no beam is emitted for a definition
  that still contains one.

## Core Terms

Core terms (`lib/cure/core/term.ex`) are plain tagged tuples using
**de Bruijn indices** for variables — `{:var, 0}` means "the nearest
enclosing binder" — so there are no names and no capture bugs. The grammar
is textbook dependent type theory:

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
| `{:hole, name}` | a typed gap: checks against anything, blocks codegen (see the TCB note above) |

The universe ceiling is hard: `Type 3` is not even a well-formed term
(`Cure.Core.Universe`, `@ceiling 2`).

Note what is *not* in the grammar: there are no boolean literals or
boolean primitives. `Bool` (like `Nat`) is a genuine inductive family,
seeded into every environment through the **builtin-inductive registry**
(`Cure.Core.Builtins.seed` + `Env.register_builtin/3`) — the kernel
eliminates it with the same `{:case, ...}` machinery as any user
datatype, and it erases to native BEAM booleans at emit time (the same
treatment is planned for `Nat` → native `Int`). Definitions and constructor
arguments also carry **usage grades** from `Cure.Core.Grade`'s four-element
carrier `{:erased, :linear, :affine, :unrestricted}` (`{0, 1, ≤ 1, ω}`): an
`:erased`-graded binder exists only for checking and leaves no runtime
footprint, while `:linear`/`:affine` additionally constrain how many times a
bound value may be used.

## Bidirectional Checking

The kernel type-checks in two directions (`lib/cure/core/kernel.ex`):

- `infer(ctx, term)` computes a type for terms whose type is evident from
  their shape — variables, applications, `Type l`.
- `check(ctx, term, expected)` pushes an expected type *into* terms like
  lambdas and pairs, where inference would be awkward.

`check` falls back to `infer` plus the question "are these two types
equal (up to cumulativity)?" — and that question is where dependent
typing gets interesting.

## Type Equality Is Computation

Types compute. Is `Vector(Nat, plus(2, 3))` the same type as
`Vector(Nat, 5)`? Textually no; after running `plus`, yes. The kernel
answers with **normalization by evaluation**:

- `eval.ex` evaluates terms into a semantic value domain — closures for
  functions, "neutral" values for stuck terms like `plus(n, 2)` where `n`
  is a variable.
- `conv.ex` compares two values structurally.

So type equality is "evaluate both sides, compare the results":
definitional equality up to computation.

One twist matters later: evaluation may only unfold a global function
(δ-reduction) if that function has been **certified total**. Otherwise a
looping definition would make the type checker itself loop.

## Inductive Families: Parameters vs. Indices

A family declaration (`lib/cure/core/inductive.ex`) has three parts:

- a **parameter telescope** — uniform arguments, identical in every
  constructor (the `a` in `Vector(a, n)`);
- an **index telescope** — the arguments constructors get to *choose*
  (the `n`);
- per constructor: an argument telescope plus **result index terms** —
  expressions saying which indices this constructor's result carries.

```cure
type Vector(a: Type) indices (n: Nat)
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

Here `empty` has result index `[Z]` and `prepend` has result index
`[S(n)]`, where `n` comes from its own arguments. When a family is
declared (`Inductive.declare/3`, driven from the elaborator's
declaration pass), the telescopes are type-checked and two guards are
enforced:

- **Universe check** — a constructor field cannot live in a bigger
  universe than the family itself (otherwise Girard's paradox smuggles
  `Type l : Type l` in through a data declaration).
- **Strict positivity** (`Inductive.positive?/2`) — the family name may
  not appear to the left of an arrow in a field type.
  `MkBad : (Bad -> Nat) -> Bad` is rejected: a negatively-occurring
  family yields a non-terminating term with no recursion at all, which as
  a proposition is a proof of `False`.

The positivity walk is **nested**: when a field mentions *another*
family, the checker descends into that family's constructors too
(cycle-guarded by a seen-set), mirroring Agda's `Positivity.hs` and
Idris's `Positivity.idr` — so smuggling a negative occurrence through an
intermediate wrapper datatype is also rejected.

## Dependent Case: Index Unification

The centerpiece. When you `match` on a `Vector(a, n)`, the kernel checks a
`{:case, scrut, motive, branches}` node. The **motive** states the type of
the whole expression *as a function of the scrutinee* — that is what makes
the elimination dependent.

The interesting question is: **which branches are even possible?** It is
decided purely by talking about indices. For each constructor,
The kernel's branch unifier compares the scrutinee's type indices with that
constructor's result index terms. If the scrutinee is `Vector(a, Z)`:

- `empty` claims result index `Z`. Unify `Z ~ Z`: succeeds. Branch
  required.
- `prepend` claims result index `S(n)`. Unify `S(n) ~ Z`: two different
  rigid constructor heads — no solution can ever exist. The branch is
  **impossible**, and the kernel lets you omit it (or mark it
  `-> impossible` explicitly; see [MATCH.md](MATCH.md)).

The unifier is first-order and structural, with the classic rule set:

- **Solution** — `?x ~ t` for a flexible variable → record the
  substitution. When the solved variable is one of the constructor's own
  arguments, the branch body is checked with that argument *refined*:
  matching `prepend(x, rest)` against `Vector(a, S(k))` teaches the
  checker that `rest : Vector(a, k)`.
- **Injectivity** — `S(t) ~ S(u)` reduces to `t ~ u` (constructors are
  injective).
- **Deletion** — syntactically identical sides → discard the equation.
- **Clash** — `S(...) ~ Z` → `:impossible`.
- **Cycle** — `x ~ S(x)`, or any equation where a variable occurs
  **strongly rigidly** in the other side (reachable purely through
  constructor/data spines): no finite term is its own strict subterm, so
  the branch is `:impossible`. This is Agda's Cycle rule
  (`var_cycle?`/`strongly_rigid_occurs?` in `kernel.ex`), and it also
  fires on *merged* cycles reached through earlier solutions
  (`a ~ k, k ~ S(a)`). A variable occurring only under stuck
  applications is not strongly rigid — that stays `:undecided`.
- Anything undecidable (e.g. `plus(n, m) ~ Z`, a stuck application) →
  `:undecided`, and the kernel conservatively requires the branch.

This one mechanism is what makes indexed programming pleasant: coverage
checking, impossible-branch discharge, and in-branch type refinement all
fall out of unifying index expressions.

## Propositional equality

`Std.Equivalent` is a genuine indexed family in Core:

```cure
@builtin(:eq)
type Equivalent(a: Type) indices (x: a, y: a)
  reflexive : Equivalent(a, w, w)
```

The builtin marker ties the authored declaration to the kernel's canonical
family and constructor identities. Construction checks endpoint conversion;
elimination is ordinary dependent `case`. Primitive `{:eq}`, `{:refl}`, and
`{:rewrite}` nodes have no live producer and the release validator rejects
them.

## Totality: the Gatekeeper for Computation

Because type checking *runs* functions (in the conversion check), any
function the checker may unfold must provably terminate. The certificate
(`lib/cure/core/certificate.ex`) implements **size-change termination**
(Lee–Jones–Ben-Amram), ported from Idris's
`Core/Termination/SizeChange.idr`:

1. A definition that never calls itself (directly or through its
   mutual group) is accepted outright.
2. Self-recursive definitions are accepted when the size-change
   principle holds: every infinite call sequence would have to strictly
   decrease some structural argument infinitely often — which covers
   single-argument structural descent, argument permutations, and
   lexicographic/Ackermann-style descent.
3. **Mutual recursion** is handled by the cross-function generalisation
   (the `addFunctions` construction): calls between members of a
   mutually-reachable group are analysed with the same size-change
   matrices, so `even`/`odd`-style mutual definitions certify.

Still deliberately conservative: descent must be *structural* (pieces
obtained by pattern matching). Semantic termination arguments — a
measure that shrinks, well-founded recursion on a custom order — fall
outside the certificate. Uncertified definitions may still exist; they
just stay opaque during type checking (δ-reduction never unfolds them).

## Serialization

Core terms carry no PIDs, references, or closures, so every checked term
has a total, reversible JSON-able encoding (`Term.to_external/1` /
`from_external/1`, plus `serialize.ex`). An independent checker can
re-validate the same Core terms — the basis of proof-carrying artifacts
(see [PROOF_CARRYING.md](PROOF_CARRYING.md)).

## Summary

The kernel is a bidirectional checker for a three-universe dependent type
theory with Π, Σ, propositional equality, and indexed inductive families,
where type equality is decided by evaluation, case elimination is driven
by first-order unification of index expressions (Solution, Injectivity,
Deletion, Clash, Cycle), and evaluation itself is gated behind a
size-change termination certificate. Since this doc was first drafted,
three components have already been made less conservative without
becoming unsound: termination (structural-single-argument → size-change
with mutual recursion), positivity (shallow → nested), and unification
(occurs-as-undecided → the Cycle rule). The remaining frontier is
tracked in the peerness roadmap, including discharging more
`:undecided` index equations without expanding the trusted base.
