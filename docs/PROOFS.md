# Proofs in Cure

Proofs are ordinary Cure values checked by the dependent kernel. There is no
runtime equality token and no separate legacy checker: a declaration proving a
proposition elaborates to checked Core, and proof-only values are erased before
BEAM emission.

The proof *language* — `proof chain`, `because`, `have`, `rewrite`, `simplify`,
`induction` — is elaboration syntax on top of that. It adds no Core
constructors and no kernel rules; everything below expands to terms you could
have written by hand.

Every `cure` fence in this document compiles against the tree as-is.

## 1. Propositional equality

`Std.Equivalent` defines the kernel-recognised identity family:

```cure
@builtin(:eq)
type Equivalent(a: Type) indices (x: a, y: a)
  reflexive : Equivalent(a, w, w)
```

An inhabitant of `Equivalent(a, x, y)` is evidence that `x` and `y` are the
same value. This differs from `Std.Equatable`: `x == y` computes a runtime
`Bool`, while `Equivalent(a, x, y)` is a proposition checked at compile time.

`Equivalent` and `reflexive` are preluded — you only need `use Std.Equivalent`
to reach the combinators `sym`, `trans`, and `cong`.

`reflexive` closes a goal whose endpoints are definitionally equal. Matching on
an equality proof identifies the endpoints, so transport and the usual laws
are written without a primitive `rewrite` node:

```cure
mod Symmetry
  use Std.Equivalent

  fn symmetric(
    {a: Type},
    {x: a},
    {y: a},
    evidence: Equivalent(a, x, y)
  ) -> Equivalent(a, y, x) = match evidence
    reflexive() -> reflexive(x)
end
```

## 2. Indexed propositions

Any indexed family can be a proposition. Its constructors are the valid proof
rules:

```cure
type IsEven indices (n: Nat)
  even_zero : IsEven(Z)
  even_step : IsEven(n) -> IsEven(S(S(n)))
```

A function returning `IsEven(n)` must construct evidence for that exact index.
Impossible branches can be marked `impossible` when constructor-index
unification proves that no value can reach them.

## 3. The proof vocabulary

These are the canonical spellings. There are no aliases — Cure does not accept
`calc`, `by`, `simp`, `simpa`, `congr`, `exact`, or `apply`.

| Form | Role | §
|---|---|---|
| `have <name> [: <Prop>] = <expr>` | name a checked local fact | [3.1](#31-have--named-local-facts) |
| `proof chain` | equational reasoning block | [3.2](#32-proof-chain--equational-reasoning) |
| `because <expr>` / `because` + block | justify one chain step | [3.3](#33-because--justifying-a-step) |
| `simplify` | close the goal by approved reduction | [3.4](#34-simplify) |
| `simplify using [<rules>]` | …with extra rules | [3.4](#34-simplify) |
| `simplify using <proof>` | reuse a near-matching proof | [3.4](#34-simplify) |
| `rewrite using <eq>` | directed rewrite, forwards | [3.5](#35-rewrite) |
| `rewrite backwards using <eq>` | directed rewrite, reversed | [3.5](#35-rewrite) |
| `rewrite using <eq> at <n>` | pick an occurrence | [3.5](#35-rewrite) |
| `rewrite using <eq> in <hyp>` | rewrite a hypothesis, not the goal | [3.5](#35-rewrite) |
| `induction <value>` + `case <Ctor>(…) =>` | structural induction | [3.6](#36-induction) |
| `?name`, `?_` | typed hole | [3.7](#37-holes) |
| `f(label: value)` | named theorem arguments | [3.8](#38-named-arguments) |

All of these are **contextual**: outside their distinctive shape, `have`,
`rewrite`, `simplify`, `induction`, `proof`, and `because` remain ordinary
identifiers. A local variable named `simplify` does not break.

### 3.1 `have` — named local facts

`have` introduces checked local evidence for the rest of the enclosing body.
The proposition annotation is optional when it can be inferred:

```cure
mod Facts
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn inferred(value: Nat) -> Equivalent(Nat, plus(Z, value), value) =
    have fact = reflexive(value)
    fact

  fn annotated(value: Nat) -> Equivalent(Nat, plus(Z, value), value) =
    have fact: Equivalent(Nat, plus(Z, value), value) = reflexive(value)
    fact
end
```

`have` is **not** an assumption. It lowers to a checked local `let` and will not
admit an unproved proposition — if the expression does not prove the stated
fact, you get a type error naming the fact and both propositions.

### 3.2 `proof chain` — equational reasoning

A `proof chain` proves equality between its first and final expressions. Each
step is a full proposition followed by its justification:

```cure
mod OneStep
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn left_identity(value: Nat) -> Equivalent(Nat, plus(Z, value), value) = proof chain
    plus(Z, value) == value
    because reflexive(value)
end
```

In later steps, `_` in the left position means *the result of the preceding
step*. It is not a metavariable and not a proof-search hole:

```cure
mod TwoSteps
  use Std.Equivalent
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn twice_left_identity(
    value: Nat
  ) -> Equivalent(Nat, plus(Z, plus(Z, value)), value) = proof chain
    plus(Z, plus(Z, value)) == plus(Z, value)
    because reflexive(plus(Z, value))

    _ == value
    because reflexive(value)
end
```

Two things that will bite you:

- **A multi-step chain needs `use Std.Equivalent`.** Chaining is elaborated
  through `Std.Equivalent#trans`, and if that name is not in scope the chain
  fails with `UNKNOWN VALUE [E091]` pointing at the whole chain rather than at
  a missing import. A single-step chain does not need it.
- **`==` here is a proposition, not the `Bool` operator.** Version 1 supports
  only propositional equality via `Equivalent`. Inequality chains and
  mixed-relation calculations are not available.

The compact layout above is what the formatter emits. The older vertically
expanded layout — left expression, relation, and `because` progressively
indented — still parses.

### 3.3 `because` — justifying a step

`because` takes either a proof expression (as above) or an indented
**justification block** whose goal is that one step's equality:

```cure
mod Justified
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn left_identity(value: Nat) -> Equivalent(Nat, plus(Z, value), value) = proof chain
    plus(Z, value) == value
    because
      simplify
end
```

Commands run in source order and the block succeeds as soon as the goal is
closed. This is the single most important thing to understand about
justification blocks:

> **Some commands close the goal; some only transform it.** `simplify` closes.
> `rewrite` **does not** — it rewrites the goal and leaves it open.

A block that ends with the goal still open is
`PROOF JUSTIFICATION IS UNFINISHED [E110]`, which is what you get from a block
containing only a `rewrite`. Finish with `simplify`, or with an evidence
expression. Conversely, commands placed after the goal is already closed are
unreachable-proof-step errors.

### 3.4 `simplify`

Bare `simplify` closes the goal using the default approved rule set: beta,
constructor/iota, and let/zeta reduction, certified transparent definitions,
generated defining equations, and a small audited set of orientation-checked
equations. It terminates and builds an ordinary proof certificate — it will not
unfold arbitrary recursive definitions or declare two terms equal because the
host computed so.

Supply extra rules as a **bracketed list**:

```cure
mod ExtraRules
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
    case Z => reflexive(Z)
    case S(previous, induction_hypothesis) => proof chain
      plus(S(previous), Z) == S(previous)
      because
        simplify using [induction_hypothesis]
end
```

Without brackets, `simplify using <proof>` means something different: it is the
readable replacement for Lean's `simpa using`. Both the supplied proof's
proposition and the current goal are normalised under the same rules, and the
proof is used if they agree. If they don't, `SIMPLIFIED PROOF DOES NOT MATCH
[E112]` prints all three propositions — before, after, and what the supplied
proof simplified to.

These two forms are deliberately distinguished by syntax, not by guessing
whether an identifier names a proof or a rule.

### 3.5 `rewrite`

Forward rewriting consumes an equality left-to-right; `backwards` consumes it
right-to-left. Neither closes the goal, so pair it with `simplify`:

```cure
mod Rewriting
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
    case Z => reflexive(Z)
    case S(previous, induction_hypothesis) => proof chain
      plus(S(previous), Z) == S(previous)
      because
        rewrite using induction_hypothesis
        simplify
end
```

`backwards` changes the direction the supplied equality is consumed in. It does
not synthesize a reversed global theorem.

Rewriting searches the goal recursively, including beneath ordinary function
applications, and succeeds automatically **only when exactly one occurrence
matches**. The other two cases are diagnostics, not silent choices:

That recursive search is automatic congruence: if evidence proves `a == b`, a
rewrite beneath `S(a)`, `wrap(a)`, or one argument of `combine(prefix, a)`
constructs the required equality-elimination term automatically. There is no
separate congruence tactic, and no untrusted shortcut in Core.

- Zero occurrences reports the left side it searched for and the current goal.
- Multiple occurrences reports `REWRITE MATCHES MORE THAN ONCE [E111]` and
  labels *every* candidate, with a `Rewrite occurrence 1` / `Rewrite occurrence 2`
  hint per candidate. It never picks the first.

Select one with `at <n>`, numbered left-to-right from 1:

```cure
mod Selected
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
    case Z => reflexive(Z)
    case S(previous, induction_hypothesis) => proof chain
      plus(S(previous), Z) == S(previous)
      because
        rewrite using induction_hypothesis at 1
        simplify
end
```

An out-of-range selector is `REWRITE OCCURRENCE DOES NOT EXIST [E111]`. Note
that the occurrence count depends on direction: an equality with two backwards
matches may have only one forwards.

To rewrite a **hypothesis** instead of the goal, use `in`:

```text
rewrite using theorem in hypothesis_name
rewrite backwards using theorem in hypothesis_name
```

This refines that local proof binding for the rest of the proof context; it
leaves the goal untouched. `at` applies to the goal, `in` to the named
hypothesis — combining both is not supported.

An older `rewrite <proof> in <body>` form (no `using`) also exists and is what
the compiler's own oracle tests use; it elaborates to a Core rewrite with a
synthesized motive. Prefer `rewrite using`.

### 3.6 `induction`

Induction follows the constructors of the selected value. Each `case` binds the
ordinary constructor fields **followed by** the induction hypotheses generated
for structurally recursive fields:

```cure
mod Induction
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
    case Z => reflexive(Z)
    case S(previous, induction_hypothesis) =>
      rewrite induction_hypothesis in reflexive(S(previous))
end
```

Here `S` has one field, so `case S(previous, induction_hypothesis)` binds the
predecessor and then the hypothesis for it. Every binding may be renamed. The
generated hypotheses are specialised to the current branch.

`induction` expands to the datatype's ordinary eliminator — it adds no kernel
induction rule, and the totality checker validates the result through the same
path as handwritten recursion. For non-inductive case analysis, keep using
`match`; there is no separate `cases` command.

Note the arrow: `case <Pattern> =>` uses `=>`, not the `->` of `match` arms.

### 3.7 Holes

`?name` (or `?_` for an anonymous one) stands in for a term you have not
written yet:

```cure E014
mod Holes
  type Nat = Z | S(Nat)

  fn later(value: Nat) -> Equivalent(Nat, value, value) = ?goal
end
```

(That fence is tagged `E014` because it is *meant* to fail compilation — the
doc checker requires exactly that code.)

A hole reports its goal type and local context to editors via a `:hole_goal`
pipeline event, and it blocks code generation.

Two practical points:

- **`cure check` passes a file containing holes.** Only `cure compile` reports
  `UNFILLED HOLE [E014]`. Do not read a green `check` as "finished".
- **`??` is obsolete as of Cure 0.34.** It is rejected with a diagnostic that
  points to `?_`; this prevents old source from silently surviving the breaking
  surface change. Bare `?` remains a proof-search hole, and generated `???`
  placeholders remain reserved for tooling.

### 3.8 Named arguments

A theorem is a function, so invoking it is ordinary call syntax. Labels may
follow a positional prefix:

```cure
mod NamedArguments
  use Std.Equivalent
  type Nat = Z | S(Nat)

  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  fn left_identity(value: Nat) -> Equivalent(Nat, plus(Z, value), value) =
    trans(p: reflexive(plus(Z, value)), q: reflexive(value))
end
```

The elaborator reorders labels into the declared telescope before building
Core. Unknown, duplicate, missing, misplaced, and ambiguous labels are all
`E115` with authored ranges and machine-applicable code actions —
`UNKNOWN NAMED ARGUMENT [E115]` names the offending label and the value it was
given.

This is why the proof language has no `apply`: there is nothing for it to do.

## 4. Generated defining equations

Every total function is specified to expose kernel-checked equations for the
complete paths through its pattern matching, named from source constructor
paths (`dot.Empty`, `succ_int.NegativeSuccessor.Zero`) rather than decision-tree
ordinals like `eq_1`.

An equation member takes the variables needed to reconstruct that branch. For
the successor branch below, `add3.S3(k, y)` certifies the complete authored
equation, including reconstruction of the scrutinised `S3(k)` argument:

```cure
mod DefiningEquations
  use Std.Equivalent

  type Nat3 = Z3 | S3(Nat3)

  fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
    Z3() -> y
    S3(k) -> S3(add3(k, y))

  @lemma
  fn add3_succ_eq(
    k: Nat3,
    y: Nat3
  ) -> Equivalent(Nat3, add3(S3(k), y), S3(add3(k, y))) = add3.S3(k, y)
end
```

Friendly equation calls are resolved during elaboration and emitted only when
reachable from runtime code. Unknown members use `E114`; unused certified
equations remain compile-time-only and do not bloat the BEAM module.

### 4.1 Dependent refinement and named implicit patterns

Pattern matching refines indices before checking a branch. A named implicit
pattern makes an erased constructor index explicit: `{n = .k}` asserts that the
constructor's hidden `n` is definitionally equal to `k`. The dot is a forced
value, not a new binder:

```cure
mod RefinedPatterns
  type Nat = Z | S(Nat)
  type Vec(a: Type) indices (n: Nat)
    vnil : Vec(a, Z)
    vcons : a -> Vec(a, n) -> Vec(a, S(n))

  fn keep({a: Type}, {k: Nat}, value: Vec(a, S(k))) -> Vec(a, S(k)) = match value
    vcons({n = .k}, head, tail) -> value
end
```

The forced equality is checked against branch unification. A wrong value is a
type error; erased indices cannot be smuggled into relevant runtime code.

## 5. Diagnostics

| Code | Title | Raised when |
|---|---|---|
| `E014` | Unfilled hole | a hole survives to `cure compile` (§3.7) |
| `E091` | Unknown value | a proof helper is not imported or an ordinary value name cannot resolve |
| `E109` | Proof chain syntax error | an empty/malformed chain, missing relation/right side/`because`, or a statement after closure |
| `E110` | Proof chain mismatch | adjacent carriers disagree, evidence proves the wrong equality, or a `because` block ends open |
| `E111` | Directed rewrite failed | no match, multiple matches, invalid `at`, unavailable target, or reverse-only match |
| `E112` | Simplification failed | inadmissible rule, residual goal, supplied-proof mismatch, or resource guard |
| `E113` | Induction failed | non-inductive subject, bad case coverage/shape, or unavailable/mistyped hypothesis |
| `E114` | Defining equation unavailable | unknown, inaccessible, uncertified, or ambiguous friendly equation member |
| `E115` | Named argument mismatch | unknown/duplicate/misplaced/missing label or label-ambiguous overload |

Every one of these carries the authored range, and the `E109`–`E115` family
follows the same terminal, JSON, and LSP structured-diagnostic path as the rest
of the compiler. `cure explain E110` prints the catalog entry.

## 6. Trust

`postulate`, bodyless `@extern`, and `believe_me` are explicit trust roots. The
compiler records their canonical identities and dependency reachability:

```bash
cure audit trust My.Module [--format text|json] [--strict] [--target <t>]
```

The report distinguishes a theorem proved from definitions from one that
depends on an axiom. SMT guard coverage is linting outside the trusted kernel;
it can warn about coverage or shadowing but does not manufacture proof
evidence.

Nothing in §3 is a trust root. Proof commands are elaboration syntax: they add
no unchecked Core nodes and do not survive erasure.

## 7. Standard proof modules

- `Std.Equivalent` — identity, symmetry (`sym`), transitivity (`trans`), and
  congruence (`cong`).
- `Std.Proof` — structural equality laws over `Std.Nat`.
- `Std.Proof.Math` — positive-natural and ordering evidence.
- `Std.Decision` — decidable propositions carrying either evidence or a
  refutation.
- `Std.Proof.LinearArithmetic` — checked linear-arithmetic reflection and its
  semantics.

## See also

- [Dependent Types](DEPENDENT_TYPES.md) — indexed programming
- [Kernel](KERNEL.md) — conversion, totality certificates, the trusted boundary
- [Type System](TYPE_SYSTEM.md) — bidirectional checking and erasure
- [Macros](MACROS.md) — the other elaboration-time surface

The authoritative design is
`docs/superpowers/specs/2026-07-21-proof-language-ergonomics-design.md`; §3
locks the vocabulary above and §5 defines the justification-block execution
model. Where it and this document disagree, this document was checked against
the compiler and the spec was not.
