# Proofs in Cure

Proofs are ordinary Cure values checked by the dependent kernel. There is no
runtime equality token and no separate legacy checker: a declaration proving a
proposition elaborates to checked Core, and proof-only values are erased before
BEAM emission.

The proof *language* — `proof chain`, `because`, `have`, `rewrite`, `simplify`,
`induction`, and explicit solver commands — is elaboration syntax on top of that. It adds no Core
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

These are the canonical spellings. Cure does not add Lean aliases such as
`calc`, `simp`, `simpa`, or `congr`. `by` introduces an explicit solver or a
declared computed tactic; it is not a general tactic-block introducer.

| Form | Role | §
|---|---|---|
| `have <name> [: <Prop>] = <expr>` | name a checked local fact | [3.1](#31-have--named-local-facts) |
| `proof chain` | equational reasoning block | [3.2](#32-proof-chain--equational-reasoning) |
| `because <expr>` / `because` + block | justify one chain step | [3.3](#33-because--justifying-a-step) |
| `simplify` | close the goal by approved reduction | [3.4](#34-simplify) |
| `simplify using [<rules>]` | …with extra rules | [3.4](#34-simplify) |
| `simplify using <proof>` | reuse a near-matching proof | [3.4](#34-simplify) |
| `simp?` | `simplify` + report which ambient lemmas fired | [3.4](#34-simplify) |
| `rewrite using <eq>` | directed rewrite, forwards | [3.5](#35-rewrite) |
| `rewrite backwards using <eq>` | directed rewrite, reversed | [3.5](#35-rewrite) |
| `rewrite using <eq> at <n>` | pick an occurrence | [3.5](#35-rewrite) |
| `rewrite using <eq> all` | rewrite all original occurrences | [3.5](#35-rewrite) |
| `rewrite using <eq> in <hyp>` | rewrite a hypothesis, not the goal | [3.5](#35-rewrite) |
| `induction <value>` + `case <Ctor>(…) =>` | structural induction | [3.6](#36-induction) |
| `?name`, `?_` | typed hole | [3.7](#37-holes) |
| `f(label: value)` | named theorem arguments | [3.8](#38-named-arguments) |
| `exact <proof>`, `apply <proof>` | close a justification with checked evidence | [3.9](#39-explicit-evidence-and-solvers) |
| `by search`, `by positivity`, `by assumption`, `by decide [using <decision>]`, `by omega` | checked solver commands | [3.9](#39-explicit-evidence-and-solvers) |
| `tactic <rule> computed by <callback>` | declare a goal-inspecting checked-request callback | [3.10](#310-goal-inspecting-computed-tactics) |
| `:goals` / `cure/proofState` | REPL / custom LSP goal inspection | [3.11](#311-goal-views) |

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

Certified recursive definitions **do** compute through the existing certified
delta-normalization path. For example, `plus(Z(), plus(Z(), value))` simplifies
to `value`. By contrast, `plus(value, Z())` with neutral `value` needs induction
or an induction lemma, in Cure as in Lean; it is not a missing unfolding rule.

Use `@simp` (or `@lemma(:simp)`) to register an equality for ambient
simplification. This uses Cure's decorator syntax, not Lean's `@[simp]`.
The declaration must strictly decrease the number of Core nodes without
introducing or duplicating quantified variables. Equal-size, expanding, cyclic,
and unsupported binder-containing rules are rejected at declaration with E112.
Only certified, kernel-checked proofs participate. Safe ordinary `@lemma`
equations remain ambient for compatibility; unsafe orientations are ignored
unless explicitly opted into simp validation.

```cure
mod AmbientSimplification
  type Nat = Z | S(Nat)
  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))

  @simp
  fn plus_zero(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
    case Z => reflexive(Z())
    case S(previous, ih) => rewrite ih in reflexive(S(previous))

  fn nested(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
    plus(plus(value, Z()), Z()) == value
    because simplify
end
```

The ambient set is imported with its checked module interface and runs in
deterministic registry order to a fixed point, with a resource guard.

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

#### `simp?` — which lemmas fired

`simp?` is `simplify` with the fired-rule report switched on. It runs **exactly
the same simplification** — same rule set, same traversal, same evidence — and
then names the ambient lemmas that actually rewrote the goal. It is a debugging
command, not a second prover: a goal that closes under `simplify` closes
identically under `simp?`, and one that fails under `simplify` fails under
`simp?` too.

The report is emitted two ways: as `%{kind: :lemma, name: ...}` entries in the
proof trace, and as a `:simp_trace` pipeline event carrying
`%{lemmas: [...], rules: [...], command: span}`. Subscribe to it with
`Cure.Pipeline.Events.subscribe(:type_checker, :simp_trace)`.

The event reports only this successful invocation's progress, not earlier
entries already on the goal's trace. Ambient lemmas that were tried but did not
apply leave no named entry; a lemma used twice may appear twice. `rules` also
carries the current explicit-rule, reduction or proof-adaptation trace entries,
including for `simp? using [rules]` and `simp? using proof`. Event metadata uses
the command's actual source file and line. Failed simplification remains a
diagnostic, not a fabricated successful trace report.

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

Use `rewrite using theorem all` (or `rewrite backwards using theorem all`) to
select every occurrence found in the **original** normalized goal, in
left-to-right order. Each replacement produces an ordinary equality transport;
new occurrences introduced by the replacement are not revisited. The command
still leaves the transformed goal open. Zero matches is still an error.
The single-occurrence default is unchanged.

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

A surviving hole blocks code generation. The custom `cure/proofState` request
and REPL goal view observe its actual expected type and named local context
where the hole is checked (§3.11). For example, a hole used as an `Int` argument
to a function returning `Float` requires `Int`, not `Float`.

The legacy `Program.hole_goals/1` API and existing hole inlay hints remain
definition-level return/context summaries. They must not be interpreted as
precise nested-hole states or as a completed cursor-position goal panel.

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

Ordinary calls cover forward reasoning; they do not replace backward reasoning.
The currently supported `apply` closes a goal with supplied evidence, like
`exact`; generating new premise goals from an under-applied theorem is later
goal-API work, not an implemented feature.

### 3.9 Explicit evidence and solvers

Inside a `because` justification, `exact expression` checks the expression
against the goal. `apply expression` currently requires that application to
close the goal too. Both inline and block forms are supported; neither creates
unchecked evidence.

The explicit solvers also work as function bodies and in checked expression
positions, including non-equality propositions:

```cure
mod ExplicitSolvers
  use Std.Proof.Math
  use Std.Decision

  fn reuse(n: Nat, h: IsPositive(n)) -> IsPositive(n) = by search
  fn assumed(n: Nat, h: IsPositive(n)) -> IsPositive(n) = by assumption
  fn positive_sum(n: Nat, m: Nat, h: IsPositive(n)) -> IsPositive(plus(n, m)) = by positivity
  fn decided() -> Equivalent(Bool, True(), True()) = by decide
  fn explicit_decision() -> IsPositive(S(Z())) = by decide using decide_is_positive(S(Z()))
end
```

- `by search` uses local evidence, checked projections, and tagged lemmas.
  Missing or ambiguous evidence fails with E110.
- `by assumption` is the deliberately narrow sibling of `by search`: it closes
  the goal with a **local hypothesis** whose type is the goal, and consults no
  lemmas, projections or decision procedures. Its outcome is therefore
  predictable from the goal state alone. Like `search`, it only uses a bare
  local binder when the goal is a proposition — a proof-relevant value type
  such as `Nat` is never silently inhabited by a local value.
- `by positivity` uses the `Std.Proof.Math.IsPositive` fragment: successors,
  addition, multiplication, and available sign evidence. It is not generic
  lemma search, and refuses zero or an unknown sign.
- `by decide` infers the certified `Std.Decision` Boolean-equality decider.
  `by decide using expression` handles a supplied `Decision(P)` for any goal
  `P`. Certified reduction must expose `Yes(evidence)`, and that evidence is
  checked against the original goal. `No`, stuck decisions, unsupported
  fragments, and resource exhaustion fail closed. A host Boolean is not proof.
- `by omega` reconstructs a bounded non-strict integer-order fragment. Supported
  targets are `Std.Proof.IntOrder.IsLessThanOrEqual` propositions, using actual
  local order evidence, reflexivity, transitive paths, addition of the same
  term to both sides, addition of two inequalities, and scaling by a literal
  natural. Reconstruction uses at most 128 original local slots, depth 12,
  512 steps, and scalar literals at most 1024. Each intermediate candidate and
  the final evidence are checked at their actual propositions.

  The untrusted producer/reifier searches for Farkas candidates, and the
  certified `Std.Proof.LinearArithmetic.check_lia_candidate` computes a Boolean
  verdict. That successful verdict is **not** evidence of the original goal:
  admission also requires ordinary Core evidence reconstructed with checked
  `Std.Proof.IntOrder` lemmas. The reflection module's
  `goal_evaluates_true` preserves supplied evidence of
  `IsTrue(evaluate_atom(goal, valuation))`; it is not a theorem turning a
  candidate-checker result into arbitrary goal evidence.

  Strict inequalities, equality goals, nonlinear expressions, algebraic
  rearrangements or other unreconstructed goals, and exhausted bounds refuse.
  Closed non-reflexive literal comparisons are not discharged by this
  reconstruction slice either. This is not complete Presburger automation or
  a general Farkas checker-to-goal soundness theorem.

Internally, `ProofGoal.new/5` preserves the original obligation and
`ProofGoal.inspect_goal/1` exposes its target and hypotheses.
`Tactic.command/1`, sequencing, focus, all-goals, choice, and bounded repetition
retain checked solutions in `Tactic.Result`; an empty goal list alone is not
enough to reconstruct a proof. Named template tactics are described in
[`MACROS.md`](MACROS.md#21-tactic-rules--a-new-proof-command). They compose these
checked commands and may return an open goal for a later command.

### 3.10 Goal-inspecting computed tactics

A `tactic <rule> computed by <callback>` declaration names an ordinary Cure
function evaluated through the checked `MacroExpand.expand_typed` executor.
The callback receives one `Syntax` argument per declared capture, in order,
followed by a typed `Std.Tactic.Goal`. It can choose operations by inspecting
the actual target and local hypotheses rather than merely expanding captures
into a fixed template.

```cure
mod GoalAwareTactics
  use Std.Tactic
  use Std.Syntax
  use Std.Bool
  use Std.Equivalent

  macro Tactics
    tactic close computed by close_goal

  fn close_goal(g: Goal) -> MacroResult = match is_equality(g)
    True() -> expand(Std.Tactic.simplify(g))
    False() -> reject_goal("this tactic requires an equality")

  fn theorem(x: Int) -> Equivalent(Int, x, x) = by close
end
```

Qualify `Std.Tactic.simplify(g)` as above: it is an ordinary helper function,
distinct from the contextual `simplify` proof command. A computed rule can be
invoked in a `because` justification or as an explicit `by close` checked body.
Source-backed imports are supported; interface-only macro grammar publication
remains a separate inherited limitation.
An imported bare callback name requires a provider file with one module
identity. If the provider file contains several modules, qualify the callback
explicitly; an ambiguous home is refused rather than resolved from caller scope.

**Inspection values.** `Goal` carries `target: Syntax`,
`hypotheses: List(Hypothesis)` and an opaque `state: Syntax` handle. Each
`Hypothesis` has an authored `name: String` and `type: Syntax`.
`goal_target`, `goal_hypotheses`, `has_hypothesis`, `hypothesis_type_of` and
`hypothesis_is` expose this data.

The inspection schema is structural, not parser AST or a quotation of evaluator
values. A family application is `Node(short_name, attrs, children)`, with
`KV(:name, SAtom(qualified_name))` and a `:parameters` count in `attrs`;
children are parameters followed by indices. Thus `Equivalent(Int, x, y)` has
tag `:Equivalent` and three children. A local is
`Leaf(:variable, [KV(:index, SInt(index))], SStr(authored_name))`.
Constructor applications also carry qualified identity. Other forms retain
structural children; binder bodies use the synthetic inspection name
`$binder`. This data is for inspection, not proof evidence; matching a short
head name cannot establish the goal.

**Result protocol.** Return `expand(operation)` or
`expand(Node(:list, [], operations))`, or use `reject_goal` / `reject_with`
for authored refusal diagnostics. Every operation retains the supplied goal's
fresh invocation handle. Missing, duplicated, stale or forged protocol fields
are refused. A callback cannot replace the actual target by editing reflected
data or reuse another invocation's handle.

At most 256 operations may be returned. The closed vocabulary includes
simplification, explicit-rule simplification, forward/backward/all rewrites,
`exact`, closing `apply`, and the explicit solver clients. Arity and arguments
are validated, and operation arguments cannot introduce another deferred
computed use. Generated binders use explicit `Std.Syntax.fresh(...)` markers;
ordinary authored identifiers are not silently renamed.

The callback runs once; operations run in order through existing checked
commands. They may leave a transformed goal for a later command, but an
unfinished whole proof still refuses. Returned syntax is a set of requests,
not evidence or a trusted Core-construction API. Closure evidence is
kernel-checked at the original obligation. Premise-generating `apply` and a
reusable induction command remain open features.

### 3.11 Goal views

`Cure.Elab.ProofState` provides scoped presentation-only observations of
commands and checked holes. It publishes `:proof_state` pipeline events with a
phase (`:before`, `:after`, `:failed`, `:unfinished`, or `:hole`), source spans
and the ordered remaining goals. A successfully closed command has no remaining
goals. Each goal includes the target and named hypotheses; rendering deferred
`have` facts preserves the physical kernel-context names rather than shifting
the target onto the new fact's name.

The custom LSP request `cure/proofState` accepts `textDocument.uri` and
`position`, using the negotiated UTF-8/16/32 encoding. Inside a command it
returns that command's input state; at the command's end or between commands it
returns its output. A refused/unfinished command retains the available residual
state instead of requiring a successfully elaborated document. A cursor outside
an observed proof region returns no goals. Responses carry
`{"goals": [{"function": "...", "goal": "...", "context": ["x : Int"]}]}`.

REPL `:goals` shows the last definition submission's remaining states, including
a refused proof, without installing failed definitions. `:reset` clears that
retained view. `Cure.REPL.Session.goals/1` uses the same capture API for session
definitions. These observations do not resolve holes, certify definitions or
weaken the code-generation firewall.

**Scope boundary:** the server capability and REPL path are implemented, not
a VS Code goal-panel consumer. Legacy `Program.hole_goals/1` and existing hole
inlay hints still summarize enclosing definitions; they are not interchangeable
with this precise command/hole view. C7 and authoritative Phase 4 therefore
remain partial.

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
- `Std.Proof.LinearArithmetic` — linear-arithmetic data, candidate checking and
  semantics; Boolean certificate acceptance is not a general goal-soundness
  theorem.
- `Std.Proof.IntOrder` — integer-order propositions and checked reconstruction
  lemmas used by the bounded `omega` client.
- `Std.Tactic` — typed goal inspection and authenticated checked-command
  requests for computed tactics.

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
