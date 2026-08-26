# Beginner-Friendly Proof Language Ergonomics

**Date:** 2026-07-21

**Status:** implemented; authoritative for the proof-authoring features
specified here

The complete implementation ledger and acceptance evidence are recorded in
`../plans/2026-07-21-proof-language-ergonomics-plan.md`. The restored affine
semantics workload is kernel-checked through `Std.Proof.LinearArithmetic.Semantics`
and has paired Cure/Idris oracle coverage.

**Implementation ledger:**
`../plans/2026-07-21-proof-language-ergonomics-plan.md`

**Applies to:** parser, formatter, elaborator, proof diagnostics, generated
defining equations, and editor assistance

**Related documents:**

- `2026-07-20-structured-compiler-diagnostics-design.md` and
  `2026-07-20-elm-diagnostic-parity-remaining-work.md` are mandatory diagnostic
  dependencies. Every rejection introduced here follows their registry,
  producer, source-range, rendering, catalog, JSON, and LSP contracts.
- `2026-07-17-proof-authoring-elaborator-ergonomics-design.md` remains the
  living catalog of concrete elaborator and kernel-completeness gaps. This
  document is authoritative when that catalog discusses possible proof syntax.
- `2026-07-18-auto-lemma-proof-search-design.md` owns automatic lemma discovery.
  The constructs below may consume a found proof, but do not change search
  coherence or solver arbitration.
- `2026-07-18-verified-lia-reflection-design.md` supplies the immediate
  acceptance workload. The parked affine-semantic proofs must be expressible
  with this design without changing the trusted kernel.

## 1. Purpose

Cure can express the required proofs today, but routine equational arguments
often become explicit serializations of transitivity, symmetry, congruence,
defining equations, and dependent equality transport. That representation is
useful Core, but it is poor source language.

This design adds a small proof-authoring vocabulary that reads like the
mathematical argument while elaborating to the same ordinary Cure terms. It is
designed for a programmer encountering proofs for the first time, not only for
users already fluent in Lean, Agda, Idris, or Coq tactic terminology.

The user-facing operations are:

1. `proof chain` with `because`;
2. `rewrite using` and `rewrite backwards using`;
3. reuse of a near-matching proof with `simplify using`;
4. structured `induction`;
5. named intermediate facts with `have`;
6. automatic reasoning beneath ordinary function applications;
7. proof-producing `simplify`;
8. generated, descriptive defining equations;
9. automatic dependent-pattern refinement; and
10. ordinary named arguments for theorem calls.

These ten items are one coherent design. Implementations must not substitute
the expert-facing spellings `calc`, `by`, `simpa`, `simp`, `congr`, or `apply`
as the canonical Cure surface.

## 2. Design principles

### 2.1 Small and compositional

A beginner learns five operations: chaining, naming a fact, rewriting,
simplifying, and induction. Multiline `because` blocks compose those same
operations; they are not a second tactic language.

### 2.2 Explicit intent, inferred plumbing

The source says which mathematical fact justifies a step. The elaborator owns
transitivity terms, symmetry, congruence under functions, constructor-index
transport, and generated defining-equation lookup.

### 2.3 Proof-producing automation

Every successful operation produces an ordinary Core proof term. The existing
kernel independently checks the result. There is no trusted simplifier,
rewriter, tactic evaluator, or new equality rule.

### 2.4 Friendly does not mean prose-shaped

The syntax uses a few regular constructs rather than many English phrases.
Words such as `congruence`, `motive`, `transport`, `simpa`, and `lhs` must not be
required to complete an ordinary proof. Advanced diagnostics may expose the
formal term behind an explanation, but the primary message uses source-level
language.

### 2.5 Progressive disclosure

Generated equations, congruence, and dependent refinement are discoverable in
completion and diagnostic detail, but normally invisible. An author can always
request or inspect the explicit proof term produced by elaboration.

## 3. Locked surface vocabulary

The canonical spellings are:

```cure
proof chain
because
have
rewrite using
rewrite backwards using
simplify
simplify using
induction
case
```

`proof` is deliberately not defined as a standalone construct here. It remains
available for a possible future general proof block. `proof chain` is parsed as
one contextual two-word introducer; it does not imply that bare `proof` is a
valid expression.

Proof words should be contextual parser words wherever doing so preserves clear
diagnostics and avoids unnecessary source breakage. This design does not reserve
them globally merely for lexer convenience.

The following are not canonical aliases in the first release:

```text
calc  by  simpa  simp  congr  congrArg  exact  apply  rewrite <-
```

They may appear in comparison or migration documentation, but examples,
completion, formatting, and diagnostics teach the Cure vocabulary.

## 4. The ten features

### 4.1 `proof chain`: equational reasoning

A proof chain is an expression proving equality between its first and final
expressions:

```cure
proof chain
  multiply_int(add_int(a, b), value) == add_int(multiply_int(a, value), multiply_int(b, value))
  because multiply_int_distributes_over_coefficient_add(a, b, value)

  _ == expected
  because induction_hypothesis
```

Every step is a complete proposition followed by its justification and has:

- a left-hand expression (or `_` for the previous result);
- a relation, initially only `==`, and a right-hand expression; and
- a `because` justification.

`_` in the left position means the result of the preceding step. It is not a
new metavariable or proof-search hole. The formatter emits the compact layout
above and `_` for continuation steps. The parser also accepts the older
vertically expanded layout, with the left expression, relation, and `because`
progressively indented, so existing source and deliberate personal formatting
remain valid.

Version 1 supports only propositional equality represented by Cure's canonical
`Equivalent` family. Arbitrary transitive relations, inequality chains, and
mixed-relation calculations are deferred. Restricting the first release makes
step typing and diagnostics deterministic.

If the chain contains expressions of type `A`, it elaborates to evidence of:

```cure
Equivalent(A, first_expression, final_expression)
```

using ordinary reflexivity, symmetry when explicitly requested by a supplied
proof, transitivity, and equality elimination. The chain itself introduces no
Core constructor.

Each `because` accepts either a proof expression:

```cure
_ == result
because known_theorem(arguments)
```

or an indented justification block:

```cure
_ == result
because
  rewrite using head_equation
  rewrite backwards using tail_equation
  simplify
```

A justification block begins with the equality for that one step as its goal.
Commands transform or close that goal in source order. The block succeeds as
soon as it has produced evidence for the goal. Reaching the end with an open
goal is an error; commands after closure are unreachable-proof-step errors.

### 4.2 Directed rewriting

Forward rewriting is:

```cure
rewrite using addition_commutes(a, b)
```

Reverse rewriting is:

```cure
rewrite backwards using addition_commutes(a, b)
```

`backwards` modifies the direction in which the supplied equality is consumed.
It does not mutate or synthesize a reversed global theorem.

Rewriting searches the current goal recursively, including beneath ordinary
function applications. It succeeds automatically only when the chosen
direction has one unambiguous applicable occurrence. Zero occurrences reports
the searched-for left side and the current goal. Multiple occurrences reports
and labels every candidate occurrence; it does not silently choose the first.
The author then uses the `at` selector defined below.

Rewriting a named local hypothesis is supported with:

```cure
rewrite using theorem in hypothesis_name
rewrite backwards using theorem in hypothesis_name
```

This produces a new refined local proof binding for the remainder of the proof
context; it does not alter an earlier immutable source binding at runtime.

When more than one occurrence matches, the author selects the numbered
occurrence shown by the diagnostic:

```cure
rewrite using theorem at 2
rewrite backwards using theorem at 2
```

Occurrences are numbered from left to right in source presentation, starting at
1. The diagnostic and editor action insert the selector, so authors do not need
to count an unlabelled Core tree. `at` selection applies to the current goal;
`in hypothesis_name` applies to that hypothesis. Combining both selectors is
deferred until a real need is demonstrated.

### 4.3 Reusing a near-matching proof

When an existing proof differs from the goal only by approved simplification:

```cure
simplify using previous_proof
```

The elaborator simplifies both the supplied proof's proposition and the current
goal under the same rule set, then uses the supplied proof if the normalized
propositions agree. This is Cure's readable replacement for `simpa using`.

A bare proof expression after `using` is the proof being adapted. A bracketed
list after `using` supplies additional simplification rules instead (§4.7):

```cure
simplify using previous_proof
simplify using [dot.Empty, add_int.ZeroRight]
```

These forms are syntactically distinct and must not be resolved by guessing
whether an identifier names a proof or a rewrite rule.

### 4.4 Structured induction

Induction follows the constructors of the selected value:

```cure
induction count
  case Z =>
    simplify

  case S(previous, induction_hypothesis) =>
    ...
```

The source pattern binds ordinary constructor fields followed by the induction
hypothesis or hypotheses generated for structurally recursive fields. Generated
hypotheses have specialized propositions for the current branch. Authors may
rename every binding.

The elaborator expands `induction` to the datatype's ordinary eliminator and
structurally smaller recursive evidence. It must not add a kernel induction
rule. The totality checker validates the elaborated recursion through the same
path as handwritten definitions.

Ordinary non-inductive case analysis continues to use Cure's existing `match`.
There is no separate general `cases` tactic. Editor code actions generate a
complete `induction` skeleton with all constructors and descriptive binding
names; omitted or impossible cases use the existing coverage rules.

### 4.5 Named intermediate facts

`have` introduces checked local evidence for the remainder of its enclosing
expression or proof block:

```cure
have head_distributes =
  multiply_int_distributes_over_coefficient_add(left, right, value)

have tail_distributes:
  Equivalent(Int, dot(added_tail, values), expected_tail) =
  dot_added_coefficients(rest)
```

The proposition annotation is optional when it can be inferred. `have` lowers
to the existing checked local `let` representation with proof relevance and
erasure determined by the ordinary quantity rules. It is not an assumption and
does not admit an unproved proposition.

The binding is scoped to the following statements/body at the same indentation
level. Duplicate names follow ordinary local-shadowing diagnostics. Failures
name the fact and show its inferred and expected propositions.

### 4.6 Automatic congruence beneath functions

If a proof establishes `a == b`, rewriting may establish equality inside any
well-typed ordinary function context, for example:

```cure
wrap(a) == wrap(b)
add_int(prefix, a) == add_int(prefix, b)
```

The elaborator generates the appropriate equality-elimination/congruence term.
Users do not need `congr`, `congrArg`, `add_int_cong_left`, or
`add_int_cong_right` for the routine single-occurrence case.

Multiple changed arguments may be solved by multiple rewrites or simplification.
Version 1 does not introduce a user-facing congruence tactic. If inference
cannot identify a unique context, diagnostics label the differing arguments
rather than asking the user to understand a congruence combinator.

### 4.7 Proof-producing simplification

The current goal may be simplified with the default approved rule set:

```cure
simplify
```

Additional rules are explicit:

```cure
simplify using [dot.Empty, dot.NonEmpty, add_int.ZeroRight]
```

Simplification may use:

- beta reduction of applied lambdas;
- constructor/iota reduction;
- local-let/zeta reduction;
- certified transparent definition reduction already accepted by conversion;
- generated defining equations;
- explicitly supplied equality proofs; and
- a finite default set of orientation-checked simplification equations.

The simplifier must terminate, record every rewrite, and construct an ordinary
proof certificate. It may not silently unfold arbitrary recursive definitions,
use a theorem in an orientation that fails the termination policy, or declare
two terms equal because a host-language computation says so.

Manual global registration syntax for default simplification rules is not
specified in version 1. Generated equations and a small audited standard set are
sufficient for the first implementation; explicit `using [...]` handles local
needs. This avoids prematurely committing to Lean-style attributes or a public
rewrite-rule termination language.

### 4.8 Generated defining equations

Every total function exposes kernel-checked equations corresponding to complete
paths through its source pattern matching. For example:

```cure
dot.Empty
dot.NonEmpty
succ_int.FromNat
succ_int.NegativeSuccessor.Zero
succ_int.NegativeSuccessor.Successor
```

Names are function-qualified and derived from source constructor paths, never
from decision-tree ordinals such as `eq_1`. Nested matches extend the path.
Where two paths would receive the same public name, that short name is omitted
and completion presents the full source patterns as individually selectable
equations. The equation registry retains stable structural pattern keys rather
than traversal ordinals. A later specification may add explicit source labels
for otherwise-colliding equations; the compiler must never append an unstable
`eq_1`-style number or reject the function merely because a friendly short name
cannot be derived.

Each generated equation is an ordinary `Equivalent` definition checked by the
kernel. Public functions expose their equations across modules; private/local
functions keep equations within the same visibility boundary. Equations carry
source provenance back to the defining clause or match path.

Completion after `dot.` displays the equation name and its full proposition,
including the source pattern. Users should discover equations as properties of
the function rather than memorize generated names.

### 4.9 Automatic dependent-pattern refinement

Matching a dependent constructor refines the entire branch context, not only
the return motive. Constructor-fixed indices, existential index values, sibling
binder shapes, and impossible alternatives become available directly:

```cure
case AddedCons(left, right, value, rest) =>
  ...
```

Authors must not defensively rematch already-refined vectors or manually carry
proof-only constructor fields merely to recover information present in the
constructor type. Residual non-definitional index equalities must be retained as
usable branch evidence rather than discarded.

This item consumes the still-open matching gaps cataloged in the July 17 living
document. It is elaborator completeness work, not proof-search automation. Any
kernel-side adjustment follows the repository's TCB hard-stop, Antigen, and
termination gates; the desired surface does not justify weakening conversion or
coverage checking.

### 4.10 Named theorem arguments

Named arguments are ordinary Cure call syntax, applicable equally to proofs and
runtime functions:

```cure
add_int_cong_right(
  prefix: value,
  from: old_tail,
  to: new_tail,
  proof: induction_hypothesis
)
```

Names refer to source parameter labels and may be mixed with positional
arguments only according to the general named-argument language rule. The
elaborator reorders them into the declared telescope before Core construction,
rejecting unknown, duplicate, omitted-required, or ambiguous labels.

The proof language does not add `apply`. A theorem is a function, and invoking
it uses the same call syntax as every other Cure function. Signature help and
completion show labels for long theorem calls.

## 5. Justification-block execution model

A multiline `because` block is goal-directed elaboration, not an untyped script
interpreted at runtime.

For each statement:

1. the elaborator holds a typed proposition goal and local context;
2. `have` extends that context with checked evidence;
3. `rewrite` replaces the goal or a selected hypothesis while constructing the
   equality-elimination bridge;
4. `simplify` constructs a simplification certificate; and
5. a proof expression is checked against the remaining goal.

A command may close the goal automatically. The block then ends; later commands
are rejected as unreachable. If the final command leaves a goal, the diagnostic
shows the residual proposition and relevant local facts.

This execution model may later be reused by a general standalone `proof` block,
but that construct and its placement rules are out of scope. Implementations
must not add bare `proof` merely because the internal block machinery exists.

## 6. Elaboration and trust boundary

All ten features live outside the trusted equality theory:

```text
surface proof syntax
        |
        v
goal-directed elaboration and proof-term construction
        |
        v
ordinary Cure Core term
        |
        v
existing kernel check
```

The implementation may add generic elaborator data structures for proof goals,
rewrite traces, equation registries, and local evidence. It must not:

- add a kernel axiom, equality constructor, trusted tactic, or solver escape;
- accept a proof merely because simplification or a host function reports
  success;
- emit proof commands, a tactic interpreter, or generated-equation dispatcher
  into runtime BEAM code;
- give generated equations special unchecked status;
- bypass totality, relevance, erasure, positivity, or ordinary kernel checking;
  or
- encode proof syntax as an opaque runtime container.

Proofs and generated equations erase according to existing relevance rules.
Any runtime residue is a grading issue to fix in the ordinary pipeline, not a
reason for proof-specific code generation.

## 7. Structured diagnostics are a feature gate

Diagnostics are part of each feature, not a follow-up cleanup. No proof-language
producer may return a new bare tuple, generic `:conversion_failure`, formatted
string, or catch-all syntax error to a public compilation path.

Every distinct rejection condition introduced here must have:

- an owned producer-variant identifier;
- an entry in `Cure.Diagnostic.Registry` with a stable code, title, severity,
  payload schema version, converter, reachability state, catalog fixture, and
  documentation reference;
- a typed family payload (`SyntaxProblem` for grammar failures and the relevant
  proof/type problem family for elaboration failures);
- exact parser-owned ranges for the complete construct and meaningful children;
- an exhaustive family-adapter conversion with no ordinary-error fallback;
- one real failing Cure program exercising the public compiler path;
- deterministic plain and ANSI terminal snapshots at the catalog widths;
- JSON assertions for the semantic payload and all ranges;
- LSP assertions for the primary range, related information, and edits; and
- producer-branch coverage in `mix cure.diagnostics --coverage`.

Existing diagnostic codes are reused when the semantic condition is genuinely
the same. A new surface construct is not by itself a reason to allocate a new
code. Conversely, a proof-specific condition must not be hidden under E094 or a
generic type mismatch merely to avoid adding a registry entry.

### 7.1 Required producer families and payloads

The exact stable code numbers are allocated through the registry implementation,
but the following producer variants and information are mandatory.

#### Proof-chain syntax and structure

- malformed or empty `proof chain`: construct range, observed token, expected
  first expression, and valid continuations;
- missing relation, right-hand expression, or `because`: preceding step range,
  insertion position, and a machine edit when exactly one token repairs it;
- `_` on the first step: underscore range and explanation that no previous step
  exists; and
- statement after a closed justification: unreachable statement range and the
  earlier statement that closed the goal.

#### Proof-chain typing

- adjacent-step mismatch: the previous result range and next starting range,
  both surface expressions and surface types, and the zero-based internal plus
  one-based displayed step index;
- wrong justification: the complete `because` range, required proposition,
  supplied proposition, and expectation origin identifying the chain step; and
- unfinished justification: the block range, residual surface proposition, and
  useful named local facts.

The primary presentation labels the authored chain step, never the generated
transitivity application. A nested `trans` failure is an internal implementation
leak and fails the diagnostic gate.

#### Rewriting

- no matching occurrence: theorem range, chosen direction, searched surface
  expression, current surface goal, and any near matches;
- ambiguous occurrence: one secondary label per applicable authored occurrence,
  stable left-to-right occurrence numbers, and separate machine edits inserting
  each valid `at n` selector;
- invalid occurrence number: selector range, requested number, and the available
  labeled occurrences;
- unknown or ineligible hypothesis target: target range, local candidates, and
  whether the name exists but is not proof evidence; and
- wrong-direction suggestion: when only the reverse side matches, a
  machine-applicable edit inserting `backwards` and prose using that spelling.

#### Simplification

- rejected rule: rule range, its proposition, and why it cannot be oriented or
  admitted under the termination policy;
- supplied proof still does not match: proof range, simplified supplied
  proposition, simplified goal, and the simplification trace identifiers;
- residual goal after `simplify`: command range, before/after surface goals, and
  the rules that made progress; and
- simplifier resource/termination guard: command range and an honest operational
  explanation without claiming the proposition is false.

The trace is structured machine data. Renderers show a concise summary by
default and an expanded trace on request.

#### Induction

- non-inductive subject: subject range and its surface type;
- missing, duplicate, unknown, or impossible constructor case: relevant case
  ranges, constructor declarations as related information, and safe case-edit
  suggestions where available;
- wrong case-field shape: constructor pattern range, expected fields, observed
  fields, and which recursive fields produce induction hypotheses; and
- unavailable or wrongly specialized induction hypothesis: hypothesis use range,
  recursive field provenance, required proposition, and available proposition.

#### Local facts, equations, refinement, and named arguments

- `have` mismatch labels the fact name and body separately and retains inferred
  and annotated surface propositions;
- unavailable or inaccessible generated equation records the requested
  function/path, visible alternatives, defining-clause provenance, and import or
  qualification repair when known;
- a dependent-refinement failure labels the constructor pattern and the exact
  sibling/index use that could not be refined, retaining residual equations in
  debug data without presenting raw motives as the primary explanation; and
- unknown, duplicate, misplaced, ambiguous, or missing named arguments reuse the
  general call-diagnostic family while preserving parameter labels, declaration
  range, supplied argument ranges, implicitness, and telescope order.

### 7.2 Presentation requirements

At minimum:

- a chain mismatch labels the end of step `n` and start of step `n + 1`;
- a wrong justification labels that `because` clause and explains the two
  propositions in source vocabulary;
- a rewrite miss shows the expression sought and the current goal;
- an ambiguous rewrite labels every applicable occurrence and offers targeted
  `at n` edits without choosing one;
- reverse-direction advice says `rewrite backwards using ...`;
- unfinished justification blocks show the residual goal;
- induction errors distinguish a missing constructor, a wrong field pattern,
  and an unavailable induction hypothesis;
- generated-equation completion shows full propositions and source patterns;
- simplification provides an opt-in equation trace; and
- primary messages avoid raw Core, de Bruijn levels, motives, and equality
  transport unless expanded diagnostic detail is requested.

Every primary range points to authored source. Generated equations and elaborated
proof terms appear as secondary related information with provenance; they never
displace an available authored primary span.

### 7.3 Editor behavior

The LSP must support:

- completion for the contextual vocabulary;
- generated-equation member completion;
- context-aware simplification-rule completion after `simplify using [`, with
  local equality facts, visible generated equations, and the audited standard
  rules filtered and ranked as rules rather than generic values;
- hover for every simplification command and rule candidate; generated-equation
  hover must explicitly say that `map.Cons`, for example, is the certified
  `Cons` defining equation of function `map` (not a module) and show its full
  proposition and defining-clause provenance;
- induction-case generation;
- signature help for named arguments;
- related information linking a generated equation to its definition; and
- code actions for unambiguous repairs proposed by structured diagnostics.

Terminal, JSON, and LSP projections must preserve the same step and occurrence
labels through the structured diagnostic system.

## 8. Formatting

The formatter emits multiline chains in this shape:

```cure
proof chain
  first == second
  because proof_one

  _ == third
  because
    rewrite using proof_two
    simplify
```

It keeps short inline justifications inline and indents block justifications one
level beneath `because`. It never rewrites canonical Cure vocabulary to the
borrowed expert spellings listed in §3.

Generated equation names and named argument labels are stable under formatting.
Formatting must not change rewrite occurrence identity; occurrence diagnostics
are derived from source AST ranges, not formatted character offsets.

## 9. Compatibility and migration

The new constructs are additive. Existing explicit terms using `trans`, `sym`,
`cong`, eliminators, or handwritten defining equations remain valid. The
formatter does not automatically convert explicit proof terms into proof
syntax.

No aliases for Lean/Agda/Idris/Coq tactic words are required. If later user
evidence supports compatibility aliases, they require a separate design and a
canonical formatter target.

Handwritten equation lemmas may coexist with generated equations when their
names differ. A collision with the generated qualified name is diagnosed; the
compiler does not silently replace either theorem.

## 10. Implementation order

The dependency-respecting sequence is:

1. shared typed proof-goal/justification-block elaboration infrastructure;
2. `have`, proving checked local binding and scope behavior;
3. `proof chain` for `Equivalent`, inline `because`, and step diagnostics;
4. multiline `because` blocks;
5. directed unique-occurrence rewriting with automatic congruence;
6. generated defining equations and member discovery;
7. proof-producing simplification, then `simplify using` proof adaptation;
8. structured induction and editor case generation;
9. full dependent-pattern context refinement and residual equation evidence;
10. general named arguments and theorem-call tooling;
11. restore the parked verified-LIA proof phase and rewrite it as the end-to-end
    acceptance workload.

An implementation plan may split these into smaller red/green commits, but may
not reorder a consumer ahead of its proof-producing substrate. Each phase is
committed independently after focused verification.

## 11. Acceptance criteria

The design is implemented only when all of the following hold:

1. Every accepted construct elaborates to ordinary Core evidence and is
   independently kernel-checked.
2. `proof chain` reports the exact mismatching step, not a failure on the final
   nested transitivity term.
3. Forward and backward rewrite work beneath nested function applications and
   reject ambiguity honestly.
4. `simplify` terminates, records its derivation, and cannot accept a forged
   equation or uncertified definition.
5. Generated equations cover every complete path of representative flat and
   nested total definitions, remain stable across recompilation, respect
   visibility, and are usable cross-module.
6. Induction supplies correctly specialized hypotheses and remains subject to
   ordinary totality checking.
7. Dependent constructor branches expose all index-implied refinements needed by
   the affine vector proofs without defensive rematching.
8. Named arguments preserve dependent telescope solving, implicit inference,
   relevance, and runtime arity.
9. Parser, formatter, elaborator, kernel, erasure/codegen, diagnostics, LSP, and
   negative tests cover both successful and rejected forms. Every deliberate
   rejection producer is registry-owned, has a real public-path catalog fixture,
   and reaches 100% registered producer-branch coverage; terminal, JSON, and LSP
   views agree on its semantic payload and authored ranges.
10. The parked `Std.Proof.LinearArithmetic` semantic homomorphism and fold
    preservation proofs are restored and made materially shorter and more
    readable using the new surface.
11. Cure/Idris oracle relations remain correct for the corresponding proof
    corpus.
12. The full suite, canonical stdlib compilation, TCB/termination checks, and
    complete Antigen gate pass with no new trusted primitive.

## 12. Explicit non-goals

- A general standalone `proof` block in version 1.
- Arbitrary relational or mixed-relation proof chains.
- An untrusted runtime tactic interpreter.
- A new kernel equality or induction rule.
- A public global simplifier-attribute language before orientation and
  termination policy are separately specified.
- Silent first-match rewrite occurrence selection.
- Replacing automatic lemma search or the verified LIA certificate producer.
- Making theorem proofs runtime-free by bypassing ordinary quantity analysis.
- Automatically rewriting existing explicit proof source into the new syntax.

## 13. Locked decision summary

The beginner-facing Cure proof language uses:

```cure
have fact = theorem(arguments)

proof chain
  first
    == second because fact

  _ == result
    because
      rewrite backwards using another_theorem
      simplify
```

The compiler supplies congruence, stable defining equations, dependent branch
refinement, proof-term construction, and editor discovery. The kernel continues
to decide whether the resulting proof is valid.
