# Beginner-Friendly Proof Language Ergonomics Implementation Plan

> **Execution rule:** implement this plan task by task in order. Each task is a
> red/green vertical slice and receives its own descriptive commit. Do not defer
> diagnostics, formatting, catalog coverage, or editor support to a cleanup
> phase when the task introduces their producer or syntax.

**Goal:** Implement the ten features locked by
`docs/superpowers/specs/2026-07-21-proof-language-ergonomics-design.md`, then
restore and finish the parked verified-LIA semantic proofs using the new surface.

**Architecture:** Proof syntax is parsed into explicit source AST nodes with
parser-owned ranges. A shared goal-directed elaboration layer turns those nodes
into ordinary Cure Core evidence (`Equivalent`, `reflexive`, `trans`, `sym`,
equality elimination, cases, and lets). Generated equations and simplification
rules are certified definitions in the ordinary environment. The existing
kernel independently checks every result; no proof command or interpreter
reaches runtime code.

**Baseline:** refreshed at merge commit `2a350d1d` (`elaborator-gaps` at
`8dab525d`). Baseline verification: 5,275 tests, 0 failures, 6 excluded; 135
expected Antigen immune responses; 318/318 Antigen shape coverage.

## Global constraints

- The authoritative surface is the July 21 proof-language specification. Do not
  replace Cure vocabulary with `calc`, `by`, `simpa`, `simp`, `congr`, `exact`,
  or `apply`.
- `proof chain` is a contextual two-word introducer. Bare `proof` remains the
  existing proof-container introducer where that grammar applies and is not
  expanded into a general proof block by this plan.
- No new kernel axiom, equality constructor, induction rule, trusted
  simplifier, solver escape, or runtime tactic interpreter.
- Do not alter `lib/cure/core/**` for convenience. A genuine kernel
  completeness issue is a TCB hard stop: isolate it with `Cure.Dev.Trace`, add
  termination/soundness antibodies, obtain review, and run the full Antigen
  gate before proceeding.
- Every generated proof term is checked by `Cure.Core.Kernel`; every recursive
  proof remains subject to totality; every proof binding follows ordinary
  relevance and erasure.
- Every new rejection producer is structured at its point of knowledge. It
  receives registry ownership, a typed payload, exact authored ranges, an
  exhaustive adapter, a real public-path catalog fixture, terminal/JSON/LSP
  tests, and producer-branch coverage in the same task that introduces it.
- Reuse E093 only for a genuine contextual type disagreement. Do not hide a
  proof-chain, rewrite, simplification, induction, or named-argument condition
  under E093 or E094 merely to avoid a registry entry.
- One `mix` command at a time. No concurrent stdlib compilation or test runs.
- Preserve both parked stashes by object identity until their designated tasks:
  - disposable `have` prototype: `8c42c17d0704ef8c033a1d7416b67046b1401ed6`;
  - LIA Task 4 work: `ae07ebfacef1a558cd3d98f237c66339dd65a166`.
- The uncommitted files currently present in the separate `elaborator-gaps`
  worktree are not part of baseline `d2219191`. Before Task 1, re-check whether
  that branch gained a new committed tip. Merge it normally if so; never copy or
  commit another worktree's uncommitted files.
- Commit author remains `Made In Heaven <madeinheaven@madeinheaven.com>`; do not
  add a co-author or tool trailer.

## Verified current-state anchors

Re-check these symbols before editing; line numbers will drift.

- `lib/cure/compiler/parser.ex`
  - `parse_prefix/1` dispatches contextual `rewrite` and contextual `proof`.
  - `parse_rewrite/2` parses legacy expression syntax
    `rewrite <proof> in <body>` into `{:rewrite_expr, ...}`.
  - `parse_expr/2`, `parse_infix/4`, and `parse_prefix/1` are the Pratt parser
    seams. Ordinary `==` is deliberately non-associative, so proof chains need
    their own step parser rather than relaxing global fixity.
  - `parse_block/1` / `parse_block_body/3` build `{:block, meta, statements}`.
  - calls already retain whole/callee/per-argument `SourceInfo` and positional
    `:arg_labels`; `parse_arg_label/2` recognizes `f(label: value)`.
- `lib/cure/compiler/printer.ex`
  - block printing is at `to_string({:block, ...})`;
  - legacy rewrite printing is at `to_string({:rewrite_expr, ...})`;
  - call and label printing already exist and must be extended, not replaced.
- `lib/cure/elab/elaborator.ex`
  - `elaborate_expr_checked({:rewrite_expr, ...})` is the checked rewrite entry.
  - `eq_parts/2`, `transport_case/4`, `rewrite_plan/6`, `motive_for`, and term
    occurrence/replacement helpers are the existing sound rewrite substrate.
  - `elaborate_expr_checked({:block, ...})` routes to
    `elaborate_let_block/5`.
  - `elaborate_let_block/5` already creates real Core lets via inferred or
    ascribed local bindings; `have` should reuse this path.
  - match elaboration already performs substantial context/index refinement;
    the July 17 living catalog identifies residual E8/E9 cases.
- `lib/std/equivalent.cure` provides canonical kernel-checked `Equivalent`,
  `reflexive`, `sym`, `trans`, and `cong`.
- `lib/cure/elab/overload.ex` already validates declaration-order argument
  labels and overload pruning. It does not reorder labelled arguments.
- `lib/cure/diagnostic/problems.ex` owns `SyntaxProblem`,
  `ExpectationOrigin`, and `TypeProblem`.
- `lib/cure/diagnostic/registry.ex` currently reaches E108 and validates known
  producer ownership/catalog evidence. Before allocating codes, check the tip;
  the intended reservation for this plan is E109-E115.
- `lib/cure/diagnostic/adapter.ex`, renderer modules, registry catalog, and
  `lib/cure/lsp/server.ex` are the current conversion/presentation/editor seams.
- The parked `have` prototype changes only parser/printer behavior. Inspect it
  with `git show 8c42c17d...` or `git stash show`; do not pop it wholesale.

## Stable diagnostic allocation

Unless another committed branch has claimed a code before Task 1, reserve:

| Code | Stable key | Producer variants |
| --- | --- | --- |
| E109 | `proof_chain_syntax` | empty/malformed chain, missing relation/right side/`because`, first-step `_`, unreachable proof statement |
| E110 | `proof_chain_mismatch` | adjacent endpoints disagree, wrong justification, unfinished justification |
| E111 | `rewrite_failed` | no occurrence, ambiguous occurrence, invalid `at`, bad target, reverse-only match |
| E112 | `simplification_failed` | inadmissible rule, supplied proof mismatch, residual goal, resource guard |
| E113 | `induction_failed` | non-inductive subject, case coverage/shape, unavailable hypothesis |
| E114 | `defining_equation_unavailable` | unknown/inaccessible equation or colliding friendly name |
| E115 | `named_argument_mismatch` | unknown, duplicate, misplaced, ambiguous, or missing label |

`have` annotation/body mismatches and dependent branch type disagreements use
contextual E093 with new expectation origins. Automatic congruence has no
standalone error: its miss is owned by E111/E112 at the operation that requested
it.

If a code is no longer free, allocate the next contiguous free code and update
this table, the spec's diagnostic cross-reference, registry tests, and catalog
in the same preliminary commit. Never create two authorities for a code.

## Planned file structure

### New implementation modules

- `lib/cure/elab/proof_goal.ex` — typed proof-goal state, source step identity,
  open/closed result protocol, and checked evidence closure.
- `lib/cure/elab/proof_chain.ex` — `Equivalent` chain elaboration and
  transitivity assembly.
- `lib/cure/elab/rewrite.ex` — extracted reusable rewrite planning,
  occurrence enumeration, direction, and transport builders.
- `lib/cure/elab/equations.ex` — defining-equation descriptors, stable pattern
  keys, environment/export registration, and proof declaration synthesis.
- `lib/cure/elab/simplifier.ex` — terminating oriented rewrite engine plus
  certificate construction and structured trace.
- `lib/cure/elab/induction.ex` — structured induction elaboration and auxiliary
  recursion synthesis where needed.
- `lib/cure/diagnostic/proof_problem.ex` — typed proof-specific semantic
  payloads.
- `lib/cure/diagnostic/adapter/proof.ex` — exhaustive proof-problem conversion;
  the root adapter delegates here and provides no ordinary proof-error fallback.

### Principal modified modules

- `lib/cure/compiler/parser.ex`, `lexer.ex` only if token support is genuinely
  needed, and `printer.ex`.
- `lib/cure/meta_ast/metadata.ex` for recursive metadata projection and source
  ranges on new nodes.
- `lib/cure/elab/elaborator.ex`, `declarations.ex`, `program.ex`, environment
  definition/export structures, resolution, overload handling, totality
  closure, relevance, and erasure traversal only where the new ordinary nodes
  require it.
- diagnostic registry, adapter/family converters, renderers, source registry,
  catalog, and LSP server.
- `lib/std/equivalent.cure` only for a genuinely missing ordinary theorem, never
  for trusted behavior.

### Test families

- Parser/printer/source-span tests per syntax slice.
- `test/cure/elab/proof_have_test.exs`.
- `test/cure/elab/proof_chain_test.exs`.
- `test/cure/elab/proof_justification_test.exs`.
- `test/cure/elab/proof_rewrite_command_test.exs`.
- `test/cure/elab/defining_equations_test.exs`.
- `test/cure/elab/proof_simplifier_test.exs`.
- `test/cure/elab/proof_induction_test.exs`.
- `test/cure/elab/dependent_proof_refinement_test.exs`.
- Extend argument-label, diagnostics, catalog, JSON, LSP, erasure, totality,
  oracle, and Antigen suites rather than duplicating their harnesses.

## Task 0: Refresh the baseline and freeze acceptance fixtures

**Purpose:** prevent implementation from being judged only by the final LIA
proof and ensure later diagnostics preserve the merged contextual information.

- [x] Confirm the worktree is clean and the two stash object IDs still resolve.
- [x] Check whether `elaborator-gaps` advanced beyond `9b97ebbb`; merge only a
  clean committed tip and repeat focused/full verification if it did.
- [x] Record the current parser AST, formatted output, elaboration verdict, Core
  hash, erased form, and diagnostic payload for representative explicit proofs:
  nested `trans`, `sym`, legacy `rewrite ... in ...`, congruence under a
  function, hand-written defining equations, and recursive match proofs.
- [x] Add rejected fixtures for every E109-E115 producer variant to a planning
  manifest. They may be marked pending until their task, but each must name the
  eventual public catalog case and exact expected primary/secondary ranges.
- [x] Add one small explicit proof used by every later equivalence test, proving
  that new syntax changes source authoring but not kernel verdict or erasure.

**Verification:** focused parser, rewrite, contextual diagnostic, registry, and
LSP suites; then `mix test` if the baseline merge changed.

**Commit:** `test(proofs): freeze proof-language acceptance baseline`

## Task 1: Land `have` as checked local evidence

**Purpose:** establish the smallest proof statement and reuse the real Core-let
path before introducing goal-transforming blocks.

- [x] Write parser failures/successes for inferred and annotated `have`, nested
  blocks, shadowing, use after binding, and ordinary identifiers named `have` in
  non-distinctive positions.
- [x] Inspect prototype object `8c42c17d...`; manually port only its useful
  parser/printer shape. Do not apply the stash.
- [x] Parse `have` contextually into the existing assignment node with
  `let: true, have: true`, preserving whole/name/annotation/body ranges.
- [x] Print canonical `have`; add metadata traversal, quote/syntax-builder, and
  macro hygiene coverage for the metadata flag.
- [x] Route it through `elaborate_let_block/5` and real Core `:let`. Prove the
  RHS is evaluated/bound once, dependent annotations remain transparent, and
  relevance/erasure are unchanged.
- [x] Add `ExpectationOrigin.kind = :local_fact` so
  an annotation mismatch is contextual E093 naming the fact rather than a
  generic body mismatch.
- [x] Add completion, semantic token, and formatting tests.

**Red gate:** parser does not recognize `have`; the canonical proof fixture
rejects.

**Green gate:** focused parser/printer/elab/diagnostic/LSP tests, canonical
stdlib compilation, full suite, complete Antigen.

**Commit:** `feat(proofs): add checked local facts with have`

**Completed evidence (2026-07-21):** 51 focused tests green; canonical 122-module
stdlib compile green; warnings-as-errors compile green; complete Antigen
318/318 green; full suite 5,288 tests, 0 failures, 6 excluded. The repository-wide
format check remains blocked only by pre-existing formatting drift in unrelated
files; every Task 1 file is formatted.

## Task 2: Implement inline `proof chain ... because ...`

**Purpose:** replace nested `trans` terms while keeping each step independently
typed and diagnosed.

- [x] Add source AST nodes with complete ranges:
  - `{:proof_chain, meta, [first | steps]}`;
  - `{:proof_step, meta, [left_marker, right, justification]}`;
  - distinguish the first expression from continuation `_` without creating a
    hole/metavariable.
- [x] In `parse_prefix/1`, recognize `proof chain` only when `proof` is followed
  by identifier `chain` and a valid block boundary. Preserve the existing proof
  container and ordinary identifier behavior elsewhere.
- [x] Parse steps with a dedicated `==` consumer so global non-associative
  operator behavior remains unchanged. Require `because`; recover at the next
  equally-indented relation/step.
- [x] Add canonical printer layout and parse-print-parse equality tests.
- [x] Implement `Cure.Elab.ProofChain`: infer the carrier and first endpoint,
  check each right endpoint at the carrier, check each inline justification at
  `Equivalent(carrier, left, right)`, and compose with the certified
  `Std.Equivalent#trans` definition.
- [x] Kernel-check the completed chain against both its synthesized proposition
  and any enclosing expected type. No special Core node survives elaboration.
- [x] Add E109 and E110 registry entries, typed payloads, adapters, prose,
  source labels, catalog programs, ANSI/plain/JSON/LSP snapshots, and coverage.
  Chain mismatches must point to adjacent source steps, not generated `trans`.
- [x] Add tests for empty chain, missing pieces, first `_`, wrong carrier,
  endpoint mismatch, wrong proof, two/three/fifty steps, and nested expression
  use.

**Red gate:** valid chain is a syntax rejection; each negative fixture either
falls to E094 or lacks the required ranges.

**Green gate:** new focused suites, registry validation/catalog coverage,
canonical stdlib, full suite, complete Antigen.

**Commit:** `feat(proofs): add typed equational proof chains`

**Completed evidence (2026-07-21):** dedicated AST/source roles and canonical
round-trip formatting are green; one-, two-, three-, and fifty-step chains
kernel-check and erase without a chain Core node; all inline E109 variants and
E110 carrier/justification variants project through ANSI, plain, JSON, and LSP.
Focused suites and warnings-as-errors are green, the canonical 122-module stdlib
compiles, complete Antigen is 318/318, and the full suite is 5,303 tests with 0
failures and 6 excluded.

## Task 3: Add typed multiline `because` blocks

**Purpose:** create the shared, compositional proof-command substrate without
inventing a runtime or untyped tactic interpreter.

- [x] Add `{:proof_justification, meta, statements}` for indented `because`
  bodies while retaining inline proof expressions.
- [x] Implement `%Cure.Elab.ProofGoal{expected, names, context, env, source,
  status, builders, trace}` and a command result protocol:
  `{:open, goal}` or `{:closed, core_evidence, trace}`.
- [x] Initially support only `have` and a final ordinary proof expression in a
  block. This validates scope/closure before rewrite and simplify commands.
- [x] Reject end-of-block with an open goal and any statement after closure.
- [x] Ensure local facts extend an elaboration context and lower to nested Core
  lets around the final evidence; never substitute/evaluate commands at runtime.
- [x] Complete E109/E110 producer variants for unfinished and unreachable blocks
  with residual surface goal and fact inventory.
- [x] Add nested-block, shadowing, closure, source-range, formatter, JSON, LSP,
  and erased-output identity tests.

**Green gate:** focused proof-block and diagnostic suites, registry/catalog
coverage, canonical stdlib, full suite, complete Antigen.

**Commit:** `feat(proofs): add compositional because blocks`

**Completed evidence (2026-07-21):** multiline blocks retain complete authored
ranges and canonical formatting; `have` commands extend lexical scope and lower
to kernel-checked nested Core lets; nested blocks, shadowing, open-goal fact
inventory, and post-closure rejection are covered. E109/E110 retain residual
goals and project through JSON/LSP. Administrative identity lets erase without
duplicating evaluation, making block and inline evidence emitted-form identical.
Focused suites and warnings-as-errors are green, the canonical 122-module stdlib
compiles, complete Antigen is 318/318, and the full suite is 5,313 tests with 0
failures and 6 excluded.

## Task 4: Extract rewrite infrastructure and add directed proof commands

**Purpose:** support `rewrite using`, `rewrite backwards using`, `in name`, and
`at n` while preserving legacy expression rewrite.

- [x] Move `eq_parts`, motive construction, occurrence matching, symmetry, and
  transport assembly from private elaborator helpers into
  `Cure.Elab.Rewrite`. First pin legacy `rewrite p in body` Core/verdict tests;
  extraction must be behavior-identical.
- [x] Represent rewrite occurrences with normalized term, authored/source path,
  traversal path, and stable left-to-right display number. Enumeration must not
  depend on map order or Core pretty-print order.
- [x] Parse proof-block commands:
  - `rewrite using proof`;
  - `rewrite backwards using proof`;
  - either form followed by `at positive_integer`;
  - either form followed by `in local_name`.
- [x] A unique occurrence transforms the goal and records a transport builder;
  zero/many return E111. Never choose the first match silently.
- [x] Generate congruence automatically by abstracting the matched subterm into
  the rewrite motive. Cover nested unary/binary/function/constructor arguments
  and dependent occurrences; reject contexts for which a sound motive cannot be
  synthesized.
- [x] Rewriting `in hypothesis` creates a new checked local proof binding for the
  remainder of the block and preserves the immutable source binding.
- [x] Add reverse-only detection and a machine edit inserting `backwards`.
  Ambiguity supplies one edit per `at n` candidate.
- [x] Add E111 completely to registry/catalog/renderers/JSON/LSP and prove all
  primary spans are authored proof-command spans.

**Red gate:** command syntax rejects; legacy rewrite baseline remains green.

**Green gate:** all rewrite/congruence, legacy rewrite, diagnostic/editor,
stdlib, full-suite, and Antigen gates.

**Commit:** `feat(proofs): add directed goal rewriting`

**Completed evidence (2026-07-21):** legacy expression-rewrite verdicts and
baseline Core hashes remain unchanged after extraction into `Cure.Elab.Rewrite`;
forward, backward, selected, nested-application, binder-aware, and local-
hypothesis rewrites kernel-check through ordinary `Equivalent` elimination.
E111's five planned variants project through plain, ANSI, JSON, and LSP, with
machine edits for direction and every numbered ambiguity candidate.
The canonical 122-module stdlib compiles, all changed files are formatted,
the full suite is 5,321 tests with 0 failures and 6 excluded, 147 expected
immune responses fire, and complete Antigen coverage is 318/318.

## Task 5: Generate certified defining equations

**Purpose:** eliminate handwritten `dot_empty`, `dot_cons`, and nested-match
equation boilerplate while making equations discoverable and stable.

- [x] Define an equation descriptor containing owner key, complete constructor
  path, structural pattern key, telescope, left/right surface/Core terms,
  visibility, definition span, and provenance.
- [x] Capture complete decision-tree paths from function clauses and nested
  matches without using traversal ordinals as public identity.
- [x] Generate equations only after the owner body is installed and totality
  certified, so open-term reflexivity may use its certified delta rule. Build
  each as an ordinary `Equivalent` definition and kernel-check it.
- [x] Register descriptors in the elaboration environment and exported module
  interface. Public/private visibility follows the owner.
- [x] Resolve unique friendly members (`dot.Empty`, `dot.NonEmpty`, nested
  constructor paths). For short-name collisions, omit the ambiguous alias and
  retain selectable structural pattern keys; do not reject the function or add
  `eq_1` suffixes.
- [x] Ensure generated theorem definitions participate in totality closure,
  relevance, erasure, incremental interface hashes, imports, qualification,
  docs/reflection policy, and no runtime emission unless ordinarily reachable
  at a present grade.
- [x] Add E114 for unavailable/inaccessible/colliding friendly equation names,
  including defining-clause related information.
- [x] Add member completion after `function.`, hover proposition, go-to-definition
  provenance, and cross-module tests.
- [x] Cover flat clauses, nested matches, multiple arguments, impossible paths,
  private owners, guarded collisions, recompilation stability, and forged
  equation rejection.

**Green gate:** equation, incremental/export, diagnostic/LSP, stdlib, full-suite,
oracle, and complete Antigen gates.

**Completed evidence (2026-07-21):** defining equations are extracted from
certified decision trees after totality closure and installed as ordinary
kernel-checked definitions. The registry preserves complete structural paths,
source propositions and spans, visibility, import/export identity, and stable
interface hashes; ambiguous short names fail with E114 while exact nested paths
remain selectable. Dependent, sequential, polymorphic, and type-valued results
are covered (the latter by the predicative `TypeEquivalent` family), as are
impossible indexed branches and guarded same-constructor clauses. A trace over
all 122 canonical stdlib modules found zero rejected generated definitions;
oracle replay and the focused equation/diagnostic/LSP gates pass. Final suite
and Antigen gates pass: 5,336 tests with 0 failures and 6 excluded, 144
expected immune responses, diagnostic coverage 58/58, and complete Antigen
coverage 318/318.

**Commit:** `feat(proofs): expose certified defining equations`

## Task 6: Implement the terminating proof-producing simplifier

**Purpose:** solve routine definitional/equational goals without trusting a host
decision or silently unfolding arbitrary recursion.

- [x] Define rule admission and orientation. Version 1 rules are generated
  defining equations, an audited finite standard set, and explicit local proofs.
  Orient by a documented well-founded term measure; reject non-decreasing or
  ambiguous rules.
- [x] Implement deterministic traversal/order, visited-state cycle protection,
  and explicit resource bounds. A resource guard is E112, not a false theorem.
- [x] At each rewrite, construct equality evidence through
  `Cure.Elab.Rewrite`; compose the trace with `trans`. Definitional beta/iota/
  zeta/certified-delta normalization may close with `reflexive`, but the kernel
  still checks convertibility.
- [x] Parse `simplify` and `simplify using [rule, ...]` only inside a
  justification block in version 1.
- [x] A solved goal closes the block. A residual goal reports before/after
  surface propositions, rules that progressed, and structured trace IDs.
- [x] Add opt-in trace rendering without changing the compact default message.
- [x] Add contextual LSP completion and hover for `simplify`, explicit local
  rules, generated defining equations, and the audited default rule set. Hover
  must distinguish function-equation members such as `map.Cons` from modules
  and show their certified propositions and provenance.
- [x] Add E112 registry/catalog/adapter/renderers/JSON/LSP coverage.
- [x] Add termination regressions for symmetric equations, recursive equations,
  mutually cycling explicit rules, duplicate rules, and large terms; add forged
  rule and certificate rejection tests.

**Green gate:** simplifier unit/certificate tests, kernel rejection negatives,
diagnostics, stdlib, full suite, complete Antigen, and an explicit time/step
ceiling regression.

**Completed evidence (2026-07-21):** the audited beta/iota/zeta/certified-delta
set and certified generated equations are deterministic defaults; explicit
rules require a strict Core-node decrease, while generated rules revalidate
their totality certificate and kernel definition before admission. Traversal is
left-to-right in user-list order with visited-state protection and a 256-step
ceiling. Every rewrite builds ordinary equality transport through
`Cure.Elab.Rewrite`, the enclosing chain composes checked evidence, and final
conversion closes only with kernel-checked reflexivity. E112 carries authored
before/after propositions and structured trace IDs through terminal, JSON, and
LSP, with expanded traces opt-in. Completion and hover cover the command, local
equality rules, and generated function equations while explicitly
distinguishing `map.Cons`-style members from modules. Compact chains are now the
formatter default while the expanded legacy layout remains parse-compatible.
The 122-module stdlib and 5,352-test full suite pass with 0 failures and 6
excluded; diagnostic coverage is 59/59, 136 expected immune responses fire,
and complete Antigen coverage is 318/318.

**Commit:** `feat(proofs): add proof-producing simplification`

## Task 7: Adapt near-matching proofs with `simplify using`

**Purpose:** cover the former `simpa using` use case without adding a second
simplification language.

- [x] Parse bare `simplify using proof_expression` distinctly from bracketed
  additional-rule syntax.
- [x] Infer the supplied proof's `Equivalent` proposition; simplify both it and
  the current goal with the same admitted rules and deterministic configuration.
- [x] If normalized propositions agree, bridge the supplied proof to the goal
  with the recorded simplification evidence and close the block.
- [x] If they do not, emit E112 with supplied/original/simplified propositions
  and trace IDs; never degrade to a final E093 on an internal bridge term.
- [x] Cover reverse endpoints, local facts, generated equations, no-progress,
  wrong carrier, non-equality evidence, and nested chains.

**Green gate:** focused proof adaptation plus all Task 6 gates.

**Completed evidence (2026-07-21):** parser metadata distinguishes bare proof
adaptation from bracketed rule lists without name-based guessing. The elaborator
infers ordinary local/global equality evidence or specializes a certified
generated equation against the authored goal, normalizes supplied and required
propositions under the same audited defaults, and kernel-checks either the
direct evidence or an explicit symmetry bridge. E112 retains supplied,
simplified-supplied, original, and simplified-goal representations and never
leaks an internal E093. Focused coverage includes direct and reverse endpoints,
local facts, nested chains, generated equations, mismatches, wrong carriers,
and non-equality evidence; LSP completion covers both bare proof and bracketed
rule contexts. The 122-module stdlib and 5,358-test full suite pass with 0
failures and 6 excluded; diagnostic coverage is 59/59, 151 expected immune
responses fire, and complete Antigen coverage is 318/318.

**Commit:** `feat(proofs): simplify existing evidence into goals`

## Task 8: Implement structured induction

**Purpose:** introduce constructor-shaped cases and specialized induction
hypotheses while retaining ordinary totality checking.

- [x] Before coding, pin two elaboration strategies with probes:
  1. induction over an enclosing function parameter lowered to recursive calls
     to the current definition; and
  2. induction over a local/arbitrary expression lowered through a private,
     closure-lifted auxiliary definition.
  Choose the smallest generic representation that supports both and is visible
  to totality; do not fake local recursion with a runtime fixpoint.
- [x] Parse `induction subject` plus constructor-shaped `case` arms into a
  distinct AST retaining subject, case, pattern-field, and body ranges.
- [x] Resolve the subject datatype and constructor telescopes. Bind ordinary
  fields followed by one specialized induction hypothesis for each structurally
  recursive field, in deterministic constructor-field order.
- [x] Reuse ordinary match motive/context refinement and coverage. Impossible
  and omitted cases follow existing coverage semantics.
- [x] Generate Core case/recursive evidence and submit the enclosing or lifted
  definition to ordinary totality closure. Add erasure/codegen tests proving no
  tactic structure remains.
- [x] Add E113 with constructor declaration related information and typed
  payloads for non-inductive subjects, missing/duplicate/unknown/impossible
  cases, field-shape errors, and unavailable/mistyped hypotheses.
- [x] Add LSP complete-case code actions with descriptive editable names,
  semantic tokens, hover, and formatting.
- [x] Cover Nat, canonical Int, multi-recursive constructors, indexed evidence,
  nested induction, local subject lifting, totality rejection, and oracle parity.

**Green gate:** induction/totality/coverage/diagnostic/LSP suites, canonical
stdlib, full suite, complete Antigen including recursion/termination antibodies.

**Commit:** `feat(proofs): add structured induction`

**Completed evidence (2026-07-21):** direct-recursion and closure-lift probes,
Nat, canonical Int, multi-recursive Tree, indexed impossible evidence, nested
and local induction, totality rejection, runtime erasure, E113, formatter, hover,
completion, and complete-case code-action coverage are green. The combined
focused and oracle gate passes 165 tests; compiler/meta-AST coverage passes
1,147 tests; the canonical 122-module stdlib and warnings-as-errors compilation
pass; diagnostic coverage is 60/60; complete Antigen is 318/318; and the full
suite passes 5,385 tests with 0 failures and 6 excluded (164 expected immune
responses).

## Task 9: Close dependent-pattern refinement gaps required by proofs

**Purpose:** make constructor-implied index information available without
defensive rematching or explicit proof-only carries.

- [x] Restore only the smallest LIA semantic proof fixture needed to expose the
  current dependent `AddedCons` friction, or build an equivalent isolated probe.
- [x] Use `Cure.Dev.Trace` first. Classify each failure against the July 17
  catalog: already-fixed whole-context substitution, residual sequential-match
  composition (E8), or missing residual index evidence (E9).
- [x] Add red tests for branch context values/types, sibling shapes, existential
  names, sequential matches, impossible pruning, and residual stuck equations.
- [x] Extend branch substitution to the whole accumulated context and coverage
  consumer where missing. Retain non-definitional residual equations as local
  `Equivalent` evidence with honest provenance.
- [x] Prefer elaborator changes. If a kernel change is genuinely required, stop
  this task for the dedicated TCB review and add wrong-body, conversion,
  termination, and Antigen antibodies before implementation.
- [x] Surface ordinary mismatches as contextual E093 with a new dependent-branch
  origin; do not expose motives/de Bruijn indices in primary prose.
- [x] Prove existing match verdicts, Core, erasure, and coverage remain unchanged
  outside newly accepted completeness cases.

**Green gate:** dependent match/elab/core/coverage tests, wrong-proof negatives,
Idris oracle, full suite, complete Antigen.

**Commit:** `feat(elab): propagate dependent proof refinements`

**Completed evidence (2026-07-21):** `Cure.Dev.Trace` classified the isolated
`AddedCons` probe before implementation audit. Seven dedicated dependent-proof
tests cover sequential composition, whole-context sibling and existential
refinement, impossible pruning, stuck computed indices, false reconstruction,
and contextual dependent-branch E093 output in plain, JSON, and LSP forms.
Existing carried-index, rewrite-as-case, coverage, wrong-family, and Idris-oracle
controls remain green; no Core or kernel rule changed. The combined dependent,
match, diagnostic, and oracle gates pass, warnings-as-errors compilation passes,
complete Antigen is 318/318, and the full suite passes 5,392 tests with 0
failures and 6 excluded (138 expected immune responses).

## Task 10: Upgrade argument labels into reorderable named arguments

**Purpose:** finish item 10 by extending, not replacing, Cure's existing
declaration-order label system.

- [x] Amend the older overloading/argument-label design to state that the July
  21 proof-language design supersedes its “no reordering” v1 non-goal.
- [x] Extend call metadata so each argument retains label plus its own range;
  preserve the all-positional historical AST shape.
- [x] Resolve labels against the chosen declaration's present parameter
  telescope, then reorder surface arguments into telescope order before
  bidirectional implicit/dependent solving. Lock the general mixing rule:
  positional arguments must precede every named argument and fill the leftmost
  present parameters in declaration order; following named arguments may appear
  in any order and fill the remaining parameters. Reject every
  positional-after-named call.
- [x] Ensure overload pruning considers label sets independent of source order,
  while types are checked only after arguments are aligned to each candidate.
- [x] Reject unknown, duplicate, missing-required, misplaced, and
  overload-ambiguous labels with E115. Retain declaration and per-argument
  ranges, implicitness, and candidate owners.
- [x] Update printer stability, formatter, signature help, inlay hints, and code
  actions. Named arguments remain a general language facility, not proof-only.
- [x] Cover dependent telescopes where a later-written named argument determines
  an earlier implicit, typeclasses/dictionaries, overloads, partial application,
  runtime arity, erasure, macros/reflection, and constructor-call disambiguation.

**Green gate:** argument-label/overload/call diagnostics/LSP, stdlib, full suite,
complete Antigen.

**Commit:** `feat(language): support reorderable named arguments`

**Completed evidence (2026-07-21):** call metadata retains an aligned label and
label-range vector while all-positional calls preserve their historical AST.
Every ordinary, overloaded, constructor, interface-method, constrained, checked,
partial, and piped call path aligns authored arguments against its present
telescope before Core construction; overload candidates are aligned and checked
independently. E115 covers positional-after-named, unknown, duplicate, missing,
and ambiguous labels with authored primary ranges, declaration secondaries, and
safe edits. Completion, label hover, reordered signature help, inlay hints, and
generic code actions share the same source metadata. Dedicated tests prove
dependent implicit solving, dictionary insertion, constructor disambiguation,
overload order independence, reflection hygiene, formatter stability, and exact
Core/erasure equivalence with positional calls. No trusted Core module changed;
frontend-only declaration ranges do not enter `Cure.Core.Env`, artifact hashes,
or emitted forms. Changed-file formatting and warnings-as-errors compilation
pass, the canonical 122-module stdlib compiles, diagnostic coverage is 61/61,
complete Antigen is 318/318, and the full suite passes 5,413 tests with 0
failures and 6 excluded (135 expected immune responses). A first loaded run had
one 8-second prelude-scan timeout; the isolated test passed 1/1 and the clean
full rerun above passed unchanged.

## Task 11: Restore and finish verified-LIA Task 4 using the new language

**Purpose:** use a real difficult proof as the integrated acceptance test rather
than shipping isolated toy ergonomics.

- [x] Restore the content of stash object `ae07ebface...` after confirming its
  exact object identity and paths; retain the stash object itself for recovery.
- [x] Reconcile it with the final `proof_int_order.cure`,
  `proof_linear_arithmetic.cure`, and semantic module layout without discarding
  completed coefficient-distributivity work.
- [x] Rewrite the affine homomorphism proofs to use:
  - `have` for head/tail facts;
  - `proof chain` for equality composition;
  - directed rewrite inside `because` blocks;
  - generated equations for dot/add/scale cases;
  - `simplify`/`simplify using` for definitional rearrangements;
  - structured induction over alignment/fold evidence;
  - automatic dependent refinement in `AddedCons`; and
  - named theorem arguments where calls remain long.
- [x] Complete dot addition/scaling semantics, atom combination preservation,
  fold preservation, shape evidence, Boolean inversion, and every remaining
  Task 4 gate in the verified-LIA ledger. Do not stop at syntax conversion.
- [x] Compare old explicit and new proof sizes/structure. Record source line and
  explicit combinator reductions without claiming mathematical complexity was
  removed.
- [x] Run paired Cure/Idris `rel=same` fixtures and wrong-proof/forged-certificate
  negatives.
- [x] Update the verified-LIA plan ledger and proof ergonomics spec status with
  the exact completed acceptance evidence.

**Green gate:** canonical stdlib fresh compile, LIA runtime tests, Cure/Idris
oracle, offline replay, proof diagnostics, full suite, complete Antigen.

**Commit:** `feat(std): prove affine semantics with readable evidence`

**Completed evidence (2026-07-21):** the parked LIA content was identified by
the exact `ae07ebface...` object (the integer-order file matches byte-for-byte;
the arithmetic file is retained and extended with the public equations and
checked semantic substrate). The new semantic module is 267 lines and uses 45
readable proof-language constructs; the restored explicit arithmetic source is
194 lines versus 189 lines in the parked snapshot. This is a source-structure
tradeoff, not a claim that the mathematics became simpler: the six quantified
homomorphism/fold obligations are now explicit and kernel-checked. Fresh
stdlib compilation, 43 focused proof/induction/LIA tests, OTP oracle replay
(`linear_arithmetic_semantics` and `_wrong` both `rel=same`), complete Antigen
(318/318), and the full suite (5,417 tests, 0 failures, 6 excluded) pass.

## Task 12: Final integration, catalog, documentation, and audit

- [x] Run a producer inventory and raw-error scan. No new proof path may emit a
  bare tuple/string, generic E094/E093 fallback, generated primary blame, or
  unregistered producer.
- [x] Run `mix cure.diagnostics --color=always --width=80 --coverage` and the
  color-free catalog. Require 100% reachable-code and producer-branch coverage.
- [x] Verify every new diagnostic in terminal, plain, JSON, UTF-8/16 LSP, and
  code-action projections.
- [x] Verify formatter idempotence and parse-print-parse for every construct.
- [x] Verify removing source diagnostic metadata does not alter verdict, Core,
  erasure, hygiene, hashes, or emitted forms.
- [x] Verify no proof AST node or command appears in emitted Erlang/BEAM forms.
- [x] Run formatting, warnings-as-errors compile, focused parser/elab/core/LSP/
  diagnostics suites, canonical stdlib compile, oracle replay, `mix antigen
  complete`, and full `mix test`.
- [x] Update `docs/LANGUAGE_SPEC.md`, proof authoring examples, generated-equation
  discovery docs, error catalog documentation, and the July 17 living catalog.
- [x] Mark the proof-language spec implemented only when all twelve acceptance
  criteria and the restored LIA workload are green.

**Commit:** `docs(proofs): complete proof-language ergonomics rollout`

**Completed evidence (2026-07-21):** producer inventory confirms E109–E115 are
registry-owned and the raw-error scan found no new bare proof-path diagnostic.
The colored and color-free catalogs pass with registered diagnostic coverage
61/61. Formatter, metadata-invariance, Core/erasure, codegen, LSP, and
negative-path tests are covered by the focused suites and the full suite.
Changed-file formatting, warnings-as-errors compilation, fresh 124-module
stdlib compilation, OTP oracle replay, complete Antigen (318/318), and the
serial full suite (5,417 tests, 0 failures, 6 excluded) are green. The public
language spec now documents proof commands, generated-equation discovery,
named arguments, and E109–E115 diagnostics.

## Per-task verification template

Use the smallest relevant set first, then the task's stated full gate:

```sh
mix format --check-formatted
MIX_ENV=test mix compile --warnings-as-errors
mix test test/cure/compiler/*proof* test/cure/compiler/*parser* test/cure/compiler/*printer*
mix test test/cure/elab/*proof* test/cure/elab/*rewrite* test/cure/elab/*match*
mix test test/cure/diagnostic_test.exs test/cure/diagnostic test/cure/compiler/contextual_type_diagnostic_test.exs
mix test test/cure/lsp*
mix antigen complete
mix cure.diagnostics --color=always --width=80 --coverage
NO_COLOR=1 mix cure.diagnostics --color=auto --width=80
mix test
```

Shell globs must be narrowed to files that exist at that task. Do not run
multiple `mix` commands concurrently.

## Completion definition

The plan is complete only when:

- all ten locked features work together through ordinary Cure compilation;
- every produced proof is independently kernel-checked and no trusted primitive
  was added;
- every deliberate rejection has rich structured diagnostics and public-path
  catalog coverage;
- generated equations are stable, certified, visible, and discoverable;
- simplification and induction terminate under explicit checked policies;
- dependent constructor evidence removes the LIA defensive-rematching tax;
- named arguments work with dependent and overloaded calls;
- the parked LIA semantic/fold proofs are complete and readable;
- Cure/Idris relations, totality, erasure, full tests, and complete Antigen are
  green; and
- the worktree is clean with one descriptive commit per phase.
