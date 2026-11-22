# Lean 4 Parity — Status Scorecard

Updated 2026-11-21 against the implementation and executable proof suites.
**Authoritative scope and phases:** [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md), §8.
**Proof-language reference:** [`PROOFS.md`](PROOFS.md).
**Source corpus:** [`test/lean4_parity/`](../test/lean4_parity/), run with
`mix test test/lean4_parity_test.exs`.

## Phase status

- **Phase 1 — C4, C5, C8: implemented.** Explicit simp admission, certified
  unfolding, and deterministic opt-in rewrite-all have positive and refusal
  tests. No kernel rules or Agda files changed.
- **Phase 2 — C1.1, C1.3: implemented.** Existing justification commands use
  the checked goal API; tactic combinators retain evidence. Search, positivity,
  and decision commands have positive and negative corpora.
- **Phase 3 — C3:** not audited for completion in this change. Parser support
  alone does not establish declaration-driven transitive fixity completion.
- **Phase 3 — C1.2: implemented.** A `tactic` macro rule kind lets a LIBRARY
  (not the stdlib) define a new proof command. The expansion is checked against
  a closed tactic vocabulary, so a tactic can only produce goals and apply
  existing steps — never a Core term. See "C1.2 — user tactic macros" below.
- **Phase 4 — C1.2, C6, C7:** incomplete. Premise-generating backward `apply`
  and per-command editor/REPL goal views remain. `exact` and closing `apply`
  already work, and user-defined goal tactic macros now exist (Phase 3).
- **Phase 5 — C2:** not changed; execute the existing universe design.
- **Phase 6 — C9, C10:** not changed; follow the kernel reach ledger.

The phase numbers in `PATH_TO_LEAN4_PLAN.md` and `LEAN4_MIGRATION_PLAN.md`
were different. Those documents are historical, not alternative current gates.

## Implemented gates and evidence

### C4 — ambient simplification

`@simp` and `@lemma(:simp)` use Cure's existing decorator grammar. Lean's
`@[simp]` spelling is not added. Explicit declarations are rejected with E112
unless equality endpoints strictly decrease in Core size without introducing
or duplicating quantified variables. Binder-containing endpoints are
conservatively refused. A common substitution-stable ordering prevents loops
across imported sets; it is not a heuristic claim that every useful theorem
can be oriented.

Certified quantified rules specialize to checked evidence and run to a bounded
fixed point. Safe legacy `@lemma` equations remain ambient. Imported metadata,
forged/uncertified refusal, nested induction-lemma rewriting, and declaration
source spans are pinned in `test/cure/elab/simp_set_test.exs` and
`test/cure/diagnostic/simp_declaration_test.exs`.

### C5 — certified computation

The audited default set remains beta, iota, zeta, and certified delta.
`Simplifier` already reached the existing certified normalization machinery;
this change does not add another unfolding implementation. Nested recursive
computation closes; removing the recursive function's certificate leaves a
residual goal. See `test/cure/elab/tactic_integration_test.exs`.

**Audit correction:** `plus(n, Z()) = n` with neutral `n` is an induction
theorem in Lean too, not a missing recursive-unfolding case. That rejection
remains a deliberate corpus pin. `plus(Z(), plus(Z(), n)) = n` is the actual
computational positive witness.

### C8 — rewrite-all

`rewrite using h all` and its backwards form visit occurrences in the original
normalized target, in deterministic left-to-right order. Each replacement
builds an ordinary checked equality transport, composed back to the original
goal. Replacement-introduced occurrences are not revisited. The default remains
single-occurrence and ambiguous matches still report E111.

Evidence: `test/cure/elab/proof_ergonomics_test.exs`,
`test/cure/elab/tactic_integration_test.exs`, and the existing rewrite suites.

### C1.1 — goal API

`ProofGoal.new/5` preserves the original target/context and assigns an identity;
`inspect_goal/1` exposes the current target and hypotheses. There is no second,
incompatible goal struct. Existing `have`, chain/justification evidence,
simplify, rewrite, and induction commands pass through `Tactic.command/1`.

`Tactic.Result` retains remaining goals and checked solutions keyed by original
goal identity. Sequence, choice, focus, all-goals and bounded repeat-until-fail
preserve those solutions. Legacy goal-list projections are only scheduling or
inspection data; discarding proof terms is not a soundness boundary.

The existing proof-language and E109–E115 diagnostic suites remain the
compatibility gates. Direct evidence reconstruction and combinator behavior
are pinned in `test/cure/elab/tactic_integration_test.exs` and `tactic_test.exs`.

### C1.3 — checked solvers

- `by search`: local evidence, checked projections, tagged lemmas; ambiguity
  remains an error rather than arbitrary witness selection.
- `by positivity`: the curated natural-number `IsPositive` fragment, including
  successors, addition, multiplication and sign hypotheses. It is not generic
  lemma search and refuses zero/unknown signs/unrelated propositions.
- `by decide`: infer the certified Boolean-equality decider.
  `by decide using expression`: accept an explicit `Decision(P)`, normalize
  only through certified Core, extract actual `Yes` evidence, and check it at
  the unchanged original goal. `No`, stuck decisions and host Booleans refuse.

Commands work in inline/block justifications and checked non-equality function
bodies. Evidence: `test/cure/compiler/solver_test.exs` and
`test/cure/elab/solver_test.exs`.

### C1.2 — user tactic macros

A `tactic` member of the `macro` container lets a LIBRARY define a new proof
command. The gate is a test library, not the stdlib: `test/cure/elab/tactic_macro_test.exs`
defines tactics in its fixtures and closes real goals with them.

The safety argument is structural, not disciplinary. A rule's expansion is
classified against a closed vocabulary (`Cure.Elab.Tactic.Step`) — `simplify`,
`rewrite`, `exact`/`apply`, `by decide`/`search`/`positivity`, `induction`, and
`have` — before it can be used. A Core term, a bare proof expression, a lambda,
a `match`, or an empty body is `E092` at the rule, so a tactic can only produce
goals and apply existing steps. Composition is `seq` only: `or_else`/`try_`
would swallow failures, `repeat` would make step counts depend on a progress
heuristic, and `focus`/`all_goals` are vacuous while every command is
single-goal.

A tactic keyword is CONTEXTUAL, exactly like `apply`/`exact`: it names a command
only in command position (a `because` block or an `induction` case body) and is
an ordinary identifier everywhere else, so a library may still define and call
`fn close(x)`. A tactic that leaves the goal open is an unfinished justification
naming the residual goal, never a silent success. `tactic` rules carry the §9
self-proving obligations unchanged (`example` pins, `explain` exhaustiveness).

No new Core constructor, kernel rule, postulate, or bypass. Every step is
`Tactic.command/1`, which re-checks its evidence at the ORIGINAL goal.

## Corpus and historical G-register

The corpus uses historical G1–G11 identifiers, not the C-register or the gap
numbers in the even older readiness audit. Retain stable IDs rather than
silently reassign their meaning.

- **G1 / C7:** diagnostic and hole introspection exist; complete cursor-position
  goal tooling is still open. Unfinished proofs and holes must still refuse
  compilation.
- **G2 / C1:** goal execution/composition and user tactic macros landed. A
  `tactic` macro rule may only compose EXISTING commands; it cannot emit a Core
  term or a bare expression, and its keyword stays an ordinary identifier
  outside command position. What remains open is not the rule kind but the
  vocabulary it composes over (C6's premise-generating `apply`).
- **G3 / C5,C9:** certified computation verified; guarded-recursion ledger not
  changed. The neutral right-identity rejection is not itself a parity gap.
- **G4 / C4:** explicit simp admission and quantified ambient rules implemented.
- **G5 / C1.3:** explicit solver entry points implemented in their stated
  fragments. The separate `decide_is_true` library-call pin remains rejected;
  do not generalize that one reach issue to all dependent decisions.
- **G9 / C2:** universe work not changed. Surface binders alone are not proof of
  arbitrary-level kernel polymorphism.
- **G10:** simp-set debugging is not implemented; an explicit-rule positive pin
  is not evidence that a debugging command exists.
- **G6, G7, G8, G11:** proof/runtime correspondence obligations, not source
  capability pins. They remain outside this phase and have no corpus entries.

The corpus includes the adoption baseline plus explicit Phase 1/2/3 gates for
certified recursive computation, quantified simp, looping-rule refusal,
multi-occurrence transport, solver acceptance/refusal, and a library-defined
tactic that closes a real goal (with its Core-term refusal): **24 cases, 16
accept and 8 reject**, measured from `Corpus.all/0`. Rejection counts include
deliberate safety boundaries, not just unfinished features.

Final focused integration: **96 tests, zero failures**. Documentation checker:
**357 snippets, zero failures**. `mix quality.ci`, `mix dialyzer`, and
`git diff --check` pass; the existing Dialyzer ignore inventory is unchanged.
The broad proof/compiler/diagnostic/REPL regression run passes **3,910 tests,
zero failures, two excluded**. The final frozen-snapshot standard `mix test`
passes **7,060 tests, zero failures, eight excluded**, followed by **357
documentation snippets, zero failures** (seed 200312).
The separate `mix check` regression task also passes: **69 stdlib checks and
40 examples**, with no failures or skipped examples.

Validation also exposed two unrelated test-isolation defects: REPL editor
tests inherited `VISUAL`, bypassing their `EDITOR` stubs, and an async kernel
budget test sampled VM-global reductions. The tests now isolate the editor
environment and sample process-local reductions respectively; the kernel and
the 250,000-reduction budget are unchanged.

Earlier measurements of 238 Agda modules, two postulates and zero bypasses were
adoption-time counts, not refreshed by this proof-ergonomics change. An axiom
count alone is neither a soundness certificate nor a comparison of theorem
strength. Consult `proof/README.md` and `proof/PLAN.md` for current metatheory
claims and their remaining hypotheses/refinement obligations.

## Invariants and remaining scope

No new kernel constructors, proof postulates, Lean build dependency, schema
migration, or termination bypass. Automation is untrusted and checked at the
original goal. User macros and richer backward application are not claimed
complete merely because their parser vocabulary or host-side API exists.

When behavior changes, update the corresponding corpus expectation and this
scorecard together. Negative safety pins are not aspirations to accept invalid
proofs. Keep source-level parity separate from executable-kernel, erasure,
artifact-producer and runtime correspondence work.
