# Lean 4 Parity — Status Scorecard

Updated 2026-11-22 against the implementation and executable proof suites.
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
- **Template-tactic slice (historical Phase 3): implemented and audited.**
  Libraries can compose contextual, checked proof commands. This is a
  prerequisite for C1.2, not the complete goal-metaprogramming feature.
- **Phase 4 — C1.2, C6, C7:** incomplete. Goal-inspecting `computed by`
  tactics over `Std.Tactic`, premise-generating backward `apply`, and
  per-command editor/REPL goal views remain. Named template tactics, `exact`,
  and closing `apply` already work.
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
incompatible goal struct. Existing justification commands pass through
`Tactic.command/1`. Ordinary induction retains declaration-level recursive
lowering; exposing it as a template command remains a separate reach gap.

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

### C1.2 prerequisite — checked template tactics

Historical execution-plan Phase 3 adds `tactic ... becomes ...` to the macro
container. It supports finite nested command aliases, checked local facts,
simplification, rewriting, explicit evidence, and solver commands. Open
transformed goals return to the caller; a complete justification ending open
still fails E110. Statements after closure are rejected rather than skipped.

The declaration and instantiated command shapes are validated, but the ultimate
trust boundary is kernel checking against the original obligation. Template
rules do not expose a goal value or execute a goal-inspecting Cure function.
**Full C1.2 is therefore not closed.** Induction templates are currently refused
at declaration, while actual tactic invocations inside ordinary induction arms
are checked and supported.

The 2026-11-22 audit corrected silent printer deletion/crashes, nested expression
keyword capture, unsafe literal lookahead, contextual and sequence example pins,
nested alias expansion, source-provider grammar shadowing, open-goal handling,
unreachable statements, trace duplication, and malformed command acceptance.
The former induction test declared a tactic without invoking it; it now invokes
one. The claimed `run_all(Result)` solution-loss defect was not present: its
existing evidence retention is preserved and the obsolete workaround removed.

Evidence: `test/cure/elab/tactic_macro_test.exs`,
`test/cure/elab/tactic_macro_audit_test.exs`, and
`test/cure/compiler/tactic_macro_audit_test.exs`. Tests include exact Core-byte
comparison with handwritten commands, changed-original-goal refusal, actual
Core-shaped AST rejection, real induction-arm calls, typed example acceptance
and refusal, source imports, and printer fixpoints with optional/repeated uses.
These are specific checked safety properties, not a machine-checked soundness
theorem for all frontend execution.

Source-backed imported tactic aliases retain provider helper grammar. Loading
macro grammar from interfaces alone is still an inherited limitation shared
with ordinary syntax macros; this change does not redesign artifact formats.

## Corpus and historical G-register

The corpus uses historical G1–G11 identifiers, not the C-register or the gap
numbers in the even older readiness audit. Retain stable IDs rather than
silently reassign their meaning.

- **G1 / C7:** diagnostic and hole introspection exist; complete cursor-position
  goal tooling is still open. Unfinished proofs and holes must still refuse
  compilation.
- **G2 / C1:** goal execution/composition and named template tactics landed.
  Goal-inspecting computed tactics are still missing, independently of C6's
  premise-generating `apply`. Do not equate a new rule kind with full C1.2.
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
tactic that closes a real goal (with its Core-term refusal): **25 cases, 16
accept and 9 reject**, measured from `Corpus.all/0`. Rejection counts include
deliberate safety boundaries, not just unfinished features.

Current audit validation: the first 18 focused regression tests exposed 17
failures in the prepared solution; the corrected focused integration run passes
112 tests. The expanded parity suite passes 32 tests, including the additional
false-goal pin checked through the real compiler pipeline. All 359 documentation
snippets, 69 stdlib checks and 40 examples pass. Formatting, strict Credo and
Dialyzer pass with the existing ignore inventory unchanged. The final standard
`mix test` passes **7,104 tests, zero failures, eight excluded**, followed by
**359 documentation snippets, zero failures** (seed 622482). Antigen produces
all 318 declared shape cells across 31 assays.

## Prior Phase 1/2 validation (2026-11-21)
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
