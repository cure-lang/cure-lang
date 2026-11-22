# Lean 4 Parity — Status Scorecard

Updated for the 2026-11-22 implementation continuation. Current integrated
validation is recorded separately from historical audit measurements below.
**Authoritative scope and phases:** [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md), §8.
**Proof-language reference:** [`PROOFS.md`](PROOFS.md).
**Source corpus:** [`test/lean4_parity/`](../test/lean4_parity/), run with
`mix test test/lean4_parity_test.exs`.

## Phase status

- **Phase 1 — C4, C5, C8: implemented.** Explicit simp admission, certified
  unfolding, and deterministic opt-in rewrite-all have positive and refusal
  tests. No kernel rules or Agda files changed.
- **Phase 2 — C1.1, C1.3: infrastructure delivered; adequacy gate incomplete.**
  Existing justification commands use the checked goal API and combinators
  retain evidence. Bounded solver clients have positive/refusal controls.
  Reusable induction-command lowering remains open.
- **Phase 3 — C3:** not audited for completion in this change. Parser support
  alone does not establish declaration-driven transitive fixity completion.
- **Template-tactic slice (historical Phase 3): implemented and audited.**
  Libraries can compose contextual, checked proof commands. This is a
  prerequisite slice, separate from the typed computed protocol.
- **Phase 4 — C1.2, C6, C7: partial.** Typed goal-inspecting computed tactics
  and per-command cursor-filtered LSP/REPL views are delivered. Closing `apply`
  does not generate premises: C6's backward-reconstruction gate is still open.
  The VS Code goal-panel client is absent, and legacy hole inlay hints retain
  their definition-return-summary limitation. `simp?`, local-only assumption,
  and checked bounded integer-order reconstruction are delivered slices, not
  completion of unrestricted arithmetic automation or authoritative Phase 4.
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
- `by assumption`: matching local propositional evidence only, with no tagged
  lemma search, projections, or automatic inhabitants of value types.
- `by positivity`: the curated natural-number `IsPositive` fragment, including
  successors, addition, multiplication and sign hypotheses. It is not generic
  lemma search and refuses zero/unknown signs/unrelated propositions.
- `by decide`: infer the certified Boolean-equality decider.
  `by decide using expression`: accept an explicit `Decision(P)`, normalize
  only through certified Core, extract actual `Yes` evidence, and check it at
  the unchanged original goal. `No`, stuck decisions and host Booleans refuse.
- `by omega`: reconstruct ordinary evidence for non-strict
  `Std.Proof.IntOrder` goals from local evidence, reflexivity, transitivity,
  add-same, add-both and literal-natural scaling. Bounds: 128 original local
  slots, depth 12, 512 reconstruction steps and scalars at most 1024.
  Strict/equality/nonlinear and otherwise unreconstructed goals refuse, as do
  closed non-reflexive literal comparisons. The certified Boolean candidate
  checker is not itself a theorem proving the original goal; successful
  checking must be followed by checked reconstruction in this delivered subset.

Commands work in inline/block justifications and checked non-equality function
bodies. Evidence: `test/cure/compiler/solver_test.exs` and
`test/cure/elab/solver_test.exs`.

### C1.2 — templates and typed goal-inspecting computed tactics

Historical execution-plan Phase 3 adds `tactic ... becomes ...` to the macro
container. It supports finite nested command aliases, checked local facts,
simplification, rewriting, explicit evidence, and solver commands. Open
transformed goals return to the caller; a complete justification ending open
still fails E110. Statements after closure are rejected rather than skipped.

The declaration and instantiated command shapes are validated, but the ultimate
trust boundary is kernel checking against the original obligation. Template
rules alone do not expose a goal value or execute a goal-inspecting Cure
function. The continuation supplies that separate computed protocol. Induction
templates are currently refused at declaration, while actual tactic invocations
inside ordinary induction arms are checked and supported.

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

Computed rules take captured `Syntax` arguments followed by a typed
`Std.Tactic.Goal`, with typed `Hypothesis` records and structural target/type
syntax preserving authored local names. `MacroExpand.expand_typed` checks and
evaluates the callback. It returns one operation or a syntax-list of operations
through `expand(...)`, or authored refusal diagnostics.

The closed request vocabulary has a maximum of 256 operations and validates
arity, arguments and the fresh invocation handle on each operation. Missing,
stale or forged handles, duplicate protocol keys and deferred computed uses in
operation arguments are refused. Explicit `fresh(...)` markers distinguish
generated binders from authored names. Requests execute as ordinary checked
commands at the original goal; editing reflected target data cannot replace
that obligation. Evidence: `test/cure/elab/computed_phase4_test.exs`, including
actual inspection, source-backed imports, checked Core-byte comparisons,
authored diagnostics, hygiene and original-goal/false-goal controls.
Imported bare callbacks in multi-module provider files are conservatively
refused; use an explicitly qualified callback there. Interface-only grammar
publication remains outside this source-backed protocol.

### C7 — source-indexed command views

`Cure.Elab.ProofState` captures command before/after/failure states and final
unfinished residuals, and emits `:proof_state` events. The custom
`cure/proofState` request honors the cursor and negotiated UTF-8/16/32 positions.
Its target and local context use authored names, including deferred `have`
facts. Hole observations record the actual expected type at the hole, not the
enclosing function's return type.

REPL `:goals` retains the last definition submission's proof states even when
the definition was refused; it does not install the failed definition.
`Session.goals/1` uses the same observation API. Evidence:
`test/cure/elab/proof_state_integration_test.exs`.

**Remaining boundary:** no VS Code goal-panel consumer is supplied. Legacy
`Program.hole_goals/1`, associated definition summaries, and existing hole
inlay hints still do not expose precise nested-hole obligations. A custom
server capability is not itself an editor UI, and these surfaces are not
claimed to agree in every case.

## Corpus and historical G-register

The corpus uses historical G1–G11 identifiers, not the C-register or the gap
numbers in the even older readiness audit. Retain stable IDs rather than
silently reassign their meaning.
- **G1 / C7:** per-command observations and cursor-filtered server/REPL views
  delivered; the VS Code panel and precise legacy inlay hints remain open.
- **G2 / C1:** goal execution/composition and named template tactics landed.
  Typed goal-inspecting computed tactics now execute checked requests.
  Premise-generating `apply` and reusable induction-command adequacy remain
  distinct open gates.
- **G3 / C5,C9:** certified computation verified; guarded-recursion ledger not
  changed. The neutral right-identity rejection is not itself a parity gap.
- **G4 / C4:** explicit simp admission and quantified ambient rules implemented.
- **G5 / C1.3:** explicit solver entry points implemented in their stated
  fragments, including local-only assumption and bounded checked integer-order
  reconstruction. No general Farkas checker-to-goal soundness theorem is
  claimed. A rejected dependent-decision library-call pin is a specific reach
  boundary, not evidence that all decision clients are absent.
- **G9 / C2:** universe work not changed. Surface binders alone are not proof of
  arbitrary-level kernel polymorphism.
- **G10:** `simp?` is implemented. It runs the same simplification as
  `simplify` and reports the ambient lemmas that actually progressed the goal,
  both in the proof trace and as a `:simp_trace` pipeline event. Event reports
  include only the current successful invocation's progress; explicit-rule and
  proof-adaptation traces and actual source metadata are included.
- **G6, G7, G8, G11:** proof/runtime correspondence obligations, not source
  capability pins. They remain outside this phase and have no corpus entries.

The corpus includes the adoption baseline plus explicit Phase 1/2/3 cases for
certified recursive computation, quantified simp, looping-rule refusal,
multi-occurrence transport, solver acceptance/refusal, and a library-defined
tactic that closes a real goal (with its Core-term refusal), plus Phase 4 cases
for goal-inspecting computed tactics (accepted, false-goal refusal, closed
operation vocabulary), closing `apply` (accepted, mismatch refusal),
`by assumption` (accepted, non-hypothesis refusal, proof-relevant value-type
refusal), `by omega` (checked-reconstruction acceptance and unsupported/refusal
controls) and `simp?`. Rejection counts include deliberate safety boundaries,
not just unfinished features.

The current inventory measured from `Corpus.all/0` is **39 cases: 21 accept
and 18 reject**. All pins pass through the actual compiler pipeline in the
integrated parity replay.

## Current continuation validation

Final integrated validation on 2026-11-22:
- The combined computed-tactic, Phase 4, omega, proof-state, completion and
  parity run passed **150 tests, zero failures**.
- Standard `MIX_ENV=test mix test --seed 622482` passed **7,214 tests, zero
  failures, eight excluded**, followed by **361 documentation snippets, zero
  failures**. Antigen covered all **318 declared shape cells across 31 assays**.
- `MIX_ENV=test mix check` passed **71 stdlib checks and 40 examples**, with
  zero failures and zero skipped examples.
- `MIX_ENV=test mix quality.ci`, `MIX_ENV=test mix dialyzer`, and
  `git diff --check` passed. The existing Dialyzer ignore inventory is unchanged.

The final full run followed the Dialyzer-driven traversal typing and unreachable
producer-result corrections. Earlier measurements below remain historical.
These results validate the delivered slices, not premise-generating `apply`,
reusable induction lowering, a VS Code panel, complete arithmetic automation,
or a universal soundness theorem. No kernel, Agda, dependency, schema or
warning-suppression changes were needed.

## Historical template-tactic audit validation (2026-11-22)

The earlier audit recorded that the first 18 focused regression tests exposed 17
failures in the prepared solution; the corrected focused integration passed
112 tests. Its expanded parity suite passed 32 tests, including the additional
false-goal pin checked through the real compiler pipeline. It recorded 359
documentation snippets, 69 stdlib checks and 40 examples passing, along with
formatting, strict Credo and Dialyzer using the existing ignore inventory.
The recorded standard `mix test` result was **7,104 tests, zero failures, eight
excluded**, followed by **359 documentation snippets, zero failures** (seed
622482). That audit also recorded all 318 declared Antigen shape cells across
31 assays. These are not fresh continuation results.

## Historical Phase 1/2 validation (2026-11-21)
The recorded final focused integration passed **96 tests, zero failures**.
The documentation checker passed **357 snippets, zero failures**.
`mix quality.ci`, `mix dialyzer`, and `git diff --check` passed with the existing
Dialyzer ignore inventory unchanged. The broad proof/compiler/diagnostic/REPL
regression run passed **3,910 tests, zero failures, two excluded**.
The frozen-snapshot standard `mix test` passed **7,060 tests, zero failures,
eight excluded**, followed by **357
documentation snippets, zero failures** (seed 200312).
The separate `mix check` regression task also passed: **69 stdlib checks and
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
original goal. Typed computed tactics are a bounded checked-request protocol,
not unrestricted metaprogramming. Premise-generating application, reusable
induction-command adequacy, the VS Code goal panel and a general arithmetic
checker-to-goal theorem remain open.

When behavior changes, update the corresponding corpus expectation and this
scorecard together. Negative safety pins are not aspirations to accept invalid
proofs. Keep source-level parity separate from executable-kernel, erasure,
artifact-producer and runtime correspondence work.
