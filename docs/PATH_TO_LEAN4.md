# Cure → Lean Feature Parity: Audited Roadmap

**Phase 4 is complete within its stated C1.2/C6/C7 gates (2026-11-22).**
Final integrated tests, compiled parity and the real rebuilt-server Extension
Host pass. The inherited induction-command adequacy gate is also met.
The scope limits below remain explicit; overall Lean parity is not claimed.
This document is authoritative for the C1–C10 register, phase numbering and
completion gates. It supersedes
[`LEAN4_MIGRATION_PLAN.md`](LEAN4_MIGRATION_PLAN.md);
[`PATH_TO_LEAN4_PLAN.md`](PATH_TO_LEAN4_PLAN.md) uses historical phase numbers.
[`LEAN4_PARITY_STATUS.md`](LEAN4_PARITY_STATUS.md) records measured evidence;
[`PROOFS.md`](PROOFS.md) and [`MACROS.md`](MACROS.md) describe supported syntax.

Scope: make **Cure itself** reach feature parity with Lean 4. No porting. The
Agda development in `proof/` is a separate metatheory track, not a porting target
or a substitute for Cure-facing proof tooling.

## Audited implementation status

**Phase 1 is complete within its stated gates. Phase 2's goal infrastructure,
solver clients and genuine induction command are implemented.** Ordinary
induction and its branches now execute through the goal API using the canonical
declaration frame and existing checked recursive lowering. Merged six-command
compatibility and evidence validation pass, including actual IH use and
refusal controls; a command tag alone was not counted as completion.

- **C5:** certified recursive unfolding already existed through kernel
  normalization; nested computational goals now have explicit positive and
  certificate-removal refusal tests. No second unfolding path or kernel change.
- **C8:** `rewrite … all` now visits original occurrences deterministically and
  composes checked transports correctly. The strict single-occurrence default
  and E111 diagnostics are unchanged.
- **C4:** explicit `@simp` / `@lemma(:simp)` declarations reject non-decreasing
  and variable-duplicating orientations with authored E112 diagnostics.
  Certified quantified lemmas specialize with checked evidence, including
  imported lemmas; safe legacy `@lemma` behavior is preserved.
- **C1.1:** `ProofGoal` is the goal representation (not a second `Goal`
  struct). Construction and inspection preserve the original target/context.
  Existing justification commands execute through `Tactic.command/1`;
  `Tactic.Result` retains closure evidence through sequencing, choice, focus,
  all-goals and bounded repeat-until-failure.
- **C1.3:** `by search`, `by positivity`, and `by decide [using expression]`
  are checked solver clients, with positive and refusal corpora. `by assumption`
  reuses local propositional evidence only. `by omega` reconstructs a bounded
  non-strict integer-order fragment with checked library lemmas; a successful
  Boolean arithmetic-candidate check alone is not evidence of the goal.
- **C1.2:** `tactic ... computed by` callbacks receive typed `Std.Tactic.Goal`
  values with structural target/hypothesis syntax and authored local names.
  Returned operations are bounded, authenticated requests to existing checked
  commands, not proof objects.
- **C7:** per-command observations, cursor-filtered `cure/proofState` requests
  and REPL `:goals` now share an explicit ephemeral `SourceContext` with actual
  checking-site hole reports, CLI output and inlay hints. A native VS Code
  goal tree consumes these states; real integrated host validation passes.
  Env-only `Program.hole_goals/1` remains a coarse compatibility API.
- **C6:** backward application produces ordered focused premises, stages
  dependent domains, and reconstructs checked evidence at the original parent.
  An unresolved implicit witness is a visible typed obligation, not hidden
  search. Pending parents are not solved goals.
- **Proof admission:** a hole-free declaration executing proof syntax or successful implicit search
  must receive ordinary totality certification, including its evidence
  dependencies. Uncertified recursive evidence is refused with E013; kernel
  typing alone does not prove termination. No kernel rule or bypass is added.

Corrections to the original analysis: a neutral `plus(n, Z()) = n` requires
induction in Lean too, so its rejection is not a delta-reach gap. A parser node
alone was not evidence that rewrite-all or inline proof commands worked.
`@lemma` simplification existed but its quantified path was broken.

The remaining sections distinguish implemented mechanisms from future work.
References to `@[simp]` mean the capability, spelled `@simp` or
`@lemma(:simp)` in Cure. Delivered closure mechanisms and measured integration
results are distinguished throughout and recorded in the scorecard.

### Template-tactic audit — 2026-11-22

Historical `PATH_TO_LEAN4_PLAN.md` Phase 3 now provides contextual
`tactic ... becomes ...` command templates. The audit repaired command
composition, declaration/usage printing, contextual expression isolation,
example pins, nested aliases and imported helper grammar. Its tests invoke
tactics and compare checked Core with handwritten expansions.

That template slice alone did **not** complete C1.2: a template sees captures,
not a goal. The subsequent continuation adds the goal-inspecting
`computed by` / `Std.Tactic` protocol described below.
Authoritative Phase 3 (§8) remains operator fixity; template tactics are a
prerequisite slice of authoritative Phase 4. See the scorecard for measured
status. Induction templates now invoke the checked induction command, with
structural case validation and constructor-field/IH binder hygiene.
Source-backed imported templates retain provider helper grammar; interface-only
macro grammar loading remains an inherited limitation shared with syntax macros.

### Evidence and claim boundary

The pre-continuation code-audit run recorded **7,104 tests, zero failures,
eight excluded** (seed 622482), followed by **359 documentation snippets,
zero failures**.
The separate regression task passed **69 stdlib checks and 40 examples**.
Formatting, strict Credo, Dialyzer and whitespace checks passed without adding
warning suppressions. These are recorded audit results, not a new claim of
universal soundness or a fresh audit of every language subsystem.

That audit's parity corpus had **25 cases: 16 accept and 9 reject**. Its accepted
`g2-tactic-rule-kind` program contains a theorem invoking the tactic and goes
through elaboration and kernel checking. The corpus measures reach; separate
tests assert Core-byte equivalence, original-goal preservation, actual
Core-shaped AST refusal and real induction-arm calls. Neither suite alone is
a machine-checked soundness theorem. Deliberate negative pins, including false
goals and unfinished proofs, must remain negative.

These measurements are historical baselines, not validation of the current
closure implementation. The previous continuation run passed **7,214 tests, zero failures,
eight excluded**, followed by **361 documentation snippets, zero failures**
(seed 622482). All **39 parity pins**, **71 stdlib checks and 40 examples**
passed; formatting, Credo, Dialyzer and whitespace checks passed without new
suppressions. The scorecard records the detailed results and remaining gates;
passing those historical checks does not establish current Phase 4 closure.
The final closure run passes **7,310 tests, zero failures, eight excluded**
(seed 622482), followed by **363 documentation snippets, zero failures**.
All **44 parity pins (25 accept, 19 reject)**, **71 stdlib checks** and
**40 examples** pass. Formatting, Credo, Dialyzer and whitespace checks pass
without new suppressions. The rebuilt-server official VS Code Extension Host,
TypeScript compilation, grammar check and nine Node tests pass as well.

---

## 1. What "parity" means, and what Cure already has

Lean's capabilities span several mechanisms. The table records implementation
scope, not blanket parity with every Lean tactic, library or calculus feature:

| # | Lean capability | Cure equivalent | Status |
|---|---|---|---|
| P1 | Dependent type theory, indexed families, GADTs | `indexed type`, `indices (…)`, dependent `case` | **Landed** |
| P2 | Proof commands and automation | `simplify`, `rewrite`, ordinary `induction`, checked solver clients and bounded integer-order reconstruction | **Implemented in stated fragments**; no general `omega`/Mathlib automation claim |
| P3 | `macro` / `syntax` / `elab` — user-extensible frontend | `macro` container, `becomes` / `computed by`, `syntax family` | **Landed** |
| P4 | Typeclasses + instance resolution | `interface` / `implementation`, coherence, type-directed search | **Landed** |
| P5 | Instance-driven operators and fixity | Operator interfaces and declaration-driven fixity machinery | **Completion not certified by this audit**; apply C3's full gate |
| P6 | Universe polymorphism (`Type u`) | Existing `Type(l)` / level design, U0–U7 | **Open in this roadmap**; surface binders do not establish arbitrary-level kernel support |
| P7 | Mutual and well-founded recursion | Implicit forward/mutual references; SCC size-change certification | **Mechanisms present**; not a claim of all Lean well-founded-recursion capabilities |
| P8 | Metaprogramming over goals (`Lean.Meta`) | Host goal API, checked templates and typed goal-inspecting `computed by` tactics | **Delivered bounded protocol**; not unrestricted `Lean.Meta` equivalence |

**Implementation boundary:** Cure has checked proof commands, bounded solver
clients, templates, goal-inspecting computed tactics, premise-generating
application, canonical-frame induction and source-aware native editor views.
Their final merged acceptance gates pass. Env-only hole summaries remain
coarse by design. Universes, fixity completion and the reach ledger have
separate gates; this work does not close them.

The tactic layer is not structurally absent. `docs/PROOFS.md` §3 defines
`have`, `proof chain`, `because`, `simplify` (with `using [rules]` and
`simpa`-style `using <proof>`), `rewrite` (with `backwards`/`at`/`in`),
`induction`, holes, and named arguments — all checked, all erasing to nothing.

---

## 2. Gap register: delivered scope and remaining work

| ID | Audited status / remaining gap | Lean counterpart | Impact | Gate |
|---|---|---|---|---|
| **C1** | **Implemented and validated within stated scope:** goal API, combinators, bounded solvers, templates, computed tactics and canonical-frame induction. | `Lean.Meta` / `Lean.Elab.Tactic` | Custom tactics | C1.1–C1.3 below |
| **C2** | **Open:** execute the existing U0–U7 universe design; surface syntax is not its completion gate. | `Type u` | Generic stdlib | Existing spec §21 |
| **C3** | **Unaudited completion:** fixity machinery exists; neither its parser support nor the presence of a `Precedence.ex` module settles the end-to-end gate. | Declared fixity / notation | Operator ergonomics | Section 5 |
| **C4** | **Closed:** explicit decreasing simp declarations and checked quantified ambient rules. | `@[simp]` attribute | Proof tedium | Landed |
| **C5** | **Closed:** certified recursive definitions compute; uncertified recursion stays opaque. | `simp` + certified unfolding | Every proof | Verified existing path |
| **C6** | **Implemented and validated:** focused ordered/staged premises and checked pending-parent reconstruction. | `apply`/`exact` | Proof style | Gate met |
| **C7** | **Implemented and validated:** explicit source-context CLI/REPL/LSP/hints and native VS Code goal tree, including refused states. Env-only compatibility summaries remain coarse. | InfoView | Proof authoring | Gate met |
| **C8** | **Closed:** opt-in `rewrite … all`; default still requires one occurrence. | occurrence selection | Proof tedium | Landed |
| **C9** | **Not closed by this audit:** follow the guarded-lambda recursion entry, K-bug 2. | Termination certification | Reach | Existing kernel ledger |
| **C10** | **Not closed by this audit:** follow the individual elaborator reach entries; E9's premise was falsified and is not an active gap. | — | Reach | Existing kernel ledger |

**Dependency rule:** the evidence-preserving C1.1 infrastructure supports
C1.2, C6 and C7. Full goal-inspecting C1.2 is not a prerequisite for the
already-delivered C4/C5/C8 features. C2 and C3 remain independent tracks.
Original week estimates are not a measured remaining-work forecast and are not
used as completion evidence.

---

## 3. C1 — Goal infrastructure and metaprogramming

Lean's metaprogramming libraries underpin extensible proof automation. Cure has
the syntax interface (`Std.Syntax`, `computed by`), checked template composition,
`Cure.Elab.ProofSearch`, and a bounded Cure-level `Std.Tactic` interface that
lets a callback inspect a goal and request existing checked operations.

### C1.1 — Goal state and command adequacy

**Implemented:** the goal state, checked result shape, combinators and genuine
canonical-frame induction command. **Gate met:** merged non-vacuous
all-six-command execution, reconstruction and diagnostic compatibility.

1. Use `Cure.Elab.ProofGoal` as the single goal state, with `new/5` and
   `inspect_goal/1` for construction and hypothesis/target inspection.
2. Return remaining goals **and checked solutions** in `Tactic.Result`;
   closure evidence must survive composition and check at the original goal.
   Legacy list-only results remain scheduling projections, not proof artifacts.
3. Expose combinators: `focus`, `all_goals`, `seq`, `or_else`, `repeat_until_fail`.
4. Route justification commands through this API while preserving original
   obligations and proof reconstruction. Ordinary induction and authored branch
   commands use the same API, retaining checked match/recursive lowering.
   Standalone callers supply an explicit canonical declaration frame; missing,
   foreign or changed-motive frames refuse. Arbitrary new helper motives are
   not synthesized.

**Measured gate:** all six original proof forms are genuine API clients.
Induction-template and ordinary-source tests actually invoke recursive IHs;
branch, scope, hygiene, false-goal and E109–E115 compatibility controls pass.
This evidence is additional to the existing suite, not inferred from merely
retaining old tests.

### C1.2 — Goal-inspecting library tactics

**Delivered prerequisite:** contextual `tactic ... becomes ...` templates,
finite nested aliases, sequence and typed example pins, source-backed imports,
printer round-trips, open-goal composition and checked closure.

**Delivered protocol:** `tactic <rule> computed by <fn>` names an ordinary
Cure callback. It receives one `Syntax` argument per capture, then a typed
`Std.Tactic.Goal` containing typed `Hypothesis` records, structural target/type
syntax, authored local names and a fresh opaque invocation handle.
`MacroExpand.expand_typed` checks and evaluates the callback. It returns
`expand(operation)` or an expanded syntax-list of operations, or authored
refusal diagnostics.

At most 256 operations may be returned. Each must carry the supplied invocation
handle and name a member of the closed checked-command vocabulary with the
correct arguments. Missing, stale or forged handles, malformed requests and
deferred computed uses in operation arguments are refused. Generated binders
use explicit `fresh(...)` markers rather than capturing authored identifiers.
The callback runs once per invocation; operations run in order and may leave
a transformed goal for a later command.

**Firewall and evidence:** callbacks return requests, not proof objects.
Changing the reflected target cannot change the original checking obligation.
Actual inspection/branching, checked handwritten-vs-computed Core equivalence,
source-backed imports, refusal diagnostics and malformed/original-goal controls
are covered by the computed-tactic tests. These are executable scope checks,
not a universal soundness theorem. Application sessions and canonical-frame
induction supply the corresponding checked commands; the computed protocol
does not turn callbacks into trusted evidence constructors.

### C1.3 — Checked solver clients

**Implemented within explicit fragments:**
- `by search`: local evidence, checked projections and tagged lemmas, refusing
  missing or ambiguous evidence.
- `by assumption`: matching local propositional evidence only; no tagged-lemma
  search or projections, and no automatic inhabitant of a value type.
- `by positivity`: the curated natural-number sign fragment, not generic search.
- `by decide`: inferred Boolean equality decisions; `by decide using expression`
  handles an explicit `Decision(P)` from `Std.Decision` whose certified reduction
  exposes checked `Yes` evidence.
- `by omega`: checked reconstruction of non-strict `Std.Proof.IntOrder`
  comparisons from local evidence, reflexivity, transitivity, addition and
  literal-natural scaling. Reconstruction is bounded by 128 local slots,
  depth 12, 512 steps and scalars at most 1024. Strict/equality/nonlinear or
  unreconstructed goals, including closed non-reflexive literal comparisons,
  are refused. A certified Boolean Farkas-candidate checker exists, but a
  general checker-to-original-goal soundness theorem is not implemented.

**Gate met for these clients:** positive and negative corpora, with refusal for
false, unsupported or stuck goals. This does not claim unrestricted arithmetic
automation or completion of every dependent decision-procedure library call.

---

## 4. C2 — Universe polymorphism (execute the existing spec)

**Status:** not closed or re-audited by the proof-ergonomics work. Accepted
surface level binders are not evidence that the full kernel level algebra,
generic walkers and artifact migration are complete.

The design is **complete and authoritative**:
`docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`,
phases U0–U7, with §21 completion criteria. **Do not redesign it.** Execute it.

Two things to get right, both already flagged in the spec:

1. **Every generic Core walker must descend into level atoms.** The spec names
   this as a soundness bug if missed.
   `docs/superpowers/specs/kernel/MASTER.md` §8 records prior walker-drift
   failures; this is the same failure mode with a new former. Add a coverage
   cell per (walker × level-former).
2. **Serialization version bump.** Every cache/hash containing Core must include
   the universe representation version — artifacts, certificates, interfaces,
   incremental hashes, Antigen corpus.

**Gate:** §21's criteria — `Type : Type` and `TypeLimit : TypeLimit`
unrepresentable; one polymorphic definition works at arbitrary levels; Antigen
sensitive to weakened level equality/ordering/scope.

---

## 5. C3 — Operator fixity (execute Step 3)

**Status:** completion not certified by this audit. Operator declaration and
fixity machinery is present; the earlier assertion that Step 3 was simply
"designed, not built" was not justified. Do not infer completion from parser
support or infer a fixed semantic table merely from a module's name.

Step 2 (sole route) was recorded as landed (`93ed411d`). The end-to-end Step 3
requirements remain those in `docs/superpowers/specs/types/MASTER.md` §7.3 and §7.4:

1. `precedencegroup Name` with `associativity: left|right|none`,
   `higher_than:` / `lower_than:` — a partial order compiled to topological
   binding powers.
2. Incomparable adjacent groups ⇒ `{:ambiguous_precedence, g1, g2}` (stricter
   than numeric levels — Swift behaviour, deliberate).
3. `infix`/`prefix`/`postfix` declarations; `{:no_operator_meaning}` when a
   fixity has no function.
4. `use`-propagated fixity (§7.4): `fixity(M)` is the transitive `use` closure
   plus `@prelude` providers. **The `DepGraph.scan_file` statement-level
   recovery precondition is load-bearing** — without it a module using a
   not-yet-propagated operator is dropped wholesale.
5. Seed semantic fixity from `Std.Operators`, not a competing compiler-owned
   fixed operator table. Compatibility helpers are not themselves evidence of
   a second table; inspect their live callers before deleting them.

**Gate:** end state is "the compiler owns NO fixed operator list"; printer
callers thread `fixity(M)`.

---

## 6. C4–C8 — Proof ergonomics: implemented and remaining

| ID | Status | Boundary / remaining work |
|---|---|---|
| **C4** | Implemented | `@simp` / `@lemma(:simp)` with declaration-time strict decrease and non-increasing variable multiplicities; checked quantified/imported rules and bounded fixed points. Safe legacy `@lemma` rules remain ambient. This is not Lean's literal `@[simp]` syntax or an unrestricted simp-rule admission policy. |
| **C5** | Verified existing path | Certified recursive computation uses existing kernel normalization and certified unfolding, including `Normalise.unfold_certified_head/3`; no second unfold implementation. Uncertified recursion remains opaque. |
| **C6** | Implemented and validated | Partial global/local applications and constructors produce ordered focused premises. Value/proof-dependent domains stage after earlier witnesses close. Original-parent checking happens only after evidence reconstruction; no metas or internal holes count as evidence. |
| **C7** | Implemented and validated | Explicit source context drives actual hole occurrences, CLI/REPL/LSP/hints and the native VS Code tree. Version/URI/cursor/generation checks reject stale client results; empty cursor state is not a proof-completion claim. Env-only `Program.hole_goals/1` remains coarse. |
| **C8** | Implemented | Opt-in `rewrite … all` visits original normalized occurrences, composes checked transports, respects binder scope and does not revisit replacement-introduced occurrences. Keep the strict single-occurrence default. |

---

## 7. C9–C10 — Reach gaps (execute the existing ledger)

Both are already scoped in `docs/superpowers/specs/kernel/MASTER.md` §5.3 and §9.
**Do not re-plan.**
This audit did not certify their closure or authorize new kernel changes.

- **C9 (K-bug 2):** recognise deferred self-calls under an unapplied lambda as
  not owing the decrease (mirror Idris). Follow the recorded design decision
  and project hard-stop requirements for any TCB change.
  Antibody = a must-certify pin. Completeness, not soundness.
- **C10:** E9 (premise falsified — not a gap), E10 (higher-order in index
  position; do last), E12 (`rewrite` δ-blind occurrence finder), E13 (diagonal
  GADT one-way unification), K-bug 1 (order-dependent ctor injectivity).
  Discipline per gap: red-green oracle-anchored, negative antibody, done = the
  workaround is removed from a real module that still replays `rel=same`.

---

## 8. Authoritative phases and closure gates

Phase numbers below are stable. In particular, **Phase 3 means C3 fixity**.
The template-tactic work called "Phase 3" in the historical execution companion
is a delivered slice of **Phase 4**, not a renumbering or completion of it.

| Phase | Scope | Audited status | Closure gate |
|---|---|---|---|
| **1** | C4, C5, C8 | **Complete for stated scope** | Certified-recursive simplification closes; unsafe/looping explicit simp declarations are rejected; multi-occurrence rewrite-all closes through checked transports; uncertified/false-goal refusals remain. |
| **2** | C1.1, C1.3 | **Complete for stated scope** | Genuine canonical-frame induction and branch clients join the goal API. All six original forms, compatibility diagnostics, hygienic IH use and ordinary checked evidence/totality are validated. |
| **3** | C3 | **Completion unaudited** | Establish declaration-driven semantic fixity across transitive `use`/prelude closure, ambiguity/refusal behavior and printer callers; no competing fixed semantic operator list. |
| **4** | C1.2, C6, C7 | **Complete for documented contracts** | Computed/original-goal controls, focused ordered/staged reconstruction, precise source views, real merged-server Extension Host behavior and automatic proof-admission refusals pass with the final full validation. |
| **5** | C2 | **Not closed by this audit** | Meet the existing universe spec's §21 criteria, including arbitrary-level polymorphism, prohibited self-typing, walker coverage and artifact/version obligations. |
| **6** | C9, C10 | **Per-ledger work remains** | Close each genuine reach item with oracle-anchored positive/negative pins and remove its workaround from a real module that still replays `rel=same`, or explicitly retain it as deliberate. |

C2 and C3 can proceed independently. Validate the actual induction-client
execution rather than treating a passing old suite as proof that every command
is exposed. Phase 4 builds on the delivered goal infrastructure; metatheory,
second-checker and runtime correspondence obligations remain separate tracks.

**Evidence:**
- Goal state, proof reconstruction, combinators and certified unfolding:
  `test/cure/elab/tactic_integration_test.exs` and `test/cure/elab/tactic_test.exs`.
- Simp admission and source diagnostics: `test/cure/elab/simp_set_test.exs`
  and `test/cure/diagnostic/simp_declaration_test.exs`.
- Solver and existing proof compatibility:
  `test/cure/elab/solver_test.exs`, `test/cure/elab/proof_ergonomics_test.exs`, and the
  existing proof-language/compiler/diagnostic suites.
- Actual template execution, Core-byte equivalence, original-goal controls,
  source imports and printer fixpoints: `test/cure/elab/tactic_macro_test.exs`,
  `test/cure/elab/tactic_macro_audit_test.exs`, and
  `test/cure/compiler/tactic_macro_audit_test.exs`.
- Typed computed-goal inspection and authenticated checked requests:
  `test/cure/elab/computed_phase4_test.exs`.
- Command events, encoded cursor transport, named local facts, precise nested
  holes and refused REPL proof retention:
  `test/cure/elab/proof_state_integration_test.exs`.
- Arithmetic candidate/reifier controls and checked order reconstruction:
  `test/cure/elab/omega_pipeline_test.exs`, `omega_proof_test.exs` and
  `omega_solver_test.exs` in the same directory.
- Reach through the real compiler, including deliberate refusals:
  `test/lean4_parity_test.exs` and `test/lean4_parity/corpus.exs`.
- Ordered/staged applications, parent evidence and genuine induction:
  `test/cure/elab/application_session_test.exs`,
  `test/cure/elab/phase4_closure_audit_test.exs` and
  `test/cure/elab/induction_command_test.exs`.
- Source isolation, admission and the arithmetic proof dependency cone:
  `test/cure/elab/source_context_test.exs`,
  `test/cure/elab/proof_admission_test.exs` and
  `test/cure/elab/int_order_totality_test.exs`.
- Actual native editor consumer: `vscode-cure/src/test/hostSuite.ts`,
  `vscode-cure/test/` and `.github/workflows/extension.yml`.

### Proof-admission gate

Completed declarations executing proof syntax or successful implicit search require ordinary
totality certification after body checking. This includes templates/computed
tactics, induction and legacy `rewrite proof in body`; quoted syntax is data,
not executed proof syntax. E013 distinguishes an unproven logical-proof
requirement from an authored `@total true` requirement. `@total false` cannot
waive proof admission. Ordinary partial runtime code remains legal, and
development holes remain checkable but cannot pass release/code-generation
E014. No pending certification deferral counts as proof.
Anonymous search holes and automatic refinements are covered; only the
selected overload commits admission effects. Ordinary partial runtime code
without proof execution is not reclassified merely by a discarded candidate.

Single-buffer compile/check and imported-provider loading share canonical
grammar expansion. The editor checks an unsaved active consumer with saved
source providers; provider saves invalidate dependent analysis. Unsaved sibling
provider overlays and interface-only grammar publication are not claimed.

The integer-order dependency cone is repaired through four private structural
Nat helpers for commutativity/associativity without changing public theorem
types or trusted termination rules. This does not add general Farkas
soundness, full Presburger automation or a broader `omega` fragment.

Scope-specific test success is not a completion claim for unexercised
interfaces or a substitute for a kernel soundness/refinement theorem.

---

## 9. Relationship to the earlier metatheory plan

`LEAN4_MIGRATION_PLAN.md` is historical. Retaining Agda and building Cure-native
tooling is consistent with this roadmap; the withdrawn claim is that extending
the metatheory or adopting a rule name establishes user-facing proof parity.
Keep the tracks and their evidence separate:

1. **Agda models the kernel; Cure tooling supplies the user-facing capability.**
   Proof ergonomics work happens in `lib/cure/elab/`, `lib/cure/compiler/` and
   Cure libraries. A successful metatheory check alone does not add a goal API,
   a backward application tactic or an editor view.
2. **A second checking backend is a separate obligation.**
   `docs/superpowers/specs/kernel/MASTER.md` §1.1 decision 6 records the
   lean4lean backend direction via forgetful projection. It witnesses the
   dependent skeleton, not the quantitative layer. The decision is not evidence
   that the backend is implemented, and the template-tactic audit does not
   close it or add a Lean toolchain dependency.
3. **Final Core is deliberately Idris/Agda-shaped, not Lean-shaped**
   (`docs/superpowers/specs/kernel/MASTER.md` §1.1 decision 5): QTT
   multiplicities, predicative cumulative universes, irrelevance via quantity
   0, no impredicative `Prop`.
   The proposed QTT→Lean projection is forgetful: checking the dependent
   skeleton does not certify the quantitative layer. Parity therefore means
   **parity of capability, not equivalence of calculi.**

The applicable non-goals are stated explicitly in §11 below.

---

## 10. Definition of done

Cure reaches Lean feature parity when:

1. A user can write a tactic that inspects the goal and decides what to do (C1).
2. `Type(l)` is polymorphic and the ceiling is gone (C2).
3. Operators have declaration-driven, `use`-propagated fixity (C3).
4. Explicit simp admission and certified unfolding close the stated
   computational/lemma-driven goals while refusing unsafe rules (C4, C5;
   delivered within their gates).
5. Backward `apply` produces premise goals and reconstructs checked evidence;
   accepting the spellings `apply`/`exact` is not enough (C6).
6. Remaining goals are visible at the cursor after proof commands, not just
   at holes or in failure diagnostics (C7).
7. The open reach ledger (C9, C10) is closed or explicitly pinned as
   deliberate.

The audited implementation satisfies some of these gates, not all. Original
effort estimates are historical and have not been recalculated as a remaining
schedule. Do not infer overall Lean parity from a green scoped test suite.

---

## 11. Non-goals and invariants

- Do not port anything to Lean. Final Core stays Idris/Agda-shaped.
- Do not add `propext` or `Classical.choice` merely to match Lean's axiom count.
  Preserve the existing axiom policy and consult `proof/README.md` for its
  current inventory and caveats; axiom counts alone do not establish comparative
  soundness or theorem strength.
- Do not permit termination/positivity pragmas; the bypass allowlist stays empty.
- Do not change `rewrite`'s single-occurrence default.
- Do not let `simplify` declare terms equal because the host computed so.
- Do not delete the `Proof/*Examples.agda` fixtures — they are the non-vacuity
  evidence for the parameterised theorems.
- Do not redesign the universe-polymorphism spec; execute it.
