# Lean 4 Feature Parity — Roadmap & Status

Single source of truth for Cure's Lean 4 feature-parity effort, consolidating
and replacing the six earlier roadmap, audit, execution-plan, scorecard, and
Phase 5 inventory documents.

- **Scope:** make **Cure itself** reach practical proof-engineering and
  type-system feature parity with Lean 4. No porting to Lean. Final Core stays
  Idris/Agda-shaped (QTT multiplicities, predicative cumulative universes,
  quantity-0 erasure, no impredicative `Prop`). Parity means **parity of
  capability, not equivalence of calculi**.
- **Separate track:** the Agda metatheory and executable-kernel correspondence
  work lives in [`proof/README.md`](../proof/README.md) and
  [`proof/PLAN.md`](../proof/PLAN.md).
- **Proof-language & macro references:** [`PROOFS.md`](PROOFS.md),
  [`MACROS.md`](MACROS.md).
- **Pinned source corpus:** [`test/lean4_parity/`](../test/lean4_parity/)
  (`mix test test/lean4_parity_test.exs`).

---

## 1. Status at a glance

**All six phases (Phases 1–6, `C1`–`C10`) are complete within their documented
contracts.** Remaining items outside this roadmap are explicit scope boundaries
and separate metatheory/backend tracks (§3).

| Phase | IDs | Capability | Lean counterpart | Status |
|---|---|---|---|---|
| **1** | **C4, C5, C8** | Ambient `@simp`, certified recursive computation, opt-in `rewrite … all` | `@[simp]`, `simp` + `whnf`, occurrence selection | **Done** |
| **2** | **C1.1, C1.3** | Checked goal API & combinators, canonical-frame `induction`, bounded solver clients (`search`, `assumption`, `positivity`, `decide`, `omega`, `simp?`) | `Lean.Elab.Tactic` core, built-in solvers | **Done** |
| **3** | **C3** | Declaration-driven, `use`-propagated operator fixity (`Std.Operators`, `FixityTable`, `FixityResolver`, printer `fixity(M)`) | Declared fixity / notation | **Done** |
| **4** | **C1.2, C6, C7** | Template & typed goal-inspecting `computed by` tactics, premise-generating `apply`/`exact`, source-context CLI/REPL/LSP/VS Code goal view, automatic proof-admission totality | User tactics, `apply`/`exact`, InfoView | **Done** |
| **5** | **C2** | Agda-style predicative universe polymorphism (U0–U7), ceiling removed | `Type u` | **Done** |
| **6** | **C9, C10** | Kernel & elaborator reach ledger (`K-bug 1`, `K-bug 2`, `E6-A`, `E10`, `E12`, `E13`) | Termination & unification reach | **Done** |

### Definition of done

- [x] **C1** — Users can write tactics that inspect the goal and request checked operations.
- [x] **C2** — `Type(l)` is universe-polymorphic and the fixed universe ceiling is gone.
- [x] **C3** — Operators have declaration-driven, `use`-propagated fixity with no competing compiler-owned fixed table.
- [x] **C4, C5, C8** — Explicit `@simp` admission, certified recursive unfolding, and opt-in `rewrite … all` work within their safety gates.
- [x] **C6** — Backward `apply` produces ordered/staged premise goals and reconstructs checked evidence.
- [x] **C7** — Remaining goals are visible at the cursor after proof commands in CLI, REPL, LSP, and VS Code.
- [x] **C9, C10** — Every genuine item in the kernel/elaborator reach ledger is closed with positive and negative controls.

---

## 2. What's done

### Phase 1 — Simplification, certified computation, and rewrite-all (`C4`, `C5`, `C8`)

- **C4 (ambient simplification):** `@simp` and `@lemma(:simp)` use Cure's
  decorator grammar (Lean's `@[simp]` spelling is not added). Explicit
  declarations are rejected with `E112` unless equality endpoints strictly
  decrease in Core size without introducing or duplicating quantified variables;
  binder-containing endpoints are conservatively refused. Certified quantified
  rules specialize to checked evidence (including across imports) and run to a
  bounded fixed point. Safe legacy `@lemma` equations remain ambient.
- **C5 (certified computation):** `simplify` uses the existing kernel
  normalization and certified unfolding path (`Normalise.unfold_certified_head/3`)
  covering β, ι, ζ, and certified δ — no second unfolding implementation and no
  kernel change. Nested certified recursive computation (e.g.
  `plus(Z(), plus(Z(), n)) = n`) closes; uncertified recursion remains opaque.
  *(Note: neutral `plus(n, Z()) = n` requires induction in Lean too and is not
  a delta-reach gap.)*
- **C8 (`rewrite … all`):** opt-in `rewrite using h all` (and its backwards
  form) visits occurrences in the original normalized target in deterministic
  left-to-right order, composing checked equality transports back to the
  original goal without revisiting replacement-introduced occurrences. The
  strict single-occurrence default (`E111` on ambiguity) is preserved.

### Phase 2 — Goal API, canonical-frame induction, and checked solvers (`C1.1`, `C1.3`)

- **C1.1 (goal API & combinators):** `Cure.Elab.ProofGoal` is the single goal
  state (`new/5`, `inspect_goal/1`), preserving original target, context, and
  goal identity. `Tactic.Result` retains remaining goals and checked solutions
  keyed by goal identity across `seq`, `or_else`, `focus`, `all_goals`, and
  bounded `repeat_until_fail`. All six original proof commands (`have`,
  `proof chain`, `because`, `simplify`, `rewrite`, `induction`) execute through
  `Tactic.command/1` with `E109`–`E115` diagnostic compatibility. Ordinary
  `induction` and authored branches execute through the goal API using a
  canonical declaration frame and existing checked recursive lowering, with
  hygienic field/IH binders and refusal of missing/foreign/changed-motive
  frames.
- **C1.3 (checked solver clients):** all automation is untrusted-and-checked at
  the original goal:
  - `by search` — local evidence, checked projections, and tagged lemmas
    (refuses missing or ambiguous evidence).
  - `by assumption` — matching local propositional evidence only (no tagged
    lemmas, projections, or value-type inhabitants).
  - `by positivity` — curated natural-number `IsPositive` fragment.
  - `by decide` / `by decide using expr` — inferred Boolean-equality decider or
    explicit `Std.Decision.Decision(P)` normalized via certified Core to checked
    `Yes` evidence (`No`, stuck decisions, and host Booleans refuse).
  - `by omega` — checked reconstruction of non-strict `Std.Proof.IntOrder` goals
    from local evidence, reflexivity, transitivity, addition, and literal-natural
    scaling (bounds: 128 local slots, depth 12, 512 steps, scalars ≤ 1024).
    Strict, equality, nonlinear, and closed non-reflexive literal goals refuse.
  - `simp?` — runs `simplify` and reports only the rules that actually
    progressed the current invocation in the proof trace and `:simp_trace`
    pipeline event.

### Phase 4 — Extensible tactics, backward `apply`, editor goal view, and proof admission (`C1.2`, `C6`, `C7`)

- **C1.2 (template & typed computed tactics):**
  - `tactic ... becomes ...` inside `macro` containers composes checked command
    aliases with finite nesting, open-goal preservation, unreachable-statement
    diagnostics, source-backed imports, and Core-byte equivalence to handwritten
    proofs. Core-shaped ASTs and non-command bodies are refused structurally.
  - `tactic <rule> computed by <fn>` evaluates a Cure callback via
    `MacroExpand.expand_typed`, passing captured `Syntax` arguments and a typed
    `Std.Tactic.Goal` (`Hypothesis` records, structural target/type syntax,
    authored local names, fresh opaque invocation handle). Callbacks return at
    most 256 authenticated requests from the closed checked-command vocabulary
    (or authored refusal diagnostics), with explicit `fresh(...)` hygiene
    markers. Callbacks return requests, not proof objects; editing reflected
    target data cannot alter the original checking obligation.
- **C6 (backward `apply` / `exact`):** application sessions retain immutable
  pending parents and child goals for partial global/local heads, constructors,
  and nested applications. Independent premises appear in telescope order;
  dependent domains stage after earlier witnesses close; unresolved implicit
  arguments surface as visible typed witness obligations. Ordinary source
  sequencing focuses the first premise while host `all_goals` retains broadcast
  semantics. Original parents check only after reconstructed evidence closes.
  `apply`/`exact` are contextual keywords gated on parser `proof_context`, so
  ordinary identifiers like `Std.Core.apply/2` are unaffected.
- **C7 (source-indexed goal views & VS Code panel):** `Cure.Elab.ProofState`
  captures before/after/failure states and unfinished residuals, publishing
  `:proof_state` events. An explicit ephemeral `SourceContext` (wrapping
  `Compiler.check_source`) drives actual checking-site hole observations, CLI
  output, REPL `:goals` (retaining refused submissions without installing them),
  inlay hints, and LSP `cure/proofState` (honoring cursor position in negotiated
  UTF-8/16/32 encodings and URI/version freshness with `-32801` on stale
  requests). The native VS Code `cure.goals` tree and `cure.showGoals` command
  consume these states with debouncing, cancellation, and transport-generation
  guards, validated against the real VS Code Extension Host. *(Env-only
  `Program.hole_goals/1` remains a coarse deprecated compatibility API.)*
- **Automatic proof-admission totality:** hole-free declarations executing proof
  syntax (including expanded tactics, induction, legacy `rewrite proof in body`,
  anonymous search holes, and automatic refinement discharge) require ordinary
  totality certification after body checking. Uncertified recursive evidence is
  refused with `E013` (`proof_totality_unproven`), which `@total false` cannot
  waive. Partial runtime functions remain legal; surviving development holes
  stay checkable while `E014` blocks release. Four private structural `Nat`
  helpers repair the `IntOrder` dependency cone without altering public theorem
  types or trusted termination rules.

### Phase 5 — Universe polymorphism (`C2`, U0–U7)

Implemented end-to-end per
[`2026-07-20-agda-style-universe-polymorphism-design.md`](superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md):

- **U0–U1:** characterization inventory, runtime baseline capture, and
  `Cure.Core.UniverseLevel` canonical maximum-plus level algebra (`constant`,
  sorted `[{atom, offset}]`, canonical construction, equality, ordering,
  substitution, shifting, validation, printing).
- **U2:** Core sort representation migration, NbE `LevelValue` evaluation and
  read-back, fail-closed level-atom traversal across Core walkers, and
  serialization/interface version bumps.
- **U3:** removal of `Cure.Core.Universe.ceiling/0`, unbounded trusted sorting
  and cumulativity, rigid-level `piSort` classification, and `TypeLimit`
  stratification (`Type(a) : Type(a)` and `TypeLimitN : TypeLimitN` rejected).
- **U4:** surface universe syntax (`UniverseLevel`, `universe_zero`,
  `universe_succ`, `universe_max`, `Type(l)`, `TypeN`, `TypeLimit`,
  `TypeLimitN`), LUB family sort inference (replacing the old `0..2` retry
  loop), level unification, and use-site level inference.
- **U5:** single universe-polymorphic stdlib definitions for `Equivalent`,
  `List`, `Option`, and `Sigma` across all 82 stdlib modules.
- **U6:** grade-0 erasure enforcement for universe-level binders, rejection of
  runtime-relevant level usage, and byte-identical BEAM runtime baseline output.
- **U7:** Antigen polymorphic and adversarial universe generators, canonical
  maximum-plus shrinking, and §19.6 weak-kernel sensitivity antibodies.

### Phase 3 — Declaration-driven operator fixity (`C3`)

Implemented per
[`docs/superpowers/specs/types/MASTER.md`](superpowers/specs/types/MASTER.md)
§7.3 and §7.4:

- `precedencegroup` partial order compiled to topological binding powers in
  `Cure.Compiler.Parser.FixityTable`, reporting `{:ambiguous_precedence, g1, g2}`
  for incomparable adjacent groups and `{:no_operator_meaning, op}` when a
  fixity has no function.
- `Std.Operators` (`lib/std/operators.cure`) is the sole semantic fixity
  source via `Cure.Compiler.Parser.BuiltinFixity`; static binding-power tables
  in `Cure.Compiler.Parser.Precedence` and `check_no_builtin_rebind` are
  retired.
- Transitive `use` + `@prelude` fixity assembly in
  `Cure.Compiler.Parser.FixityResolver` with `:conflicting_operator_fixity` and
  `:conflicting_precedence_group` enforcement, `DepGraph.scan_file/1`
  statement-level recovery (`FixityScan.harvest_source/3`), and
  `prelude_providers` threaded through both parsing and
  `Program.check_no_precedence_cycle/2`.
- `Printer.quoted_to_string/2` and `AlgebraFormatter.format/2` automatically
  assemble `fixity(M)` via `Printer.fixity_for_ast/2` when `:fixity` is not
  explicitly supplied, preserving declared precedence without over-parenthesising
  custom operators.

### Phase 6 — Kernel & elaborator reach ledger (`C9`, `C10`)

Every genuine item in
[`docs/superpowers/specs/kernel/MASTER.md`](superpowers/specs/kernel/MASTER.md)
§5.3 and §9 is closed:

- **C9 (`K-bug 2` — guarded-lambda recursion):** `Cure.Core.Certificate`
  (`arg_relation/2` higher-order subterm rule) certifies continuation-style
  recursion (`Bind(e, g) -> Bind(e, fn(y) -> bind(g(y), f))`) while rejecting
  diverging controls (`test/antigen/guarded_lambda_size_change_antibody_test.exs`).
- **C10 (`K-bug 1` — symmetric constructor injectivity):** `Cure.Core.Kernel`
  (`unify_one/4`) handles outer index variables symmetrically on left and right
  (`test/antigen/unify_injectivity_symmetry_antibody_test.exs`).
- **C10 (`E6-residual Variant A`):** computed-index constructors at concrete
  goals preserve the data param/index split
  (`test/antigen/simultaneous_unification_antibody_test.exs`).
- **C10 (`E10` — higher-order index arguments):** lambda-in-index lowering
  (`E10a`) plus guarded-lambda totality (`K-bug 2`) enable free-monad `bind`
  with lambda, named-function, and partial-application continuations in
  dependent index position (`test/oracle/hoidx/hoidx01_lambda_in_index.cure`,
  `test/cure/elab/e12_rewrite_delta_expose_test.exs`).
- **C10 (`E12` — `rewrite` δ-exposed targets):** `Cure.Elab.Rewrite`
  (`legacy_plan_with_expose/7` and `directed_plan_with_expose/9`) retries once
  on miss with bounded WHNF (`stuck_cases: :expose, fuel: 32`) on goal
  heads/indices without unfolding recursive calls inside stuck branches;
  transport evidence is still kernel-checked at the original goal with zero
  TCB change (`test/cure/elab/e12_rewrite_delta_expose_test.exs`).
- **C10 (`E13` — diagonal GADT `SubRefl`):** reflexive constructor index
  identification propagates subsequent refinement to the goal
  (`test/cure/elab/e12_rewrite_delta_expose_test.exs`).

*(Previously listed `E9` was falsified against Idris and `K-bug 3` was
misdiagnosed; neither is an active gap.)*

---

## 3. Scope boundaries & separate tracks

All six parity phases (`C1`–`C10`) are complete. The items below are explicit
boundaries of the delivered contracts or separate long-running tracks:

### Known scope boundaries (outside delivered fragments)

These are documented limits of the delivered phases, not hidden regressions:

- **Interface-only macro grammar publication:** source-backed imports of syntax
  and tactic macros work; loading macro grammar from compiled interfaces alone
  remains an inherited limitation shared with ordinary syntax macros.
- **Unsaved sibling provider overlays:** the editor checks an unsaved active
  consumer against saved source providers (invalidating on provider save);
  unsaved sibling provider overlays are outside the current contract.
- **Arithmetic automation:** `by omega` covers the bounded non-strict
  `Std.Proof.IntOrder` reconstruction fragment; a general Farkas
  checker-to-goal soundness theorem and unrestricted Presburger automation are
  not implemented.
- **Metaprogramming:** `computed by` is a bounded, authenticated checked-request
  protocol (≤ 256 operations), not unrestricted `Lean.Meta` metaprogramming.

### Separate tracks (not Lean parity)

Tracked outside this document so source-level parity is never conflated with
metatheory or backend correspondence:

- **Agda metatheory & executable refinement (`G6`, `G8`, `G11`):** executable
  refinement of `Eval`/`Quote`/`Conv`, integrated η, `unbound` worker redesign,
  dependent-signature migration, erasure simulation, BEAM lowering, semantic
  totality (`M11`), and kernel-acceptance → certificate / producer
  correspondence. See [`proof/README.md`](../proof/README.md) and
  [`proof/PLAN.md`](../proof/PLAN.md).
- **Second checking backend (`G7`):** optional `lean4lean` backend via forgetful
  projection (witnesses the dependent skeleton, not QTT multiplicities;
  [`docs/superpowers/specs/kernel/MASTER.md`](superpowers/specs/kernel/MASTER.md)
  §1.1 decision 6). Not implemented; no Lean toolchain dependency is added.

---

## 4. Parity corpus & verification

[`test/lean4_parity/corpus.exs`](../test/lean4_parity/corpus.exs) pins **what
Cure currently accepts or rejects** through the real compiler pipeline
(`mix test test/lean4_parity_test.exs`). Every `:reject` pin carries a `:reason`
distinguishing deliberate safety boundaries from open reach gaps.

**Current inventory: 47 cases (27 accept, 20 reject)**

The corpus retains stable historical `g1`–`g11` IDs mapped to the `C1`–`C10`
register below:

| Corpus gap | Register | Cases | Accept | Reject | Current meaning |
|---|---|---:|---:|---:|---|
| `g1` | **C7** | 2 | 0 | 2 | Deliberate refusal pins for unfinished proofs (even with goal display) |
| `g2` | **C1** | 16 | 9 | 7 | Goal API, templates, computed tactics, `apply`, `induction` + safety refusals |
| `g3` | **C5, C9** | 4 | 3 | 1 | Certified recursive computation + neutral right-identity refusal pin |
| `g4` | **C4** | 4 | 3 | 1 | Explicit `@simp`, quantified ambient rules + looping-rule refusal |
| `g5` | **C1.3** | 14 | 6 | 8 | `search`, `assumption`, `positivity`, `decide`, `omega` + refusal controls |
| `g9` | **C2** | 5 | 4 | 1 | `Type`, `UniverseLevel`, `Type37`, `TypeLimit` accepted; `Type(0)` rejected (Phase 5 U4) |
| `g10` | **C4** | 2 | 2 | 0 | `simp?` progress reporting |
| `g6`, `g7`, `g8`, `g11` | *Metatheory* | 0 | 0 | 0 | No source pins by design (enforced by `test/lean4_parity_test.exs`) |

### Key test suites by phase

- **Phase 1 (C4/C5/C8):** `test/cure/elab/simp_set_test.exs`,
  `test/cure/diagnostic/simp_declaration_test.exs`,
  `test/cure/elab/proof_ergonomics_test.exs`,
  `test/cure/elab/tactic_integration_test.exs`.
- **Phase 2 (C1.1/C1.3):** `test/cure/elab/tactic_test.exs`,
  `test/cure/elab/solver_test.exs`, `test/cure/compiler/solver_test.exs`,
  `test/cure/elab/omega_pipeline_test.exs`, `test/cure/elab/omega_proof_test.exs`,
  `test/cure/elab/omega_solver_test.exs`,
  `test/cure/elab/induction_command_test.exs`.
- **Phase 4 (C1.2/C6/C7/Admission):** `test/cure/elab/tactic_macro_test.exs`,
  `test/cure/elab/tactic_macro_audit_test.exs`,
  `test/cure/compiler/tactic_macro_audit_test.exs`,
  `test/cure/elab/computed_phase4_test.exs`,
  `test/cure/elab/application_session_test.exs`,
  `test/cure/elab/phase4_tactics_test.exs`,
  `test/cure/elab/phase4_closure_audit_test.exs`,
  `test/cure/elab/proof_state_integration_test.exs`,
  `test/cure/elab/source_context_test.exs`,
  `test/cure/elab/proof_admission_test.exs`,
  `test/cure/elab/int_order_totality_test.exs`,
  `vscode-cure/src/test/hostSuite.ts`.
- **Phase 3 (C3):** `test/cure/compiler/fixity_propagation_test.exs`,
  `test/cure/compiler/fixity_resolver_test.exs`,
  `test/cure/compiler/fixity_table_test.exs`,
  `test/cure/compiler/builtin_fixity_prelude_test.exs`,
  `test/cure/compiler/printer_precedence_test.exs`,
  `test/cure/std/operators_module_test.exs`.
- **Phase 5 (C2):** `test/cure/core/universe_level_test.exs`,
  `test/cure/core/universe_polymorphism_characterization_test.exs`,
  Antigen universe assays (`lib/antigen/generators/universes.ex`).
- **Phase 6 (C9/C10):** `test/antigen/guarded_lambda_size_change_antibody_test.exs`,
  `test/antigen/unify_injectivity_symmetry_antibody_test.exs`,
  `test/antigen/simultaneous_unification_antibody_test.exs`,
  `test/cure/elab/e12_rewrite_delta_expose_test.exs`.
- **Parity corpus:** `test/lean4_parity_test.exs`.

---

## 5. Non-negotiable invariants

1. **No Lean port:** Final Core stays Idris/Agda-shaped.
2. **No new postulates, holes, or bypasses:** the Agda check-bypass allowlist
   stays empty; do not add `propext` or `Classical.choice` to match Lean's axiom
   list.
3. **Never widen the TCB to fix an elaboration or conversion failure:** kernel
   changes require explicit hard-stop review.
4. **Automation stays untrusted-and-checked:** tactics and solvers emit Core
   re-checked by the kernel at the original expected goal.
5. **Never let `simplify` trust host evaluation:** only certified-total
   definitions unfold under δ.
6. **Preserve `rewrite`'s single-occurrence default:** multi-occurrence
   rewriting stays opt-in (`all`).
7. **Keep `Proof/*Examples.agda` fixtures:** they are non-vacuity evidence for
   parameterized metatheory theorems.
8. **A flipped parity pin is the review:** when behavior changes, flip the pin
   in `test/lean4_parity/corpus.exs` and update this document in the same commit.
   Never flip a deliberate negative safety pin just to raise acceptance counts.

---

## 6. How to update this document

- When closing **C3** or an item in **C9–C10**: move it from §3 to §2, check off
  its Definition of Done box in §1, and update the status table.
- When adding or flipping a pin in `test/lean4_parity/corpus.exs`: update the
  counts and gap row in §4 in the same commit.
- Keep separate metatheory/correspondence progress in `proof/PLAN.md`, not here.
