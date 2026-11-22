# Path to Lean 4 — Execution Plan

**Status:** historical execution companion to [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md).
**Scorecard:** [`LEAN4_PARITY_STATUS.md`](LEAN4_PARITY_STATUS.md)
**Corpus:** [`test/lean4_parity/`](../test/lean4_parity/)

**Phase-number correction (2026-11-21):** the sequence below differs from the
authoritative `PATH_TO_LEAN4.md` §8. Current Phase 1 is C4/C5/C8, implemented
within its stated gates. Current Phase 2 delivers C1.1 infrastructure and
C1.3 solver clients but not the reusable-induction-command adequacy gate.
Use the scorecard for current measurement. Certified unfolding required no TCB
change, and `plus(n, Z()) = n` is an induction theorem, not a missing reduction.
Later-phase descriptions and baseline findings below are retained historically,
not as assertions about today's implementation.

**Historical Phase 3 (audited 2026-11-22):** contextual `tactic ... becomes`
templates are implemented. This was a command-composition prerequisite, not
the full goal-inspecting interface. The later continuation adds typed
`computed by` / `Std.Tactic` callbacks and per-command server/REPL views.
Authoritative Phase 3 remains C3 operator fixity; authoritative Phase 4 remains
partial because premise-generating `apply` and the VS Code goal panel are open.
See the scorecard and §4 below for the precise boundary and audit corrections.

---

## 0. Relationship to the other documents

The documents describing this work have distinct roles and must not
be conflated:

| Document | Role |
|---|---|
| [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md) | **Authoritative analysis.** What parity means, what Cure already has, the ranked gap list (C1–C10), the sequencing constraint, and the non-goals. |
| **This document** | **Execution.** How to sequence and *measure* the work: phases, gates, files, and what counts as done. |
| [`LEAN4_PARITY_STATUS.md`](LEAN4_PARITY_STATUS.md) | **Measurement.** The living scorecard: baseline counts, axis scores, gap status, corpus pin inventory. |
| [`LEAN4_MIGRATION_PLAN.md`](LEAN4_MIGRATION_PLAN.md) | **Superseded.** Withdrawn by `PATH_TO_LEAN4.md` §9; retained as historical record only. |

**Where this document disagrees with `PATH_TO_LEAN4.md`, that document wins.**
It was written against a fuller reading of `docs/MACROS.md`,
`docs/superpowers/specs/types/MASTER.md` and
`docs/superpowers/specs/kernel/MASTER.md`, and it corrects several claims an
earlier audit (including this plan's first draft) got wrong.

### Corrections this plan absorbs

These were wrong in the first draft of this plan and are corrected here:

1. **`apply`/`exact` are not missing.** An earlier C6 description obscured that
   the parser already carries `proof_application` nodes for both (see
   `lib/cure/compiler/parser.ex`, `parse_proof_application/3`). The real
   remaining work is specifically generating premise goals and reconstructing
   checked evidence for an under-applied theorem. Closing `apply` alone does
   not implement that capability.
2. **`rewrite`'s single-occurrence default is a real gap (C8), not a feature.**
   The first draft treated `E111`-on-multiple-matches as correct strictness. It
   is a deliberate choice, but it is *tedium*, and `PATH_TO_LEAN4.md` §11
   forbids changing the default — so the fix is an opt-in `all` selector (which
   the parser already gained), not a default flip.
3. **The Agda development is not the parity target.** Parity work happens in
   `lib/cure/elab/` and `lib/std/`. The `proof/` tree is the *kernel's*
   metatheory and is orthogonal to user-facing proof ergonomics.

### Findings from executing Phase 0

Two **parser regressions** were found and fixed while building the corpus. Both
are contextual-keyword bugs in the `apply`/`exact` proof commands (the commands
`PATH_TO_LEAN4.md` C6 describes): a soft keyword claimed a position where the
word was a *name*, and each broke a real stdlib module.

| Word | Following token | Real meaning | Broke |
|---|---|---|---|
| `exact` | `->` | a bound match variable (`IsSingleCharacter(_, _, exact) -> match exact`) | `lib/std_deps/regex/regex_language.cure` — `E094 closing_delimiter_has_no_opener` |
| `exact` | `in` | the proof name in `rewrite exact in body` | `lib/std_deps/regex/regex_proof.cure` — `E094 rewrite_in_missing` |

Both are now excluded by an **allowlist** in `proof_application_ahead?/1` — the
keyword is claimed only when the next token can begin an expression — with
regression tests in `test/cure/compiler/dependent_proof_surface_test.exs`. The
general lesson for Phases 2–4: **every contextual keyword added by the tactic work
must be tested against the positions where its spelling is an ordinary
identifier.** That is the same discipline `docs/MACROS.md` §3 already applies to
`have`, `rewrite`, `simplify`, `induction` and `proof`.

**The `apply` ambiguity is RESOLVED (not deferred to Phase 2).**

`lib/std/core.cure:68` defines a public `fn apply(f, x)`, so `apply` is
simultaneously a stdlib function and a contextual proof command. No lookahead can
separate them — `apply(f, x)` and `apply some_proof` are both "`apply` followed by
an expression-starting token".

The first draft of this plan proposed deferring the fix to Phase 2. That was
wrong: the fix is small and belongs with the parser work.

**The resolution is a parser-state flag, not more lookahead.** `%Parser{}` gained
`proof_context: false`, set to `true` only while parsing:

* the statements of a `because` justification block (`parse_chain_justification/2`), and
* an `induction` case body (`parse_induction_cases/3`).

`proof_application_ahead?/1` now returns `false` whenever `proof_context` is
false, so outside command position `apply`/`exact` are ordinary identifiers by
construction. The token allowlist is retained as a *secondary* check, because a
justification statement may itself be an ordinary expression rather than a
command.

This makes the parser agree with its only consumer: the elaborator reads
`proof_application` nodes exclusively from `ProofGoal.command/2`, i.e. only in
command position.

Both directions are pinned in `test/cure/compiler/dependent_proof_surface_test.exs`:
`apply(f, apply(f, x))` outside a proof block must parse as a **call** and must
contain no `proof_application` node; `apply ih` inside a `because` block must
produce one.

The corpus uses explicit `use Std.Equivalent` where it needs the module's
combinators. Whether a name is ambient must be checked through the canonical
prelude and module-visibility path; a group tag or the absence of a local
`@prelude` decorator alone is not sufficient evidence.

---

## 1. What this plan adds

`PATH_TO_LEAN4.md` specifies *what* to build. It has no measurement layer, so
"how far are we?" is unanswerable from it. This plan adds exactly two things:

1. **A parity corpus** (`test/lean4_parity/`) that pins current accept/reject
   behaviour, so every reach change is a visible diff.
2. **A phase sequence with gates**, ordered by the risk/impact rule in §3.

Nothing here changes Cure's semantics. The corpus is observation only.

---

## 2. The measurement model

### 2.1 Pins, not aspirations

A corpus case records **what Cure does today**, never what it should do:

```elixir
parity_case(
  id: "g3-reflexive-recursive-unfolding",
  gap: :g3,
  axis: :l2,
  title: "reflexive does NOT close a goal needing a recursive definition unfolded",
  expect: :reject,
  reason: "delta-unfolding is gated behind a totality certificate ...",
  source: "..."
)
```

A `:reject` pin **requires** a `:reason`. That reason is the difference between
"deliberate exclusion" and "reach gap we intend to close" — and a future reader
needs that distinction more than they need the pin itself.

When a phase widens reach, the pin flips `:reject` → `:accept` **in the same
commit** that widens it. That diff is the review. This is how invariant 8
("preserve older artifact bytes unless a reviewed semantic change requires
migration") is enforced mechanically rather than by discipline.

### 2.2 Gap numbering

The corpus uses the **G1–G11** register from the audit (see
`LEAN4_PARITY_STATUS.md` §3), which is finer-grained than `PATH_TO_LEAN4.md`'s
C1–C10. The mapping:

| Audit gap | `PATH_TO_LEAN4.md` | Note |
|---|---|---|
| G1 (goal introspection) | **C7** | also prerequisite for C1 |
| G2 (user tactics) | **C1** | the architectural gap |
| G3 (δ-reach) | **C5**, **C9** | C9 is the guarded-lambda certificate bug |
| G4 (`@[simp]`) | **C4** | |
| G5 (automation as tactics) | **C4**/C1 clients | bounded checked clients delivered; not unrestricted arithmetic automation |
| G6 (Agda↔kernel) | — | proof-side; not a parity item |
| G7 (lean4lean backend) | — | locked decision 6; not a parity item |
| G8 (emitter) | — | out of scope |
| G9 (universe polymorphism) | **C2** | |
| G10 (`simp?`) | **C4** | folded into the simp work |
| G11 (`unbound`) | — | proof-side |

**G6, G7, G8 and G11 are not parity items.** They belong to the kernel's
metatheory track (`proof/PLAN.md`) and are tracked in the scorecard only so the
two tracks are not confused. `test/lean4_parity_test.exs` asserts they have no
source pins, so the separation is enforced, not merely documented.

---

## 3. Sequencing rule

The historical plan used **C1 before C4/C6/C7** as a sequencing heuristic.
The current dependency is more precise: the evidence-preserving C1.1 goal API
supports computed tactics, backward application and goal views; full C1.2 was
not a prerequisite for the already-delivered C4/C5/C8 features.

This plan adds a second rule, about risk:

> **Land every zero-TCB phase before the first TCB-adjacent one.**

The reason is that the zero-TCB phases (goal display, tactic monad, tactic
macros, simp sets) are cheap, reversible, and make the expensive phases
*measurable*. Doing δ-reach (G3/C5) first would be the classic mistake: it looks
like the biggest win, it is the biggest risk, and without a goal API you cannot
tell whether it actually helped.

Historical ordering: **0 → 1 → 2 → 3 → 4 → (5 | 8 in parallel) → 6 → 7 → 9 → 10.**
This is not an alternative to the authoritative phase numbers and gates.

---

## 4. Phases

The phase numbers below are historical. Each delivered slice must still meet
the corresponding current gate; a similarly named historical phase does not
establish authoritative Phase 4 completion.

### Phase 0 — Baseline and measurement

**Scope.** Record the baseline; build the corpus; confirm the CI guards.

**Status: complete.** Findings:
- `.github/workflows/proof.yml` **already existed** and already runs
  `./proof/check.sh`, `check-postulates.sh`, `test_hygiene.py` and
  `check-hygiene.py`. No CI work was needed.
- `ci.yml` already runs `mix format --check-formatted` and `mix credo --strict`.
- Corpus and scorecard created.

**Gate.** `mix test test/lean4_parity_test.exs` green; every pin matches
recorded behaviour.

**Files.** `test/lean4_parity/parity_case.exs`, `test/lean4_parity/corpus.exs`,
`test/lean4_parity_test.exs`, `docs/LEAN4_PARITY_STATUS.md`.

---

### Phase 1 — Goal-state introspection (G1 / C7)

**Scope.** Make remaining goals visible. `PATH_TO_LEAN4.md` C7; prerequisite for
C1.

**Delivered boundary after the continuation.** `ProofGoal` remains the single
checked goal state; no incompatible `%Cure.Elab.Goal{}` representation is added.
`ProofState` captures before/after/failure observations and the residual of an
unfinished block, and publishes `:proof_state` events. The LSP selects by cursor
position in the negotiated UTF encoding; REPL `:goals` retains refused
definition submissions without installing them as executable definitions.

Actual nested-hole obligations are observed where the expected type and named
context are available, not reconstructed from a function's return type.
Legacy `Program.hole_goals/1` and existing hole inlay hints still use that older
summary and are not claimed equivalent to the new views. A VS Code goal-panel
consumer remains open.

**Gate discipline.** An unfinished `because` proof remains an elaboration
refusal even when its residual goal is successfully displayed. Do not flip a
refusal pin to acceptance merely because the diagnostic is now useful.

**TCB.** None.

**Files.** `lib/cure/elab/proof_goal.ex` (goal struct), `lib/cure/pipeline/events.ex`,
`lib/cure/repl/`, `lib/cure/lsp/`, `lib/cure/diagnostic/`.

---

### Phase 2 — `Cure.Elab.Tactic` monad (G2 / C1, part 1)

**Scope.** Extract the hard-coded proof commands into a reusable API.

**Work.**
1. `lib/cure/elab/tactic.ex`: `{:ok, %Tactic.Result{goals: ..., solutions: ...}}`
   or `{:error, reason}`. Solutions retain checked evidence keyed by original
   goal identity; goal-list-only results are legacy inspection projections.
2. Combinators: `seq/2`, `or_else/2`, `repeat/1`, `repeat_until_fail/1`,
   `try_/1`, `focus/2`, `all_goals/1`.
3. Re-point `simplify`, `rewrite`, `induction`, `have`, `because`,
   `apply`/`exact` as clients. **Byte-identical diagnostics** is the gate.

**Remaining adequacy gate.** Preserve the existing `E109`–`E115` compatibility
tests and demonstrate all six original forms as genuine goal-API clients.
Ordinary induction still has declaration-level recursive lowering; accepting
an induction AST or invoking another tactic in an induction arm does not
demonstrate a reusable induction command.

**TCB.** None.

**Files.** `lib/cure/elab/tactic.ex` (new), `lib/cure/elab/proof_goal.ex`,
`lib/cure/elab/rewrite.ex`, `test/cure/elab/tactic_test.exs` (new).

---

### Phase 3 — template tactic macros (historical numbering)

**Implemented boundary:** a library defines a contextual `tactic ... becomes`
rule composing existing proof commands. That template form does not receive a
goal value; the subsequent authoritative Phase 4 continuation implements the
separate typed `computed by` / `Std.Tactic` protocol. Induction templates remain
rejected until their recursive lowering is wired to this API; invoking tactics
in ordinary induction arms is supported.

**Audit corrections (2026-11-22):**
- Scripts now return transformed open goals to caller commands and report the
  true residual goal if the entire justification ends open. Extra commands
  after closure produce the normal unreachable-statement diagnostic.
- Closed solutions and traces are retained exactly once. The earlier claim
  that `Tactic.run_all(Result)` discarded evidence was incorrect.
- Finite aliases, forward references and distinct overloads compose; recursive
  alias chains are refused. Imported templates keep provider helper grammar.
- Contextual dispatch applies only to command heads, not nested evidence
  operands. Structured literal mismatches report errors rather than crashing.
- Printer round-trips retain declarations, invocations, optional/repeated
  syntax, rewrite-all, and explicit proof applications.
- Exact example pins work for single, nested and sequence tactics. Type-only
  pins execute at the stated goal and refuse false goals. Explain obligations,
  capture-category checks and authored diagnostics remain enforced.

**Measured gates:** a test library actually invokes its tactics; resulting
proof definitions kernel-check. Audit tests compare Core bytes to handwritten
expansions and refuse altered-original-goal closure, actual Core-shaped ASTs,
malformed commands and empty blocks. The old induction acceptance fixture was
vacuous for tactic invocation and has been repaired.

The `g2-tactic-rule-kind` corpus pin compiles a theorem containing a tactic
invocation through elaboration and the kernel. It measures reach, not an
independent soundness theorem. Unit-level kernel and negative controls measure
specific safety properties; neither suite proves universal soundness.

**Inherited limit:** interface-only macro grammar loading fails for ordinary
syntax macros too. Source-backed tactic imports are tested; artifact grammar
publication is not redesigned in this slice.

**TCB:** unchanged. Existing proof commands produce evidence checked against
the original goal; no new kernel constructors or proof postulates.

---

### Phase 4 — Simp sets and tactic automation (G4, G5, G10 / C4)

**Historical scope.** Close the gap from "libraries exist" to checked tactic
clients. This is not the C1.2/C6/C7 authoritative Phase 4 closure gate.

**Delivered slices.**
1. `@simp` / `@lemma(:simp)` use Cure's decorator syntax and checked quantified
   rules. Explicit non-decreasing or variable-duplicating declarations are
   rejected; safe legacy `@lemma` behavior remains compatible.
2. Search, local-only assumption, positivity and decision clients have explicit
   supported fragments. `by omega` reconstructs ordinary Core for non-strict
   integer comparisons using local evidence, reflexivity, transitivity,
   addition and literal-natural scaling. Its limits are 128 local slots,
   depth 12, 512 reconstruction steps and scalar 1024. Strict/equality,
   nonlinear, unreconstructed and closed non-reflexive literal goals refuse.
3. `simp?` preserves simplification evidence and reports only the current
   successful invocation's progress, including explicit/adaptation trace
   entries and actual source metadata. It does not list every registered rule.

**Arithmetic boundary.** The certified `check_lia_candidate` Boolean checker
and untrusted Farkas producer/reifier are not a theorem from successful
checking to the original proposition. Goal admission additionally requires
checked evidence reconstruction. General checker-to-goal soundness and
complete Presburger automation are not delivered.

**Authoritative Phase 4 continuation.** Typed computed callbacks inspect real
`Goal`/`Hypothesis` values through `MacroExpand.expand_typed`; at most 256
authenticated operations run through existing checked commands. Explicit fresh
markers preserve generated-binder hygiene. Source-backed imports and
original-goal controls accompany the per-command server/REPL views described
above. Premise-generating `apply`, reusable induction-command adequacy, and the
VS Code goal panel remain open.

**TCB.** None — all automation is untrusted-**and**-checked.

**Files.** `lib/cure/elab/simp_set.ex`, `lib/cure/elab/tactic/*`,
`lib/cure/elab/proof_state.ex`, `lib/cure/elab/omega/*`,
`lib/std/tactic.cure`, `lib/std/proof_linear_arithmetic*.cure`,
`docs/PROOFS.md` §3.4 and §3.9.

---

### Phase 5 — δ-reach widening (G3 / C5, C9) — **high risk**

**Scope.** Let `simplify`/conversion see through recursive definitions where it
is *sound* to.

**Do not start until Phases 0–4 are landed** and the corpus can measure the
change.

**Work — widen what gets *certified*, never what gets *unfolded*.**
1. `Eval.eval({:global, name})` → `{:nglobal, name}` and the sole δ-site
   `Normalise.unfold_certified_head/3` stay exactly as they are
   (`docs/SOUNDNESS.md` §3.2).
2. Follow the guarded-lambda recursion entry (`kernel/MASTER.md` §5.3,
   K-bug 2) and its current hard-stop approval requirements. This historical
   plan is not authorization for a new TCB change.
3. Land order-dependent constructor injectivity (K-bug 1) — completeness only.
4. Extend size-change to well-founded/lexicographic descent.
5. Extend `simplify`'s rule set to generated defining equations for *certified*
   functions (`docs/PROOFS.md` §4) — the safe analogue of Lean's `rfl`-after-`whnf`.

**Corrected gate.** A computational goal such as `plus(Z(), plus(Z(), n)) = n`
closes through certified reduction. The old neutral `plus(n, Z()) = n` gate was
incorrect: that theorem needs induction or a lemma in Lean too. Every actual
reach change needs a justified corpus flip. **No postulate, bypass, or
unreviewed kernel rule.**

**TCB.** Certified unfolding already exists; kernel-reach changes require their
own current approval and validation, not historical approval by implication.

**Files.** `lib/cure/core/certificate.ex`, `lib/cure/core/size_change.ex`,
`lib/cure/core/unify.ex`, `lib/cure/elab/proof_goal.ex`.

---

### Phase 6 — Agda↔kernel correspondence (G6) — metatheory track

**Scope.** Close the gap between "soundness of the specification" and
"soundness of `Cure.Core.Kernel`."

**This is `proof/PLAN.md`'s M0 → M2 → M4 → M6 sequence, not a parity item.**
`proof/PLAN.md` §4 warns explicitly against adding more examples while
postponing it. Earlier module-growth counts were historical observations, not
a refreshed metatheory inventory or evidence of correspondence completion.

**Gate.** A bounded release-admission theorem with an honest TCB
(`proof/PLAN.md` §11 gate G1).

**TCB.** None (proof-side).

---

### Phase 7 — `lean4lean` second backend (G7)

**Scope.** Locked decision 6: a second checking backend via forgetful
projection, witnessing the dependent skeleton only.

**Gate.** The projection is mechanical and the second checker agrees on a
nonempty corpus.

**TCB.** None — it is a *checker*, not a toolchain dependency.

---

### Phase 8 — Universe polymorphism (G9 / C2)

**Scope.** Execute the approved U0–U7 design. `PATH_TO_LEAN4.md` §11: **do not
redesign it — execute it.**

**Gate.** The spec's §21 completion criteria: `Type : Type` and
`TypeLimit : TypeLimit` unrepresentable; one polymorphic definition works at
arbitrary levels; Antigen sensitive to weakened level rules.

**TCB.** **Yes** — explicit canonical levels, no level metavariables.

---

### Phase 9 — Emitter/BEAM (G8)

**Scope.** `docs/SOUNDNESS.md` §5.3 assumption 3: emission is assumed faithful.
Out of scope for parity; tracked so the assumption is never silently promoted.

---

### Phase 10 — Semantic totality (G11)

**Scope.** `proof/PLAN.md` M11. `BodiesFinal` is body finality, **not**
termination. Independent of parity.

---

## 5. Non-negotiables

Carried from `PATH_TO_LEAN4.md` §11 and `proof/PLAN.md` §3. Any proposal
violating one is rejected:

1. Never add a postulate, hole, or termination/positivity bypass. The bypass
   allowlist stays empty.
2. Never widen the TCB to fix an elaboration or conversion failure.
3. Automation stays untrusted-**and**-checked.
4. Preserve the original expected goal; normalize to establish conversion.
5. Do not port anything to Lean. Final Core stays Idris/Agda-shaped.
6. Do not add `propext`/`Classical.choice` merely to match another prover's axiom
   inventory. Counts alone do not establish comparative soundness.
7. Do not change `rewrite`'s single-occurrence default — add an opt-in selector.
8. Do not let `simplify` declare terms equal because the host computed so.
9. Do not delete the `Proof/*Examples.agda` fixtures — they are the
   non-vacuity evidence.
10. A flipped parity pin is the review of a semantic change.

---

## 6. Definition of done

Per `PATH_TO_LEAN4.md` §10, parity is reached when a user can write a tactic
that inspects the goal (C1), `Type(l)` is polymorphic (C2), operators have
declaration-driven fixity (C3), `@[simp]` + certified unfolding close
computational goals (C4/C5), backward reasoning works (C6), goals are visible at
the cursor (C7), and the open reach ledger is closed or explicitly pinned (C9,
C10).

The original effort estimate was historical, not a measured remaining schedule.
Use the authoritative remaining gates and fresh integration evidence instead.

**A conditional result with an openly named unverified adapter must never be
labelled universal refinement.** That distinction is the most important honesty
constraint in this document and in `proof/PLAN.md`.
