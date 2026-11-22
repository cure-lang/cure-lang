# Path to Lean 4 — Execution Plan

**Status:** historical execution companion to [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md).
**Scorecard:** [`LEAN4_PARITY_STATUS.md`](LEAN4_PARITY_STATUS.md)
**Corpus:** [`test/lean4_parity/`](../test/lean4_parity/)

**Phase-number correction (2026-11-21):** the sequence below differs from the
authoritative `PATH_TO_LEAN4.md` §8. Current Phase 1 is C4/C5/C8 and current
Phase 2 is C1.1/C1.3; both are implemented. Use the scorecard for current
measurement. In particular, certified unfolding required no TCB change, and
`plus(n, Z()) = n` is an induction theorem, not a missing reduction.
Later-phase descriptions and baseline findings below are retained historically,
not as assertions about today's implementation.

**Phase 3 (2026-11-22):** `tactic` macro rules are implemented — a library can
define a new proof command, expanding only to a closed vocabulary of existing
steps. See §4 Phase 3 for the findings, including two pre-existing defects the
work exposed.

---

## 0. Relationship to the other documents

Three documents now describe this work. Their roles are distinct and must not
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

1. **`apply`/`exact` are not missing.** `PATH_TO_LEAN4.md` C6 lists them as a
   gap; the parser already carries `proof_application` nodes for both (see
   `lib/cure/compiler/parser.ex`, `parse_proof_application/3`). The real
   remaining work is backward-reasoning *ergonomics*, not the commands.
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

**A documentation inaccuracy was also found:** `docs/PROOFS.md` §1 states that
"`Equivalent` and `reflexive` are preluded". They are not — `lib/std/equivalent.cure`
carries `@group(:core)` but no `@prelude` marker, so `use Std.Equivalent` is
required. The corpus uses the explicit `use` throughout.

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
| G5 (automation as tactics) | **C4**/C1 clients | libraries exist; tactics don't |
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

`PATH_TO_LEAN4.md` §2 states the critical constraint: **C1 must land before C4,
C6 and C7 can be built well — all three are clients of a goal API.**

This plan adds a second rule, about risk:

> **Land every zero-TCB phase before the first TCB-adjacent one.**

The reason is that the zero-TCB phases (goal display, tactic monad, tactic
macros, simp sets) are cheap, reversible, and make the expensive phases
*measurable*. Doing δ-reach (G3/C5) first would be the classic mistake: it looks
like the biggest win, it is the biggest risk, and without a goal API you cannot
tell whether it actually helped.

Ordering: **0 → 1 → 2 → 3 → 4 → (5 | 8 in parallel) → 6 → 7 → 9 → 10.**

---

## 4. Phases

Each phase names its gate. A phase is not done until its gate passes.

### Phase 0 — Baseline and measurement ✅

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

**Work.**
1. Promote the existing `:hole_goal` pipeline event into a first-class
   `%Cure.Elab.Goal{type, context, provenance, id}`.
2. Emit a `:proof_state` event after each proof step in a `because` block,
   carrying the ordered remaining-goal list.
3. Surface it in the REPL (`:goals`), the LSP (`cure/proofState`), and the
   terminal (print remaining goals before `E110`/`E112`).

**Gate.** An open `because` block reports *which* goal is open, with type and
context, in all three surfaces. The corpus pin `g1-open-because-block` flips to
`:accept` only when the goal list is part of the diagnostic.

**TCB.** None.

**Files.** `lib/cure/elab/proof_goal.ex` (goal struct), `lib/cure/pipeline/events.ex`,
`lib/cure/repl/`, `lib/cure/lsp/`, `lib/cure/diagnostic/`.

---

### Phase 2 — `Cure.Elab.Tactic` monad (G2 / C1, part 1)

**Scope.** Extract the hard-coded proof commands into a reusable API.

**Work.**
1. `lib/cure/elab/tactic.ex`: result type
   `{:ok, [Goal.t()]} | {:ok, []} | {:error, Diagnostic.t()}` — tactics return
   *remaining* goals, so `[]` means closed (Lean's shape).
2. Combinators: `seq/2`, `or_else/2`, `repeat/1`, `repeat_until_fail/1`,
   `try_/1`, `focus/2`, `all_goals/1`.
3. Re-point `simplify`, `rewrite`, `induction`, `have`, `because`,
   `apply`/`exact` as clients. **Byte-identical diagnostics** is the gate.

**Gate.** Every existing `E109`–`E115` test passes unchanged; no proof command
remains hard-coded in the elaborator.

**TCB.** None.

**Files.** `lib/cure/elab/tactic.ex` (new), `lib/cure/elab/proof_goal.ex`,
`lib/cure/elab/rewrite.ex`, `test/cure/elab/tactic_test.exs` (new).

---

### Phase 3 — `tactic` macro rules (G2 / C1, part 2)

**Scope.** A library can define a new proof command. This converts L3 from
closed to open.

**Status: complete.** Findings:

- The gate is met by a TEST library, not the stdlib:
  `test/cure/elab/tactic_macro_test.exs` defines tactics in its fixtures and
  closes real goals with them, including in an `induction` case body.
- **The "expands to `Tactic` combinators, never to Core terms" requirement is
  structural, not disciplinary.** A template is Cure source and cannot name an
  Elixir function, so the rule produces a `tactic_script` node whose body is
  classified against a closed vocabulary (`Cure.Elab.Tactic.Step`). The
  whitelist fails closed: an unknown node is rejected, so a Core term, a bare
  proof expression, a lambda, or a `match` is refused by construction rather
  than by enumeration.
- **Composition is `seq` only.** `or_else`/`try_` would swallow failures;
  `repeat` would make step counts depend on a progress heuristic;
  `focus`/`all_goals` are vacuous while every command is single-goal.
- **Validation must run before body elaboration.** The first implementation
  checked tactic expansions inside `MacroValidate.check_program/2`, which runs
  *after* `elaborate_declarations/3` — so a bad tactic failed first at its use
  site with an unrelated `wrong_justification`, and the offending rule was never
  blamed. The check now runs in `check_declarations/1` (pure structure, no
  environment needed).
- **A tactic keyword is contextual**, exactly like `apply`/`exact`: claimed only
  in command position, an ordinary identifier elsewhere. A library may still
  define and call `fn close(x)`. Pinned in both directions in
  `test/cure/compiler/dependent_proof_surface_test.exs`.
- **Two pre-existing defects were exposed and fixed:** `parse_solver/3` used
  `String.to_existing_atom/1` on `"decide"`, which crashes in a fresh VM where
  the atom does not yet exist; and a tactic `example` pin compared the
  `tactic_script` wrapper rather than the expanded body.
- A tactic body may be a single command or an indented SEQUENCE. `becomes`
  takes one expression in every other rule kind (`docs/MACROS.md` §13); a tactic
  is the deliberate exception, because composing steps is its entire purpose.

**Gate.** Met. A test library defines a tactic macro and closes a real goal.
Negative controls: a tactic emitting a Core node is rejected (`E092`
`invalid_tactic_expansion`); an unexplained `fail`/keyword point is `E092`
`missing_diagnosis`; an unpinned tactic under `explain` is `E092`
`rule_unpinned`; a tactic that leaves the goal open is an unfinished
justification naming the residual goal.

**TCB.** None by construction — every step is `Tactic.command/1`, which
re-checks its evidence at the original goal.

**Files.** `lib/cure/compiler/parser.ex`,
`lib/cure/compiler/macro_validate.ex`, `lib/cure/elab/tactic/step.ex` (new),
`lib/cure/elab/tactic/script.ex` (new), `lib/cure/elab/proof_goal.ex`,
`lib/cure/elab/proof_chain.ex`, `lib/cure/diagnostic/adapter/macro.ex`,
`test/cure/elab/tactic_macro_test.exs` (new), `docs/MACROS.md` §2.1.

---

### Phase 4 — Simp sets and tactic automation (G4, G5, G10 / C4)

**Scope.** Close the gap from "libraries exist" to "tactics use them."

**Work.**
1. `@[simp]` attribute on `@lemma`, building a global priority-ordered set.
   `simplify` with no arguments consults it; `using [rules]` stays explicit.
   **Orientation check mandatory** — a non-decreasing equation is skipped, not
   looped.
2. Tactic wrappers over the existing sound libraries: `decide`
   (`Std.Proof.IntMath`), `positivity` (`solver_positivity`), `omega`
   (`Std.Proof.LinearArithmetic`), `assumption`.
3. `simp?` — report which lemmas fired (G10).

**Gate.** `simplify` closes a goal using only `@[simp]` lemmas from a `use`d
module; `omega` discharges a linear goal with a kernel-checked proof object;
`simp?` names the lemmas. Negative: a looping orientation is rejected; an
out-of-fragment `omega` goal returns `Unknown`.

**TCB.** None — all automation is untrusted-**and**-checked.

**Files.** `lib/cure/elab/proof/simp_set.ex` (new), `lib/cure/elab/tactic/*`,
`lib/std/proof_linear_arithmetic*.cure`, `docs/PROOFS.md` §3.4.

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
2. Land the guarded-lambda recursion fix (`kernel/MASTER.md` §5.3, K-bug 2) —
   **already hard-stop TCB-approved**. Highest-value reach fix: it unblocks
   every `bind(...)` in type/index position.
3. Land order-dependent constructor injectivity (K-bug 1) — completeness only.
4. Extend size-change to well-founded/lexicographic descent.
5. Extend `simplify`'s rule set to generated defining equations for *certified*
   functions (`docs/PROOFS.md` §4) — the safe analogue of Lean's `rfl`-after-`whnf`.

**Gate.** `plus n Z = n` closes without explicit `induction` when `plus` is
certified. Every corpus flip justified. **No postulate, no bypass, no new kernel
rule.**

**TCB.** K-bug 2 pre-approved; everything else must pass the hard-stop test.

**Files.** `lib/cure/core/certificate.ex`, `lib/cure/core/size_change.ex`,
`lib/cure/core/unify.ex`, `lib/cure/elab/proof_goal.ex`.

---

### Phase 6 — Agda↔kernel correspondence (G6) — metatheory track

**Scope.** Close the gap between "soundness of the specification" and
"soundness of `Cure.Core.Kernel`."

**This is `proof/PLAN.md`'s M0 → M2 → M4 → M6 sequence, not a parity item.**
`proof/PLAN.md` §4 warns explicitly against adding more examples while
postponing it. The tree has grown 68 → 238 modules with M2/M4 still the
bottleneck.

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
6. Do not add `propext`/`Classical.choice`. Two postulates is better.
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

Items 1–6 are ~35–50 engineer-weeks. Item 7 is capacity-driven.

**A conditional result with an openly named unverified adapter must never be
labelled universal refinement.** That distinction is the most important honesty
constraint in this document and in `proof/PLAN.md`.
