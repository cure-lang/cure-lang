# Lean 4-Style Proof Readiness: Audit

Status: audit of the repository at the time of writing. Companion to
[`LEAN4_MIGRATION_PLAN.md`](LEAN4_MIGRATION_PLAN.md).
Scope: the mechanised proof development in [`proof/`](../proof), the executable
kernel it is about (`lib/cure/core/`), the surface proof language
([`PROOFS.md`](PROOFS.md)), and the proof-carrying package pipeline
([`PROOF_CARRYING.md`](PROOF_CARRYING.md)).

---

## 0. What "Lean 4-style proofs" means here

"Lean 4-style" is not one property. It decomposes into six independent
capabilities. This audit scores each one separately, because the project is
strongly ahead on some and structurally absent on others — and conflating them
is what produces the wrong migration plan.

| # | Capability | Lean 4 realisation |
|---|---|---|
| L1 | **Machine-checked metatheory** — the soundness theorem is a checked theorem, not a written argument | Lean's own `TypeChecker`/`Kernel` soundness work; `lean4` stdlib lemmas |
| L2 | **Small, explicit, auditable axiom base** | `propext`, `Classical.choice`, `Quot.sound` — exactly three, printed by `#print axioms` |
| L3 | **Tactic-driven proof ergonomics** — goals, local context, `simp`/`rw`/`induction`/`omega`/`aesop` | `Mathlib` tactic framework |
| L4 | **Definitional equality that computes** — `rfl` closes any goal whose sides are definitionally equal, including multi-step reduction of recursive definitions | `whnf`/`simp` via compiled `Eq.refl` unfolding |
| L5 | **A trusted kernel small enough for a human to audit, with everything else untrusted** | `Lean.Kernel` ≈ 5k LOC; elaborator/tactics untrusted |
| L6 | **Proof artifacts as first-class, checkable objects** — `.olean`, proof terms, offline re-checking | `lean --check`, `#print`, `Lean.Environment` |

---

## 1. Headline assessment

> **The project is closer to Lean 4 on the *metatheory* axis (L1, L2) than on
> the *ergonomics* axis (L3, L4), and the two axes are being confused in the
> project's own documentation.**

Concretely:

- **L1 (metatheory): substantially achieved, in Agda.** 238 checked modules
  (`65` under `proof/Core/`, `151` under `proof/Proof/`, `22` generated under
  `proof/Fixtures/`), including Progress, Preservation, `Final`-preservation,
  fuel-indexed and coinductive soundness, confluence, and a native dependent
  typing development. This is a *stronger* position than most language projects
  ever reach.
- **L2 (axiom base): achieved, and better than Lean's.** Exactly two postulates,
  enforced by CI: `funext` (`proof/Core/Syntax.agda:377`) and `tree-decides`
  (`proof/Proof/Soundness.agda:316`). Lean ships three. The project also
  maintains an *empty* check-bypass allowlist — no `{-# TERMINATING #-}`, no
  `{-# NON_TERMINATING #-}`, no `--no-termination-check`.
- **L3 (ergonomics): partially achieved, but not Lean-shaped.** The surface
  proof language exists and is real (`have`, `proof chain`, `because`,
  `simplify`, `rewrite`, `induction`, holes, named arguments — see
  `docs/PROOFS.md` §3). But it is a fixed, closed vocabulary with **no
  user-extensible tactics**, no goal-state introspection, and no `simp` lemma
  set under user control.
- **L4 (computing definitional equality): the single largest gap.** `reflexive`
  closes a goal only when the endpoints are *already* definitionally equal, and
  `simplify` "will not unfold arbitrary recursive definitions". A goal like
  `plus(Z, plus(Z, value)) == value` therefore needs an explicit two-step
  `proof chain`, where Lean would close it with `rfl` or `simp`.
- **L5 (auditable kernel): achieved.** `lib/cure/core/` (~9,200 LOC) is the
  TCB; the elaborator, SMT solver, and totality *proposer* are all explicitly
  outside it and explicitly untrusted (`docs/SOUNDNESS.md` §5.1–5.4).
- **L6 (checkable artifacts): partially achieved, and the strongest single
  asset for migration.** There is a proved wire format (`proof/Core/Wire.agda`),
  a proved decoder with `decode (encode t) ≡ just t` and **no postulate**, a
  cross-language vector asserted independently in Agda and Elixir, and
  byte-for-byte reproducible generated certificates. This is *further* than
  most Lean projects go on artifact provenance.

**Bottom line: this is not a "start from zero" migration.** It is a migration
from *excellent Agda metatheory + a closed-surface proof DSL* to *Lean-grade
ergonomics on top of that metatheory*. The metatheory does not need to be
rebuilt; the tactic layer and the definitional-equality story do.

---

## 2. L1 — Machine-checked metatheory

### 2.1 What exists

The development is a faithful formalisation of the Core calculus of
`Cure.Core.Term` (`docs/SOUNDNESS.md` §1.1): three predicative universes, graded
Π/λ/application over the QTT carrier `{0, 1, ≤1, ω}`, graded `let`, indexed
inductive families with a dependent eliminator, globals with δ gated on a
totality certificate, primitive literals, inert effects, and two
development-only leaves.

Proved, with no postulates:

| Result | Module |
|---|---|
| QTT grade carrier and all algebraic laws | `proof/Core/Grade.agda` |
| Universe hierarchy, cumulativity, `max` | `proof/Core/Universe.agda` |
| Core syntax, `shift`/`substS`, scoping | `proof/Core/Syntax.agda` |
| Reduction `_⇝_` (β, ζ, ι, δ, congruences, four literal peels) | `proof/Core/Reduction.agda` |
| Canonical-form and head-inversion lemmas | `proof/Proof/CanonicalForms.agda`, `Inversion.agda` |
| Renaming and substitution lemmas, every case | `proof/Proof/Preservation.agda` |
| Weakening, context laws, `extF` | `proof/Proof/Context.agda` |
| **Progress** | `proof/Proof/Progress.agda` |
| **Preservation** (all cases incl. β/ζ/ι/δ) | `proof/Proof/Preservation.agda` |
| `Final`-preservation | `proof/Proof/FinalPreservation.agda` |
| **`soundness-fuel`** (fuel-indexed) | `proof/Proof/Soundness.agda` |
| **`soundness-tree`** (coinductive, guarded) | `proof/Proof/Soundness.agda` |
| **`soundness-nf`** (dichotomy over normal forms) | `proof/Proof/SoundnessConfluence.agda` |
| Confluence of `_⇝_`, strong parallel diamond, no termination override | `proof/Proof/Confluence.agda`, `StrictConfluence.agda` |
| Structural erasure idempotence | `proof/Proof/Erase.agda` |
| Effect inertness | `proof/Proof/EffectInert.agda` |
| Native dependent typing, transport, preservation, progress | `proof/Proof/Dependent*.agda` (~60 modules) |
| Wire codec fidelity, no postulate | `proof/Core/Wire.agda` |

### 2.2 What is *not* proved, and is honestly labelled as such

The project's self-reporting is unusually disciplined here, and the audit
confirms it is accurate rather than defensive:

1. **`Certified` means body finality, not semantic termination.**
   `proof/Proof/Progress.agda`'s `Certified` predicate says a global's body is
   hole-free and absurd-free. It does **not** say the body terminates. The
   size-change *verifier* is trusted and tamper-tested, but the size-change
   *principle* (Lee–Jones–Ben-Amram) is an assumed theorem, and the chain from
   trusted Core call extraction to semantic descent is unproved
   (`docs/SOUNDNESS.md` §8.2).
2. **No executable refinement.** The theorems are about a *specification*
   relation `_⇝_`, not about `Cure.Core.Eval`. `Proof.ClosureEvaluation` and
   `Proof.ClosureQuotation` prove positive simulation for an explicit *model*
   evaluator, and `Core.FailureImpossibility` proves three of the four
   evaluator `raise` sites unreachable — but the fourth (`unbound`) is a
   recorded worker limitation, not a claim. `M4B-PLAN.md` §8 documents an
   attempted and **refuted** migration.
3. **η is layered, not integrated.** `Core.TypedEta` defines `_≈η_` as a
   separate relation because the common-reduct model explicitly *refutes* η
   between well-typed open functions (`eta-not-in-this-model`). The executable
   `Conv` *does* perform η. So the formal conversion relation and the
   executable conversion checker are known to disagree, in a documented,
   conservative direction.
4. **The dependent-signature fragment is restricted.** `ClosedFragmentSig`
   requires individually closed telescope entries; a genuinely dependent
   telescope is deliberately rejected (`Proof.ClosedFragmentExamples`). The
   native `Core.DependentTyping` development is the replacement under review,
   not a migration of the soundness consumers.
5. **Erasure simulation is not proved.** `erase-idem` is structural idempotence
   with administrative let collapse. `eraseSpine` is *not called by*
   `eraseTerm`, so `erase-idem` is not idempotence of the full executable
   `Erase.erase/2`. δ-vs-erasure non-commutation is a recorded *negative*
   result with two pinning tests.
6. **BEAM lowering is entirely unproved.** `docs/SOUNDNESS.md` §5.3 item 3
   assumes the emitter maps Core faithfully. Nothing checks it.

### 2.3 L1 verdict

**Strong.** The gap to Lean here is *not* one of rigour or coverage of the
calculus; it is that the calculus being proved about is a specification that
diverges from the executable in five documented places (§2.2 items 1–5).

---

## 3. L2 — Axiom base

### 3.1 Inventory

`proof/scripts/check-postulates.sh` asserts an exact, sorted, two-entry
inventory and fails CI on any change:

```
Core/Syntax.agda:funext
Proof/Soundness.agda:tree-decides
```

- `funext` — function extensionality. Not derivable in intensional type theory;
  standard for de Bruijn metatheory. Lean derives it from `propext` +
  `Quot.sound`, so this is not a *stronger* commitment, just a direct one.
- `tree-decides` — LPO on the outcome path. The only classical input. It is
  confined to the *classical* statement; the constructive `soundness-fuel` and
  `soundness-tree` do not depend on it.

`proof/scripts/check-hygiene.py` additionally enforces an **empty** bypass
allowlist — no termination/positivity pragmas anywhere in `proof/`, including
generated `Fixtures/` and any future subdirectory.

### 3.2 The honest caveat

The two-postulate count is a count of *declared* postulates. It does **not**
count:

- **module parameters**, which are hypotheses. `Proof.Preservation` takes
  `CertifiedTyped`, `Conversion`, `ReduceConv`, `CaseCoverage`, and
  `ClosedFragmentSig` as parameters. These are not axioms — they are
  obligations discharged by `Proof.SoundnessModel` on a nonempty fragment —
  but a reader who reads "two postulates" as "two assumptions" will be misled.
- **the totality principle**, which is assumed outside the development
  (§2.2 item 1).

`proof/README.md` states this explicitly ("This inventory does not account for
the remaining model/refinement obligations"), which is the right disclosure.

### 3.3 L2 verdict

**Better than Lean 4.** Two axioms vs three, CI-enforced, with a stronger
hygiene guard than Lean's default toolchain. No work needed.

---

## 4. L3 — Tactic ergonomics

### 4.1 What exists

`docs/PROOFS.md` §3 defines a real, checked proof vocabulary. It is elaboration
syntax that adds **no Core constructors and no kernel rules**, and does not
survive erasure:

| Form | Lean analogue | Notes |
|---|---|---|
| `have x [: P] = e` | `have` | checked local `let`; not an assumption |
| `proof chain … because …` | `calc` | equational reasoning; `_` = previous step |
| `simplify` | `simp` | closes the goal; β/ι/ζ + certified transparent defs + a small audited rule set |
| `simplify using [rules]` | `simp [rules]` | explicit rule list |
| `simplify using p` | `simpa using p` | near-matching proof reuse |
| `rewrite using e [at n] [in h]` | `rw` | directed; does **not** close |
| `induction v` + `case C(…) =>` | `induction` | expands to the datatype eliminator |
| `?name` | `?_` / `sorry` | hole; blocks codegen, reports goal to LSP |
| `f(label: v)` | named arguments | reorders into the telescope |

There is also a genuine, non-trivial win: **generated defining equations**
(`docs/PROOFS.md` §4). Every total function exposes kernel-checked equations
named from source constructor paths (`add3.S3(k, y)`), which is the Lean
`Nat.add_succ` / `foo.eq_def` story, and is what makes `simplify` and `rewrite`
usable at all.

### 4.2 The gaps, ranked by how much they hurt

1. **No user-extensible tactics.** The vocabulary is closed and hard-coded in
   the elaborator. Lean's power is that `simp`/`omega`/`aesop` are *libraries*
   of tactics over a `Lean.Meta`/`Lean.Elab.Tactic` API. Cure has no equivalent
   API, no `macro`/`elab` for tactics, and no way for a library to add a proof
   command. `docs/PROOFS.md` §3 even states the deliberate exclusion:
   "Cure does not accept `calc`, `by`, `simp`, `simpa`, `congr`, `exact`, or
   `apply`."
2. **No goal-state introspection.** There is a `:hole_goal` pipeline event, but
   no interactive goal display, no `case`/`next` focusing, no way to inspect
   the goal mid-proof. Lean's `InfoView` is the single biggest ergonomic
   multiplier and has no analogue.
3. **No decision procedures.** No `omega`, no `decide`, no `norm_num`, no
   `ring`. `Std.Proof.LinearArithmetic` exists as "checked linear-arithmetic
   reflection", but it is a library of proofs, not a tactic that discharges
   goals.
4. **`simplify` is a fixed, unauditable-by-the-user rule set.** The user cannot
   add a `@[simp]` lemma. `simplify using [rules]` takes an explicit list per
   call site, which does not compose across a file.
5. **No `apply`/`exact`.** `docs/PROOFS.md` argues this is fine "because
   theorem invocation is ordinary call syntax". That is true for *forward*
   reasoning and false for *backward* reasoning, which is most of real proofs.
6. **`rewrite` succeeds only on exactly one occurrence** and errors otherwise
   (`E111`). Lean's `rw` rewrites all occurrences by default. This is a
   deliberate safety choice, but it makes multi-occurrence goals tedious.

### 4.3 L3 verdict

**Partially achieved, wrong shape.** The vocabulary is Lean-*inspired* but
implemented as a closed DSL rather than an open tactic framework. Closing this
gap is the bulk of the migration work and is the one place where "Lean 4-style"
is genuinely the right target.

---

## 5. L4 — Computing definitional equality

### 5.1 The gap, precisely

Two documented statements define it:

- `docs/DEPENDENT_TYPES.md:79` — "`reflexive` closes goals whose endpoints are
  definitionally equal."
- `docs/PROOFS.md:209–212` — `simplify` covers "beta, constructor/iota, and
  let/zeta reduction, certified transparent definitions, generated defining
  equations, and a small audited set of orientation-checked equations. It
  terminates … **it will not unfold arbitrary recursive definitions**."

So definitional equality *does* unfold certified globals
(`docs/DEPENDENT_TYPES.md:63–67`), but `simplify` — the tactic — is deliberately
narrower than the conversion checker.

The consequence is visible in the project's own examples. `docs/PROOFS.md` §3.2
proves `plus(Z, plus(Z, value)) == value` with an explicit **two-step**
`proof chain`. In Lean, `rfl` closes it, because `Nat.add` is a compiled
recursive definition and `whnf` reduces it.

### 5.2 Why this is the highest-leverage gap

Every proof in the project pays this tax. It is not a missing feature at the
edge; it is a missing feature in the *inner loop* of every proof. It also
compounds with L3 gap 4 (no `@[simp]` set): the user cannot even amortise the
cost across a file.

The reason for the narrowness is sound — `simplify` must terminate, and
unfolding arbitrary recursion does not. But the fix is known and is exactly
what Lean does: **unfold only certified-total definitions, using the existing
size-change certificate as the termination witness.** The certificate already
gates δ in conversion (`Normalise.unfold_certified_head`), so the mechanism
exists; it is simply not exposed to `simplify`.

### 5.3 L4 verdict

**The largest single gap.** It is also the most tractable, because the
machinery (certified unfolding) is already built and already trusted.

---

## 6. L5 — Auditable kernel

`docs/SOUNDNESS.md` §5.1 puts the TCB at `lib/cure/core/` (~9,200 LOC, 21
modules). §5.4 records two deliberate exclusions that are genuinely
Lean-shaped:

- **The SMT solver is never trusted.** Z3 is an untrusted lint over refinement
  obligations; its verdicts can warn but never certify a kernel judgement.
- **The elaborator is never trusted.** The kernel re-derives every type; it
  never consumes an elaborator-supplied type as an axiom.

This is the correct Lean architecture and it is already in place. The
release firewall (`Emit.reject_holes/2`, `E014`) validates **pre-erase** Core,
so a hole hidden in an erased position is caught before `Erase.erase` drops it
— a subtlety Lean handles via `sorry` tracking, and Cure handles correctly.

**L5 verdict: achieved.** No migration work required.

---

## 7. L6 — Proof artifacts

This is the project's most under-appreciated asset and the strongest bridge to
Lean-style tooling.

### 7.1 What exists

- **A proved wire format** (`proof/Core/Wire.agda`): trees flatten to
  prefix-free instruction streams, decoded by a stack machine with **structural
  recursion** — no fuel, no termination override. `run-instructions` proves
  decoding inverts encoding; `decode-encode` composes it so
  `decode (encode t) ≡ just t` for every tree, **with no postulate**.
- **A proved codec for every certificate layer**: recipes, packets,
  declarations, whole certificates, snapshots, callers, checking requests
  (`Core/WireRecipe.agda`, `WireCertificate.agda`, `WireSnapshot.agda`,
  `WireCaller.agda`, `WireChecking.agda`, `WireResidualChecking.agda`,
  `WireArgumentCaller.agda`).
- **A cross-language vector**, hand-checked and asserted independently in
  `Proof.WireExamples.cross-characters` and in
  `test/cure/core/proof_wire_test.exs`: for `tm-atom_lit "a"` under the table
  `["", "a"]`, both emit `(1111111111111111111;1;;)`.
- **Byte-for-byte reproducible generated artifacts**
  (`proof/scripts/generate-wire-certificate.exs --check`), with the generator
  refusing to rewrite older artifacts.
- **A source-bound admission pipeline** (`Core.CheckedAdmission.verify`) that
  takes only represented input + name table + certificate characters and
  derives native evidence internally, with **no caller-supplied validity,
  conversion, lookup-typing or safety callback**.

### 7.2 The honest boundary

The project states it precisely and the audit confirms it: recipe replay proves
that a *represented* input has a native derivation. It does **not** prove the
converse — that every `Kernel.check` acceptance yields a replayable
certificate. That is the Stage 3 / M6 correspondence and it remains open. Also
open: universal Elixir-producer correspondence (`Validated` is a *model* of the
producer's checks, not a refinement of `Cure.Core.ProofSnapshot`), and semantic
context/environment fidelity.

### 7.3 L6 verdict

**Substantially achieved, with a clearly stated one-directional gap.** Notably,
the project's artifact story is *ahead* of what most Lean projects do — Lean
gives you `.olean` and `lean --check` but not a proved codec for the artifact
format.

---

## 8. Gap register

Ordered by (impact on the stated goal) ÷ (effort). "Impact" is the number of
proofs affected; "effort" is engineering weeks at current velocity.

| ID | Gap | Axis | Impact | Effort | Blocked by |
|---|---|---|---|---|---|
| **G1** | `simplify` will not unfold recursive definitions; no `rfl`-by-computation | L4 | Every proof | 3–4 | — |
| **G2** | No user-extensible tactic framework (`Lean.Elab.Tactic` analogue) | L3 | Every proof | 8–12 | — |
| **G3** | No `@[simp]`-style global lemma set | L3 | Most proofs | 2–3 | G2 |
| **G4** | No goal-state introspection / interactive goal display | L3 | All proof authoring | 4–6 | G2 |
| **G5** | No decision procedures (`omega`, `decide`, `norm_num`) | L3 | Arithmetic-heavy proofs | 6–10 | G2 |
| **G6** | `Certified` = body finality, not termination; size-change principle assumed | L1 | Soundness statement strength | 12–20 | — |
| **G7** | No executable refinement (`Eval`/`Quote`/`Conv` vs `_⇝_`) | L1 | Soundness *applicability* | 20–40 | G6 |
| **G8** | η layered, not integrated; formal/executable conversion disagree | L1 | Conversion soundness | 6–10 | — |
| **G9** | `unbound` failure impossibility — worker redesign | L1 | Failure correspondence | 4–6 | — |
| **G10** | Dependent-signature fragment restricted (`ClosedFragmentSig`) | L1 | Dependent coverage | 10–15 | — |
| **G11** | Erasure simulation unproved; `eraseSpine` not wired | L1 | End-to-end safety | 8–12 | G10 |
| **G12** | BEAM lowering entirely unproved | L1 | End-to-end safety | 15–25 | G11 |
| **G13** | No `apply`/`exact`; backward reasoning unsupported | L3 | Proof style | 2–3 | — |
| **G14** | `rewrite` single-occurrence-only | L3 | Proof tedium | 1 | — |
| **G15** | Kernel-acceptance → replayable certificate (one direction) | L6 | Artifact completeness | 10–15 | — |
| **G16** | Universal Elixir-producer correspondence | L6 | Artifact trust | 8–12 | — |
| **G17** | No Lean toolchain present (`lean`/`lake`/`elan` absent, no `.lean` files) | — | Tooling choice | 0 | decision |

**Total to full Lean parity on L3+L4 (G1–G5, G13, G14): ~26–39 weeks.**
**Total to full executable soundness (G6–G12): ~75–130 weeks.**
These are independent tracks and should be run in parallel, not sequenced.

---

## 9. What is *not* a gap (and should not be "fixed")

Recording these matters, because a migration plan that tries to close them will
waste effort and lose properties the project already has:

1. **Agda is not the problem.** The metatheory is strong, the axiom base is
   better than Lean's, and the hygiene guards are stricter. Porting 238 modules
   to Lean would cost 6–12 months and buy *nothing* on L1/L2. **Do not port.**
2. **Two postulates is better than Lean's three.** Do not "align" with Lean by
   adding `propext` or `Classical.choice`.
3. **The empty bypass allowlist should stay empty.** Lean permits
   `termination_by`/`decreasing_by` escape hatches; Cure's stricter position is
   a feature.
4. **`rewrite`'s single-occurrence default is safer than Lean's.** Lean's `rw`
   silently rewrites all matches; Cure's `E111` forces a choice. Keep the
   default, add an explicit `all` modifier (G14).
5. **`simplify`'s refusal to "declare two terms equal because the host
   computed so"** is correct. The fix for G1 is *certified* unfolding, not
   trusting the host evaluator.
6. **The fixture-heavy `Proof/*Examples.agda` modules are not padding.** They
   are the non-vacuity evidence that keeps the parameterised theorems honest.
   The project's own `PLAN.md` §4 warns against "an indefinite sequence of
   increments adding examples while postponing M2/M4" — that warning is about
   *sequencing*, not about the examples being worthless.

---

## 10. Summary table

| Axis | State | Score | Work to parity |
|---|---|---|---|
| L1 Metatheory | 238 Agda modules; Progress/Preservation/Soundness/Confluence proved | **Strong** | G6–G12 (executable refinement) |
| L2 Axiom base | 2 postulates, CI-enforced, empty bypass allowlist | **Better than Lean** | none |
| L3 Tactics | Real but closed vocabulary; no extensibility, no goals, no decision procedures | **Partial** | G2–G5, G13, G14 |
| L4 Computing defeq | `reflexive` needs endpoints already equal; `simplify` won't unfold recursion | **Weakest** | G1 |
| L5 Kernel auditability | 9,200 LOC TCB; SMT and elaborator untrusted; pre-erase hole firewall | **Achieved** | none |
| L6 Artifacts | Proved wire codec, no postulate, cross-language vector, reproducible | **Strong** | G15, G16 |

**The one-sentence audit:** *the project has Lean-grade metatheory and
Lean-grade kernel discipline, but a closed-DSL proof language where Lean has an
open tactic framework, and a definitional-equality story that stops one step
short of `rfl` — so the migration is a surface-language and conversion-engine
project, not a formalisation project.*
