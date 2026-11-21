# Lean 4 Parity — Status Scorecard

**Status:** living document. Updated whenever a plan phase lands or a parity pin flips.
**Execution plan:** [`PATH_TO_LEAN4_PLAN.md`](PATH_TO_LEAN4_PLAN.md)
**Authoritative analysis:** [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md)
**Corpus:** [`test/lean4_parity/`](../test/lean4_parity/) (run via `mix test test/lean4_parity_test.exs`)

This is the measurement half of the plan. The plan says *what to do*; this file records
*where we are*. Every number here is either counted from the tree or pinned by a corpus
case — nothing is estimated.

> **Gap numbering.** This scorecard uses the finer-grained **G1–G11** register, which is
> a superset of [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md)'s **C1–C10**. The mapping is in
> `PATH_TO_LEAN4_PLAN.md` §2.2. G6, G7, G8 and G11 are **not parity items** — they belong
> to the kernel metatheory track (`proof/PLAN.md`) and are listed here only so the two
> tracks are never confused.

---

## 1. Baseline (recorded at plan adoption)

| Metric | Value | How measured |
|---|---|---|
| Agda modules | **238** | `proof/Core` 65 + `proof/Proof` 151 + `proof/Fixtures` 22 |
| Postulate surface | **2** | `funext` (`Core/Syntax.agda`), `tree-decides` (`Proof/Soundness.agda`) |
| Termination/positivity bypasses | **0** | empty allowlist, `proof/scripts/check-hygiene.py` |
| Agda version | 2.8.0 | `proof/check.sh` preflight |
| Lean toolchain in repo | **none** | no `lean`/`lake`/`elan`, no `.lean`, no `lakefile` |
| Proof parity corpus cases | **14** | `test/lean4_parity/corpus.exs` (9 accept, 5 reject) |

**The postulate count is not a soundness certificate.** `proof/README.md` is explicit:
module parameters and check bypasses are separate obligations, and successful compilation
does not establish soundness-model applicability. Two postulates is a *hygiene* result.

---

## 2. Axis scores

The seven-axis model from the plan's Part I §1. Scores are qualitative and are the
plan's judgement, not a measurement; the *evidence* column is what makes them checkable.

| Axis | Capability | Score | Evidence |
|---|---|---|---|
| **L1** | Dependent type theory, inductive families, universes | **Strong** | `Cure.Core.Term`/`Kernel`; QTT grades; indexed families. `{l: UniverseLevel}` accepted at the surface; kernel level algebra (U1–U3) pending (G9). |
| **L2** | Definitional equality (NbE + δ-gated unfolding) | **Partial** | `Eval`/`Quote`/`Conv`/`Normalise` present; δ-reach limited (G3). |
| **L3** | Tactic ergonomics, goal states | **Partial** | `have`/`proof chain`/`because`/`simplify`/`rewrite`/`induction`; no goal list (G1), closed vocabulary (G2). |
| **L4** | User-extensible tactics | **Partial** | `macro` with `computed by` is a real elab; no `tactic` rule kind (G2). |
| **L5** | Tiny auditable kernel | **Strong** | `lib/cure/core/` TCB (~9.2k LOC); Z3 and elaborator both untrusted. Emitter assumed (G8). |
| **L6** | Automation (`simp` set, `aesop`, `omega`) | **Early** | Libraries exist (`ProofSearch`, `positivity`, LIA, `Std.Decision`); bare `simplify` already uses the global `@lemma` set; not exposed as tactics (G4, G5). |
| **L7** | Machine-checked metatheory | **Strong, caveated** | 238 modules, 2 postulates; but proves the *specification*, not the executable kernel (G6). |

**Score: 3 strong, 3 partial, 1 early.** Cure's foundations are ahead of its ergonomics.
That asymmetry is the entire plan.

---

## 3. Gap register

Ordered by impact per unit of risk. **Status** is one of
`open`, `in progress`, `closed`, or `unpinnable` (no Cure-source witness exists).

| # | Gap | Axis | `PATH_TO_LEAN4` | Severity | Risk | TCB | Status |
|---|---|---|---|---|---|---|---|
| **G1** | No goal-state introspection | L3 | **C7** | Critical | Low | None | **in progress** |
| **G2** | No user-extensible tactics (`macro` has no `tactic` kind) | L3/L4 | **C1** | Critical | Low | None | **open** |
| **G3** | δ-reach: `reflexive`/`simplify` won't unfold recursive defs | L2 | **C5**, **C9** | High | **High** | Gated | **open** |
| **G4** | No global `@[simp]`-style lemma set | L3/L6 | **C4** | High | Low | None | **open** |
| **G5** | Automation not exposed as tactics | L6 | C4/C1 clients | High | Low | None | **open** |
| **G6** | Agda↔kernel correspondence unproven (M2/M4) | L7 | — (proof-side) | High | **High** | None | **open** |
| **G7** | No `lean4lean`-style second backend | L5/L7 | — (decision 6) | Medium | Medium | None | **open** |
| **G8** | Emitter/BEAM semantics assumed, not proved | L5 | — (out of scope) | Medium | High | Out of scope | **open** |
| **G9** | Universe polymorphism designed (U0–U7), not landed | L1 | **C2** | Medium | Medium | **Yes** | **open** |
| **G10** | No simp-set debugging (`simp?`) | L3 | **C4** | Low | None | None | **open** |
| **G11** | `unbound` failure impossibility unproven (M4b refuted) | L7 | — (proof-side) | Low | Medium | None | **open** |

### Gaps `PATH_TO_LEAN4.md` lists that this scorecard does not

Two items in `PATH_TO_LEAN4.md` §2 are **not** reach gaps and are deliberately absent
from the register above:

| `PATH_TO_LEAN4.md` | Why it is not a G-gap here |
|---|---|
| **C3** (operator fixity Step 3) | Real, independent, and already specified. It is a language feature, not a *proof* capability, so it is not scored on the L1–L7 proof axes. Tracked in `PATH_TO_LEAN4.md` only. |
| **C6** (`apply`/`exact`) | The commands **already exist** (`proof_application` nodes in `lib/cure/compiler/parser.ex`). What remains is ergonomics, which is C1's goal API work. |
| **C8** (`rewrite` single-occurrence) | A deliberate default that `PATH_TO_LEAN4.md` §11 forbids changing. The opt-in `all` selector already landed in the parser. |
| **C10** (elaborator reach ledger) | A *collection* of reach gaps (E9, E10, E12, E13, K-bug 1), tracked in `kernel/MASTER.md` §9 rather than duplicated here. |

### Pinnable vs unpinnable

G6, G7, G8 and G11 have **no Cure-source witness** — they are proof-side or runtime-side
obligations. They have no corpus entries, and `test/lean4_parity_test.exs` asserts that
absence explicitly so a silently-dropped gap is loud rather than invisible.

| Gap | Why no source pin |
|---|---|
| G6 | The claim is about the *relationship* between Agda and `Cure.Core.Kernel`, not about any program. |
| G7 | The claim is about a second checking backend that does not exist yet. |
| G8 | The claim is about BEAM emission semantics, which no Cure program can witness. |
| G11 | The claim is about a failure *mode* of the modelled evaluator, not an accept/reject outcome. |

---

## 4. Corpus pins

`test/lean4_parity/corpus.exs` — 13 cases. A **reject** pin is a *measured gap*, not an
aspiration. Flipping one is the review of a semantic change.

| **G4** | No `@[simp]` attribute / `simp?` (bare `simplify` **does** use `@lemma`) | L3/L6 | Medium | Low | None | **open** |
|---|---|---|---|
| `g3-reflexive-nonrecursive` | G3 | accept | `reflexive` closes definitionally-equal endpoints |
| `g3-reflexive-recursive-unfolding` | G3 | **reject** | `reflexive` does **not** see through a recursive definition |
| `g3-induction-closes-recursive` | G3 | accept | the same goal **is** closable with `induction` + `simplify using [ih]` |
| **G9** | Universe polymorphism: surface binder works; kernel level algebra (U1–U3) pending | L1 | Medium | Medium | **Yes** | **open** |
| `g4-bare-simplify-uses-lemma-set` | G4 | accept | bare `simplify` **does** use the global `@lemma` set |
| `g5-confirmed-evidence` | G5 | accept | `Confirmed()` inhabits `IsTrue(True())` |
| `g5-decide-dependent-return` | G5 | **reject** | `decide_is_true`'s dependent return type is a reach gap |
| `g9-fixed-universe-type` | G9 | accept | `Type` usable at level zero |
| `g9-universe-level-binder` | G9 | accept | `{l: UniverseLevel}` **is** accepted at the surface |
| `g1-hole-blocks-codegen` | G1 | **reject** | a hole typechecks but is refused at codegen (E014) |
| `g1-open-because-block` | G1 | **reject** | an open `because` block gives `E110`, not a goal list |
| `g2-syntax-macro-works` | G2 | accept | `syntax … becomes` expands at a use site |
| `g2-tactic-rule-kind` | G2 | **reject** | a `tactic` macro rule kind does not exist |
| `g10-simplify-using-explicit-rules` | G10 | accept | `simplify using [rules]` closes with an explicit list |

**Distribution:** 9 accept, 5 reject.

### Corrections made against the tree

The first draft of this corpus contained **three wrong pins**. They were caught by
running the corpus, which is precisely what it exists to do:

| Pin | First draft | Verified | Correction |
|---|---|---|---|
| `g4-bare-simplify-user-lemma` | `:reject` | **accepted** | A bare `simplify` **does** consult the global `@lemma` set (`ProofGoal.simplify_lemma_set/2`). The real G4 gap is the `@[simp]` *attribute* and `simp?`, not lemma-set reach. |
| `g9-universe-polymorphic-binder` | `:reject` | **accepted** | `{l: UniverseLevel}` parses and elaborates. The remaining G9 gap is the kernel's canonical level algebra (U1–U3), **not** the surface binder. |
| `g1-hole-is-checkable` | `:accept` | **rejected at codegen** | A hole type-checks but is refused at compilation (`unfilled_hole`, E014). Since this corpus compiles, the pin is `:reject` — matching `docs/PROOFS.md` §3.7. |

**Lesson recorded for later phases:** a pin is a *claim about the tree*, and every
claim must be executed before it is recorded. Three of fourteen were wrong when
written from documentation alone.

### A harness defect worth remembering

The first version of `test/lean4_parity_test.exs` pattern-matched the expectation
as a literal:

```elixir
case {c.expect, Case.run(c)} do
  {:accept, {:accepted, module}} -> ...
  {:reject, {:accepted, module}} -> ...   # never matched
end
```

Because `c` is a compile-time struct literal, the compiler narrows `c.expect` to a
single atom per generated test, so the opposite branch is **statically
unreachable**. The reject-side assertions never ran, and the only symptom was a
`--warnings-as-errors` abort *after* a green `30 tests, 0 failures` — easy to
mistake for a tooling quirk.

The fix reads the expectation at runtime (`Map.fetch!(c, :expect)`), and the
harness was then **negative-controlled**: deliberately flipping one `:reject` pin
to `:accept` produced exactly one failure with the right message. A green suite
is not evidence that the assertions ran; a deliberate break is.

---

## 5. Phase status

| Phase | Scope | TCB | Status |
|---|---|---|---|
| **0** | Baseline, guards, corpus, scorecard | None | **in progress** — CI already present; corpus + this file added |
| **1** | Goal-state introspection (G1) | None | **in progress** — `E110` now renders the residual goal + local facts; REPL/LSP surfaces outstanding |
| **2** | `Cure.Elab.Tactic` monad (G2 pt 1) | None | not started |
| **3** | `tactic` macro rules (G2 pt 2) | None | not started |
| **4** | `@[simp]` sets + tactic automation (G4, G5, G10) | None | not started |
| **5** | δ-reach widening (G3) | **Gated** | not started — must follow 0–4 |
| **6** | Agda↔kernel correspondence (G6) | None (proof) | not started — the metatheory bottleneck |
| **7** | `lean4lean` second backend (G7) | None | not started |
| **8** | Universe polymorphism (G9, U0–U7) | **Yes** | not started — approved design exists |
| **9** | Emitter/BEAM (G8) | Out of scope | not started |
| **10** | Semantic totality (G11) | None (proof) | not started |

---

## 6. What "done" means

Per the plan's §12 and `proof/PLAN.md` §12, the claim ladder is:

- **G1 (bounded checked Core path)** — a mechanically delimited fragment obtains native
  admission at its original goal through checked replay, with every remaining trusted
  adapter stated explicitly.
- **G2 (actual kernel refinement)** — every successful release-admission path in the
  advertised coverage has related native evidence.
- **G3 (compiler/runtime refinement)** — accepted relevant programs lower through typed
  erasure and the BEAM boundary with stated observable behaviour.

**A conditional G1 theorem with an openly named unverified adapter must never be
labelled universal G2 refinement.** That distinction is the single most important
honesty constraint in this document.

---

## 7. Non-negotiable invariants

Carried from the plan §10. Any phase proposal that violates one of these is rejected:

1. Never add a postulate, hole, or termination/positivity bypass.
2. Never widen the TCB to fix an elaboration or conversion failure.
3. Automation stays untrusted-**and**-checked.
4. Preserve the original expected goal.
5. Add capability, not Lean spelling (`docs/PROOFS.md` §3's "no aliases" stands).
6. No new Lean toolchain in the build.
7. Preserve older artifact bytes unless a reviewed schema change requires migration.
8. A flipped parity pin is the review of a semantic change.

---

## 8. How to update this file

When a phase lands:

1. Flip the affected pins in `test/lean4_parity/corpus.exs` **in the same commit**.
2. Update the gap's **Status** in §3 and the **Distribution** in §4.
3. Update the phase's **Status** in §5.
4. If the phase changed the postulate surface or bypass inventory, update §1 and
   `proof/README.md` together — `proof/scripts/check-postulates.sh` enforces the pairing.

Do not update this file to describe intent. It records measurements.
