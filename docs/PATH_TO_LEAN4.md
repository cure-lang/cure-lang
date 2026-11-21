# Cure → Lean Feature Parity: Plan

**This document supersedes [`LEAN4_MIGRATION_PLAN.md`](LEAN4_MIGRATION_PLAN.md).**
That plan was written from the proof-side documents alone and proposed building
a tactic framework, a `@[simp]` set, and `apply`/`exact` as if they did not
exist. Reading `docs/MACROS.md`, `docs/superpowers/specs/types/MASTER.md` and
`docs/superpowers/specs/kernel/MASTER.md` shows most of that surface is either
already landed or already specified. The earlier plan also carries a **wrong
recommendation** — see §9.

Scope: make **Cure itself** reach feature parity with Lean 4. No porting. The
Agda development in `proof/` is untouched by this plan.

---

## 1. What "parity" means, and what Cure already has

Lean's power is not one feature; it is eight. Cure's position on each:

| # | Lean capability | Cure equivalent | Status |
|---|---|---|---|
| P1 | Dependent type theory, indexed families, GADTs | `indexed type`, `indices (…)`, dependent `case` | **Landed** |
| P2 | `simp`/`rw`/`induction`/`omega` tactics | `simplify`, `rewrite`, `induction`, `@lemma` proof search | **Landed** (closed vocabulary) |
| P3 | `macro` / `syntax` / `elab` — user-extensible frontend | `macro` container, `becomes` / `computed by`, `syntax family` | **Landed** |
| P4 | Typeclasses + instance resolution | `interface` / `implementation`, coherence, type-directed search | **Landed** |
| P5 | `instance`-driven operators, precedence | `precedencegroup`, `infix`/`prefix`, sole-route `==`/`<` | **Step 2 landed; Step 3 (fixity) ahead** |
| P6 | Universe polymorphism (`Type u`) | `Type(l)`, `universe_zero/succ/max`, `TypeLimit` | **Specified (U0–U7), not landed** |
| P7 | `mutual` blocks, well-founded recursion | Implicit forward/mutual refs; SCC size-change certification | **Landed** (permissive: no `mutual` keyword) |
| P8 | Metaprogramming over goals (`Lean.Meta`) | `computed by` expanders over `Std.Syntax`; `@lemma` search | **Landed for syntax; absent for goals** |

**The honest headline: Cure is at or near Lean parity on P1, P2, P3, P4, P7.
The real gaps are P5 (operator fixity), P6 (universe polymorphism), and P8's
goal-metaprogramming half.**

This is a very different conclusion from the earlier plan, which claimed the
tactic layer was "structurally absent." It is not. `docs/PROOFS.md` §3 defines
`have`, `proof chain`, `because`, `simplify` (with `using [rules]` and
`simpa`-style `using <proof>`), `rewrite` (with `backwards`/`at`/`in`),
`induction`, holes, and named arguments — all checked, all erasing to nothing.

---

## 2. The genuine gaps, ranked

| ID | Gap | Lean counterpart | Impact | Effort |
|---|---|---|---|---|
| **C1** | **No goal-state metaprogramming.** `computed by` expanders see *syntax*, never a *goal*. A user cannot write a tactic that inspects the goal and decides what to do. | `Lean.Meta` / `Lean.Elab.Tactic` | Every custom tactic | 8–12w |
| **C2** | **Universe polymorphism unspecified-but-unlanded.** `Type(l)` design is complete (U0–U7) but the kernel still has the fixed ceiling. | `Type u` | All generic stdlib | 12–20w |
| **C3** | **Operator fixity Step 3 unlanded.** `precedencegroup` + `infix`/`prefix`/`postfix` designed, not built; the static `Precedence.ex` table still exists. | `infixl`/`infixr`/`notation` | Operator ergonomics | 3–4w |
| **C4** | **No `@[simp]` global lemma set.** `simplify using [rules]` is per-call-site; `@lemma` feeds *proof search*, not `simplify`. | `@[simp]` attribute | Proof tedium | 2–3w |
| **C5** | **`simplify` will not unfold recursive definitions.** Deliberate ("it will not unfold arbitrary recursive definitions"), but Lean's `simp` does, gated on termination. | `simp` + `@[simp]` defs | Every proof | 3–4w |
| **C6** | **No `apply`/`exact`.** `docs/PROOFS.md` §3.8 argues "there is nothing for `apply` to do" — true for forward reasoning, false for backward. | `apply`/`exact` | Proof style | 2–3w |
| **C7** | **No interactive goal display.** `:hole_goal` exists; no goal view after each command. | InfoView | All proof authoring | 4–6w |
| **C8** | **`rewrite` single-occurrence only.** `E111` on multiple matches. | `rw` (all by default) | Proof tedium | 1w |
| **C9** | **Guarded-lambda recursion uncertified** (K-bug 2, open). | `%default total` | Reach, not soundness | 2–3w |
| **C10** | **Elaborator reach gaps** E9, E10, E12, E13, K-bug 1 (open ledger, `kernel/MASTER.md` §9). | — | Reach only | 10–15w |

**Critical sequencing constraint:** C1 must land before C4, C6, and C7 can be
built well — all three are clients of a goal API. C5 is independent. C2 and C3
are independent of everything.

---

## 3. C1 — Goal metaprogramming (the one real architectural gap)

Lean's `Lean.Meta` is what makes `simp`, `omega`, `aesop`, `positivity`, and
every Mathlib tactic possible. Cure has the *syntax* half (`Std.Syntax`,
`computed by`) and the *search* half (`Cure.Elab.ProofSearch`), but no API that
lets user code manipulate a goal.

### C1.1 — Extract the goal state (3w)

1. Define `Goal = %{hyps: [{name, type}], target: Core.t, ctx, meta}` in
   `lib/cure/elab/goal.ex`.
2. Define the tactic result: `{:ok, [Goal]} | {:error, diagnostic}` — a tactic
   returns *remaining* goals, so `[]` closes.
3. Expose combinators: `focus`, `all_goals`, `seq`, `or_else`, `repeat_until_fail`.
4. **Reimplement the six existing proof commands on this API.** This is the
   adequacy proof: if `simplify`/`rewrite`/`induction` can be expressed, the API
   is right. Pure refactor; `E109`–`E115` diagnostics stay byte-identical.

**Gate:** all existing proof-language tests pass unchanged.

### C1.2 — A `tactic` rule kind in `macro` (4w)

1. Extend the `macro` container (`docs/MACROS.md` §2) with
   `tactic <rule> computed by <fn>`, where the expander receives a **goal**
   (not just syntax) and returns goals.
2. The expander is ordinary Cure over a new `Std.Tactic` module — the goal
   analogue of `Std.Syntax`.
3. **Firewall:** a tactic may only *produce goals* and *apply existing
   commands*. It cannot mint a `reflexive`. Every term it emits is re-elaborated
   and kernel-checked — the existing K3 firewall, unchanged.

**Gate:** a test library defines `my_simp` as a tactic macro; the resulting Core
is byte-identical to the hand-written expansion.

### C1.3 — Surface the existing solvers as tactics (3w)

`Cure.Elab.ProofSearch` already has a tagged-lemma resolver and a
`positivity`-style sign solver (`kernel/MASTER.md` §6.3). Wrap them:
`by search`, `by positivity`, `by decide` (over `Std.Decision`).

**Gate:** each has a positive corpus and a negative corpus it must refuse.

---

## 4. C2 — Universe polymorphism (execute the existing spec)

The design is **complete and authoritative**:
`docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`,
phases U0–U7, with §21 completion criteria. **Do not redesign it.** Execute it.

Two things to get right, both already flagged in the spec:

1. **Every generic Core walker must descend into level atoms.** The spec names
   this as a soundness bug if missed. `kernel/MASTER.md` §8 documents that the
   walker-drift class was already instantiated 12×; this is the same failure
   mode with a new former. Add a coverage cell per (walker × level-former).
2. **Serialization version bump.** Every cache/hash containing Core must include
   the universe representation version — artifacts, certificates, interfaces,
   incremental hashes, Antigen corpus.

**Gate:** §21's criteria — `Type : Type` and `TypeLimit : TypeLimit`
unrepresentable; one polymorphic definition works at arbitrary levels; Antigen
sensitive to weakened level equality/ordering/scope.

---

## 5. C3 — Operator fixity (execute Step 3)

Step 2 (sole route) is **landed** (`93ed411d`). Step 3 is specified in
`types/MASTER.md` §7.3 and §7.4:

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
5. Delete the static `Precedence.ex` table; seed builtins from `Std.Operators`.

**Gate:** end state is "the compiler owns NO fixed operator list"; printer
callers thread `fixity(M)`.

---

## 6. C4–C8 — Proof ergonomics (small, independent)

| ID | Work | Notes |
|---|---|---|
| **C4** | `@[simp]` on `@lemma`; `simplify` consults a global set | **Orientation checking is mandatory** — reject a lemma whose LHS does not strictly decrease; reject looping sets. This is what keeps `simplify` terminating. |
| **C5** | Extend `simplify`'s default rules to **certified** unfolding | Reuse `Normalise.unfold_certified_head/3` — do not write a second unfold path. The size-change certificate is the termination witness. Keep the refusal for *uncertified* recursion. |
| **C6** | `apply` / `exact` | Thin clients of C1.1. **Correct `docs/PROOFS.md` §3.8** — its "nothing for `apply` to do" is wrong for backward reasoning. |
| **C7** | `:proof_state` pipeline event + InfoView-protocol goal view | `Cure.Pipeline.Events` already exists and is Registry-backed. Wire into `cure-lsp`, `vscode-cure`, and a `:proof` REPL meta-command. |
| **C8** | `rewrite … all` | **Keep single-occurrence as the default** — it is safer than Lean's silent rewrite-all. `all` is opt-in. |

---

## 7. C9–C10 — Reach gaps (execute the existing ledger)

Both are already scoped in `kernel/MASTER.md` §5.3 and §9. **Do not re-plan.**

- **C9 (K-bug 2):** recognise deferred self-calls under an unapplied lambda as
  not owing the decrease (mirror Idris). TCB change, hard-stop-approved.
  Antibody = a must-certify pin. Completeness, not soundness.
- **C10:** E9 (premise falsified — not a gap), E10 (higher-order in index
  position; do last), E12 (`rewrite` δ-blind occurrence finder), E13 (diagonal
  GADT one-way unification), K-bug 1 (order-dependent ctor injectivity).
  Discipline per gap: red-green oracle-anchored, negative antibody, done = the
  workaround is removed from a real module that still replays `rel=same`.

---

## 8. Execution order

```
Phase 1 (wks 1–4)   ── C5, C8, C4        (independent, immediate payoff)
Phase 2 (wks 1–7)   ── C1.1, C1.3        (goal API + solver tactics)
Phase 3 (wks 5–9)   ── C3                (fixity, parallel to Phase 2)
Phase 4 (wks 8–12)  ── C1.2, C6, C7      (clients of the goal API)
Phase 5 (wks 1–20)  ── C2                (universe polymorphism, long pole)
Phase 6 (parallel)  ── C9, C10           (reach ledger, as capacity allows)
```

**Phase 1 gate:** `simplify` closes a certified-recursive goal; a looping
`@[simp]` lemma is rejected at declaration; `rewrite … all` closes a
multi-occurrence goal.

**Phase 2 gate:** the six existing commands are reimplemented on the goal API
with byte-identical diagnostics and passing tests.

**Phase 4 gate:** a library defines a custom tactic macro; cursor-position goal
display works in VS Code and the REPL.

**Phase 5 gate:** the spec's §21 completion criteria.

---

## 9. Correction to the earlier plan

`LEAN4_MIGRATION_PLAN.md` §Track E recommended **"Stay on Agda; build
Cure-native tactic tooling"** and treated the Agda development as the thing to
extend. That recommendation is **wrong for this goal** and is withdrawn.

Reasons:

1. **The Agda development is about the kernel, not about Cure's ergonomics.**
   Nothing in `proof/` makes a Cure user's proof shorter. Parity work happens in
   `lib/cure/elab/` and `lib/std/`, not in `proof/`.
2. **There is a second-checker decision already locked** that the earlier plan
   missed: `kernel/MASTER.md` §1.1 decision 6 keeps **lean4lean as a second
   checking backend** via forgetful projection — it witnesses the dependent
   skeleton only, never the quantitative layer. That is the sanctioned way Lean
   enters this project, and it is a *checker*, not a toolchain dependency.
3. **Final Core is deliberately Idris/Agda-shaped, not Lean-shaped**
   (`kernel/MASTER.md` §1.1 decision 5): QTT multiplicities, predicative
   cumulative universes, irrelevance via quantity 0, no impredicative `Prop`.
   The QTT→Lean projection is forgetful/mechanical; the reverse is undecidable.
   Parity therefore means **parity of capability, not of calculus.**

The earlier plan's §9 non-goals remain correct and are carried forward.

---

## 10. Definition of done

Cure reaches Lean feature parity when:

1. A user can write a tactic that inspects the goal and decides what to do (C1).
2. `Type(l)` is polymorphic and the ceiling is gone (C2).
3. Operators have declaration-driven, `use`-propagated fixity (C3).
4. `@[simp]` + certified unfolding make `simplify` close computational goals
   (C4, C5).
5. `apply`/`exact` support backward reasoning (C6).
6. Goals are visible at the cursor during proof authoring (C7).
7. The open reach ledger (C9, C10) is closed or explicitly pinned as
   deliberate.

Items 1–6 are ~35–50 engineer-weeks. Item 7 is open-ended and should be
capacity-driven, not gated.

---

## 11. Non-goals (carried forward, unchanged)

- Do not port anything to Lean. Final Core stays Idris/Agda-shaped.
- Do not add `propext` or `Classical.choice` to match Lean's axiom count — the
  two-postulate base (`funext`, `tree-decides`) is better.
- Do not permit termination/positivity pragmas; the bypass allowlist stays empty.
- Do not change `rewrite`'s single-occurrence default.
- Do not let `simplify` declare terms equal because the host computed so.
- Do not delete the `Proof/*Examples.agda` fixtures — they are the non-vacuity
  evidence for the parameterised theorems.
- Do not redesign the universe-polymorphism spec; execute it.
