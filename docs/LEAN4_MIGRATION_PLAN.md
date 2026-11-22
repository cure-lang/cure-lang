# Lean 4-Style Proofs: Migration Plan

**Historical and superseded.** Use [`PATH_TO_LEAN4.md`](PATH_TO_LEAN4.md) for
scope and phase numbering, and [`LEAN4_PARITY_STATUS.md`](LEAN4_PARITY_STATUS.md)
for measured implementation status. This older plan contains withdrawn
recommendations and inaccurate capability claims; it is not an execution guide.

Companion to [`LEAN4_READINESS_AUDIT.md`](LEAN4_READINESS_AUDIT.md). Every step
below cites a gap ID from that audit's §8 register.

**Scope decision, stated up front:** this plan does **not** port the Agda
development to Lean. Audit §9 item 1 records why: 238 modules with a
two-postulate base would cost 6–12 months to reproduce and would buy nothing on
L1/L2. "Lean 4-style" here means **Lean 4-style *proof ergonomics and
definitional equality*, on top of the existing Agda metatheory**. Where Lean's
*toolchain* is genuinely needed (interactive goal display), we adopt the
protocol, not the language.

---

## Track A — Definitional equality that computes (G1)

**Goal:** `reflexive` closes any goal whose sides are definitionally equal
including multi-step reduction of certified-total recursive definitions; a goal
like `plus(Z, plus(Z, value)) == value` needs no `proof chain`.

**Why first:** G1 is the inner loop of every proof. It is also the cheapest
high-impact item because the mechanism already exists — `Normalise.unfold_certified_head`
already unfolds certified globals during conversion, gated on
`Env.certified?/2` (`docs/SOUNDNESS.md` §3.2).

### A1. Expose certified unfolding to `simplify` (effort: 2w)

1. In `lib/cure/elab/` (the `simplify` implementation), extend the default rule
   set to include **certified definitional unfolding**: for a goal subterm
   headed by `{:global, name}`, unfold iff `Env.certified?(sig, name)`.
2. Reuse `Normalise.unfold_certified_head/3` — do not write a second unfold
   path. The certificate is the termination witness; this is what makes the
   rule set terminating.
3. Bound the unfold depth by the same fuel the conversion checker uses. On
   exhaustion, leave the goal open and report `E112` with the residual goal —
   never claim closure.
4. Keep the existing refusal for **uncertified** recursion. `docs/PROOFS.md`
   §3.4's guarantee ("it will not unfold arbitrary recursive definitions") is
   preserved exactly; only the *certified* subset is added.

**Acceptance:** the `TwoSteps` example in `docs/PROOFS.md` §3.2 compiles with a
bare `simplify` (or `reflexive`), not a two-step chain. A non-certified
recursive definition still fails to unfold, pinned by a negative test.

### A2. Add `rfl`-by-computation as a goal closer (effort: 1w)

1. When the goal is `Equivalent(a, x, y)`, attempt conversion of `x` and `y`
   via the existing `Conv.conv?/5` before requiring syntactic reflexivity.
2. On success, emit `reflexive(…)` at the elaborated endpoints. On failure,
   report the two normal forms.
3. This is a *checker* improvement, not a kernel change — `Conv` already
   decides this; the elaborator simply was not asking.

**Acceptance:** `fn id_plus(v: Nat) -> Equivalent(Nat, plus(Z, v), v) = reflexive(v)`
compiles. Negative: `Equivalent(Nat, Z, S(Z))` still fails, with both normal
forms in the diagnostic.

### A3. Prove the elaboration is sound (effort: 1w)

1. Add `proof/Proof/SimplificationSoundness.agda`: every rule `simplify` applies
   yields a native `_⇝*_` path, hence a `Conversion._≈_` witness.
2. Model the *certified-unfold* rule as an instance of the existing δ rule
   gated on the existing `Certified` hypothesis — no new postulate.
3. Model the bounded-fuel behaviour as a partial function with an explicit
   `exhausted` outcome (mirror `Proof.ClosureEval`'s `Result` shape).

**Acceptance:** `simplification-sound` proved with no new postulate; registered
in `proof/check.sh`; `check-postulates.sh` unchanged.

---

## Track B — An open tactic framework (G2, G3, G4, G13, G14)

**Goal:** proof commands become a *library* over a tactic API, not a closed
DSL hard-coded in the elaborator.

**Sequencing note:** B1 must land before B2–B5, because every subsequent item
is a client of the API. This is the largest single work item in the plan.

### B1. Extract `Cure.Elab.Tactic` — the tactic monad and API (effort: 4w)

1. Define a goal state: `%{hyps: [{name, type}], goal: Core.t, meta: ctx}`.
2. Define the tactic result: `{:ok, [goal]} | {:ok, []} | {:error, diagnostic}`
   — a tactic returns the *remaining* goals, so `[]` means closed.
3. Define the core combinators: `focus`, `all_goals`, `seq`, `or_else`,
   `repeat_until_fail`. These are the Lean `Lean.Elab.Tactic` primitives.
4. Reimplement the existing six commands (`have`, `proof chain`, `because`,
   `simplify`, `rewrite`, `induction`) **on top of the API**. This is a pure
   refactor with no behaviour change and is the proof that the API is adequate.
5. Keep the elaborator's existing `E109`–`E115` diagnostics byte-compatible.

**Acceptance:** all existing proof-language tests pass unchanged; the six
commands are now ordinary clients of `Cure.Elab.Tactic`.

### B2. `macro`/`syntax` for tactics (effort: 5w)

1. Extend the existing `macro` container (`docs/MACROS.md`) with a
   `tactic` rule kind, so a library can define a new proof command.
2. Tactics expand to sequences of `Cure.Elab.Tactic` combinators — **not** to
   Core terms, so a user tactic cannot introduce an unchecked node.
3. Enforce: a user tactic may only *produce goals* and *apply* existing
   commands. It cannot mint a `reflexive` without going through the checker.

**Acceptance:** a test library defines `my_simp` as a tactic macro and uses it
in a proof; the resulting Core is byte-identical to the hand-written expansion.

### B3. A global, attribute-driven simp set (G3, effort: 2w)

1. Add `@[simp]` on `@lemma`-annotated definitions (`docs/PROOFS.md` §4 already
   has `@lemma` and generated defining equations).
2. `simplify` consults the global set plus the call-site `using [rules]` list.
3. **Orientation checking is mandatory**: reject a `@[simp]` lemma whose LHS
   does not strictly decrease under a fixed term ordering, and reject a set
   that would loop. This is the property that keeps `simplify` terminating —
   do not weaken it.
4. Generated defining equations are registered `@[simp]` automatically.

**Acceptance:** a file with three `@[simp]` lemmas proves its goals with bare
`simplify`; a looping `@[simp]` lemma is rejected at declaration with a
diagnostic naming the cycle.

### B4. Goal-state introspection and an LSP goal view (G4, effort: 4w)

1. Emit a `:proof_state` pipeline event (`Cure.Pipeline.Events` already exists
   and is Registry-backed) carrying `%{goals: [...], hyps: [...], cursor: pos}`.
2. Extend `:hole_goal` to carry the same payload, so holes and mid-proof states
   are the same shape.
3. Implement the **Lean InfoView protocol** — i.e. a text/JSON rendering of the
   goal state — and wire it into `cure-lsp` and the `vscode-cure` extension.
4. Add `cure proof` (or a `:proof` REPL meta-command) that steps a proof and
   prints the goal after each command.

**Acceptance:** placing the cursor after any proof command in VS Code shows the
remaining goals and hypotheses; the same payload is available from the REPL.

### B5. `apply` / `exact` (G13, effort: 2w)

1. `exact e` — check `e` against the goal, close on success.
2. `apply e` — infer `e`'s type, unify its conclusion with the goal, emit the
   resulting premises as new goals.
3. Both are thin clients of the B1 API. This directly contradicts
   `docs/PROOFS.md` §3.8's claim that "there is nothing for `apply` to do" —
   that claim is true only for forward reasoning; record the correction.

**Acceptance:** `docs/PROOFS.md` §3.8 is rewritten; a backward-reasoning
example compiles.

### B6. `rewrite … all` (G14, effort: 1w)

1. Add an `all` modifier to `rewrite`. Keep single-occurrence as the default
   (audit §9 item 4 — this is safer than Lean).
2. `all` rewrites every occurrence, in a deterministic left-to-right order,
   using the existing recursive congruence search.

**Acceptance:** a multi-occurrence goal is closed by `rewrite using h all`
followed by `simplify`.

### B7. Decision procedures (G5, effort: 6–10w, parallelisable)

Each is a separate tactic, in priority order:

1. **`decide`** — for goals in `Std.Decision`, evaluate the decision procedure
   and emit the corresponding evidence. Cheapest; `Std.Decision` already
   exists.
2. **`omega`** — linear integer/natural arithmetic. `Std.Proof.LinearArithmetic`
   already provides "checked linear-arithmetic reflection"; wire it as a tactic
   that discharges goals in its fragment, and *fail closed* outside it.
3. **`norm_num`** — literal arithmetic evaluation.
4. **`ring`** — only if the stdlib gains a ring structure; otherwise skip.

**Acceptance:** each tactic has a positive corpus and a negative corpus
(goals it must refuse), and each emits only Core the kernel re-checks.

---

## Track C — Executable soundness (G6–G12)

This track is independent of A and B and should run in parallel. It is the
"make the theorem *about the real thing*" track. It is already planned in
detail — **do not re-plan it here**; execute the existing milestones.

| Gap | Existing plan | Next action |
|---|---|---|
| G6 totality | `proof/PLAN.md` M11 | Prove the size-change principle (or the verifier-implies-termination direction) |
| G7 executable refinement | `proof/PLAN.md` M4, `M4B-PLAN.md` | Redesign the `run-config` worker per `UnboundInversion` |
| G8 η integration | `proof/PLAN.md` M5b | Migrate `Conversion` consumers onto `_≈η_`; prove rename/subst stability |
| G9 `unbound` | `M4B-PLAN.md` §8 | Fuel-indexed evaluator returning values only, related by a separate soundness theorem |
| G10 dependent signatures | `proof/PLAN.md` M7 | Migrate soundness consumers to `Core.DependentTyping` |
| G11 erasure simulation | `proof/PLAN.md` M9 | Wire `eraseSpine` into `eraseTerm`; prove typed simulation |
| G12 BEAM lowering | `proof/PLAN.md` M10 | Define semantics for the emitted Erlang abstract-form subset |

**Invariant for all of Track C** (from `proof/PLAN.md` §3): no new postulate,
no hole, no termination override, no callback that assumes the theorem it
proves. `check-postulates.sh` and `check-hygiene.py` enforce this — keep them
green at every checkpoint.

---

## Track D — Artifact completeness (G15, G16)

| Gap | Next action | Effort |
|---|---|---|
| G15 kernel-acceptance → certificate | Instrument `Kernel.check` to emit recipes on success; prove the emitted recipe replays to the same native evidence | 10–15w |
| G16 producer correspondence | Make the independently decoded canonical data authoritative, so the Elixir producer is a convenience rather than a trust root | 8–12w |

**Note:** G16's cheapest resolution is architectural, not formal — if the
canonical data is decoded and re-checked by the proved Agda decoder, an
incorrect producer produces a *rejected* artifact rather than a false theorem.
Prefer that over proving the Elixir code correct.

---

## Track E — Toolchain decision (G17)

**Decision required before Track B4.** There is currently no Lean toolchain
(`lean`/`lake`/`elan` absent, zero `.lean` files, no `lakefile`).

Three options, with a recommendation:

| Option | Cost | Buys | Recommend |
|---|---|---|---|
| **E1. Stay on Agda; build Cure-native tactic tooling** | 0 setup | Full control; no new trust root; keeps the two-postulate base | ✅ **Recommended** |
| E2. Add Lean as a *second* metatheory for new results | 2–3w setup + per-module cost | Lean's `simp`/`omega` for free on new work | ❌ Splits the axiom inventory across two provers |
| E3. Port the 238 modules to Lean | 6–12 months | Nothing on L1/L2 (audit §9 item 1) | ❌ Do not |

If E1: adopt Lean's *protocols* (InfoView JSON for B4, tactic-monad shape for
B1) without adopting Lean itself. This is what gives "Lean 4-style" ergonomics
while preserving the stronger axiom position.

---

## Execution order and gates

```
Phase 1 (weeks 1–6)    ── A1, A2, A3  ──┐
                                          ├─→ Phase 3 (weeks 11–22) ── B2, B3, B5, B6
Phase 2 (weeks 1–4)    ── B1            ──┘
                                          └─→ Phase 4 (weeks 20–30) ── B4, B7

Phase C (parallel, weeks 1–130) ── Track C milestones in proof/PLAN.md order
Phase D (parallel, weeks 1–40)  ── Track D
```

**Phase 1 gate:** `reflexive` closes a certified-recursive goal; a
non-certified one does not; `simplification-sound` is proved with no new
postulate.

**Phase 2 gate:** all six existing proof commands are reimplemented on
`Cure.Elab.Tactic` with byte-identical diagnostics and passing tests.

**Phase 3 gate:** a library defines a custom tactic macro; a `@[simp]` set
proves goals with bare `simplify`; a looping `@[simp]` lemma is rejected.

**Phase 4 gate:** cursor-position goal display works in VS Code and the REPL;
`decide` and `omega` each have positive and negative corpora.

---

## Definition of done

"Lean 4-style proofs" is reached when **all** of the following hold:

1. `reflexive` closes every goal whose sides are definitionally equal under
   certified reduction (G1 closed).
2. A library can define a new proof command without editing the compiler (G2,
   G3 closed).
3. A user can see the goal state at any point in a proof, in the editor (G4
   closed).
4. Arithmetic goals in the linear fragment are discharged by a tactic (G5
   closed).
5. The soundness theorem's `Certified` hypothesis means *termination*, and the
   theorem is about `Eval`/`Quote`/`Conv` rather than `_⇝_` (G6, G7 closed).
6. Every `Kernel.check` acceptance yields a replayable certificate (G15
   closed).

Items 1–4 are the *ergonomic* definition and are achievable in ~26–39 weeks.
Items 5–6 are the *soundness* definition and are the existing `proof/PLAN.md`
programme, ~75–130 weeks. They are independent; do not gate one on the other.

---

## Non-goals (from audit §9)

Do **not**, as part of this migration:

- port the Agda development to Lean (E3);
- add `propext` or `Classical.choice` to "match" Lean's axiom count;
- permit any termination/positivity pragma — the bypass allowlist stays empty;
- change `rewrite`'s single-occurrence default;
- let `simplify` declare terms equal because the host computed so;
- delete the `Proof/*Examples.agda` fixture modules — they are the non-vacuity
  evidence for the parameterised theorems.
