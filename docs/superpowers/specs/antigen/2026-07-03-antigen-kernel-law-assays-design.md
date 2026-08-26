# Antigen kernel-law assays — design (Run B)

**Status:** approved (design gate — operator batch-approved A/B/C/D). Autopilot on `autopilot/antigen-tier-b`. Pure-Antigen, **kernel-API only** (read-only calls into `Cure.Core.*`; **no TCB edits**).

## 1. Motivation

Antigen's assays check invariants someone thought to state. `Assays.Term` already covers two *unary* term properties — subject reduction (`nf(t)` still checks at `A`) and normalization idempotence (`nf(nf t) = nf t`). But two *relational* families the kernel and Shrink silently depend on are **unchecked**: (a) the **de Bruijn algebra** (`Term.shift`/`Term.subst` laws — a capture or off-by-one bug here corrupts every substitution the kernel and the shrinker perform, invisibly), and (b) **reduction order-independence** (a `whnf` that disagrees with `nf` is a soundness hole). This run adds three *new* relational assays for them, all checkable through the public kernel API alone.

**Scope of correctness here (see §6 for the ladder).** Cure's kernel is Elixir; `Term.t()` is an untyped tagged tuple with bare-integer de Bruijn indices (`{:var, k}`), so scope-*intrinsic* syntax (Agda/Idris/Lean `Fin n`-indexed terms, where the laws are definitional and capture is impossible by construction) is **not expressible in the host language**. This run therefore does *extrinsic property testing* of the de Bruijn laws — the cheapest rung. The stronger rungs (mechanized proof à la Coq **Autosubst**, or a scope-indexed reference the Elixir kernel is differentially checked against) are recorded as a follow-on ladder in §6, not attempted here.

## 2. Architecture — reuse `:typed_term`, add assay-ids

No new challenge **kind**. `:typed_term` challenges already carry `payload.{sig, ctx, type, term}` and have full plumbing (Coverage, Corpus, Shrink, health). The existing type-directed generator entry `Antigen.Generators.Term.typed_term(assay_id)` is how `default_gen` already emits `"term/infer_check"`, `"term/subject_reduction"`, `"term/normalization"` — but **today it is not open to arbitrary assay-ids**: `typed_term/1` is guarded `when assay_id in @assay_ids`, and `@assay_ids` is the closed 3-element list of existing term/* ids. Calling `Term.typed_term("kernel/shift_subst")` against current source raises `FunctionClauseError` (verified empirically). This run must **widen that guard** — the function body never branches on `assay_id` (it only stores it in the challenge's `assay:` field), so the correct minimal fix is loosening the guard to `when is_binary(assay_id)`, **not** adding the three new ids to `@assay_ids` itself: `@assay_ids` also drives `Antigen.Generators.Term.default_gen/0` (a *different* function from `Mix.Tasks.Antigen.default_gen/0`), which `test/antigen/health_gate_test.exs` samples directly — growing `@assay_ids` would silently pull kernel-law challenges into that test's health-gate sample space. Guard-widening avoids that coupling entirely. This run adds three assay-ids dispatched to one new assay module:

- `kernel/shift_subst` — de Bruijn algebra laws
- `kernel/weakening` — typing preserved under an unused binder
- `kernel/confluence` — `whnf`-then-`nf` agrees with `nf`

**Wiring (mirrors Run A / existing verticals):**
- `Antigen.Generators.Term.typed_term/1`'s guard widens from `assay_id in @assay_ids` to `is_binary(assay_id)` (see above); `@assay_ids` itself is untouched.
- New module `Antigen.Assays.KernelLaw` with `run/1` dispatching on `c.assay`.
- `Antigen.Runner.assay_module/1` gains the three id → `Antigen.Assays.KernelLaw` rows.
- `Mix.Tasks.Antigen.default_gen/0` gains three branches: `Term.typed_term("kernel/shift_subst")`, `…("kernel/weakening")`, `…("kernel/confluence")`. **This changes `default_gen`'s branch count from 11 to 14** — Run A's group-guard test (`gen_group_table/0` + the "exactly 11 branches" assertion) and the position→group table **must be updated in lockstep** (the three new branches all emit `:typed_term`, so they extend **Group T**; the guard becomes 14 branches, `t: [4,5,6,9,10,11,12,13,14]`). This is the coupling Run A's guard test was designed to surface — honor it, don't bypass it.

Because these are ordinary `:typed_term`s, they flow through the existing well-formedness filter, coverage dedup, health metrics (binder_usage/reduction_activity), and Shrink for free. No Coverage/Corpus/Challenge changes.

## 3. The three assays (`Antigen.Assays.KernelLaw.run/1`)

Each returns `:ok` or `{:violation, detail}` over `p = c.payload`, with `ctx = SigMenu.rebuild_context(SigMenu.env_of(p.sig), p.ctx)` (the standard reconstruction the other assays use). `t = p.term`.

### 3a. `kernel/shift_subst` — de Bruijn algebra

Checks the σ-algebra laws for the kernel's **targeted, capture-avoiding, non-renumbering** `subst` (confirmed: `subst(u,j,r)` replaces index `j`, shifts `r` under binders, never decrements other indices) and its `shift`. The statements are lifted from the standard single-point de Bruijn calculus (Autosubst / PLFA formulations) rather than hand-invented, so the risk is not "did we make up a false law" but "did we transcribe the index arithmetic correctly" — which the spec-review discharges **empirically** (each law is run over thousands of generated terms; any exception falsifies the transcription and is corrected or the law dropped). Each instance is a pure `Term` computation on `t`:

1. **Shift-zero identity:** `shift(t, 0, c) == t` for `c ∈ {0,1}`.
2. **Shift composition (same cutoff):** `shift(shift(t, a, c), b, c) == shift(t, a + b, c)` for `a,b ∈ {1,2}`, `c ∈ {0,1}`.
3. **Shift/subst commutation (the substitution lemma):** for `c ≤ j`, `shift(subst(t, j, r), a, c) == subst(shift(t, a, c), j + a, shift(r, a, c))` — sampled `j ∈ {0,1}`, `c ∈ {0,1}` (with `c ≤ j`), `a ∈ {1,2}`, `r ∈ {Z, S Z}`. This is the law previously omitted for fear of misstatement; it is now included in its standard prior-art form **and** guarded by the empirical review (below). It is the strongest of the four — a capture or off-by-one bug in either `shift` or `subst` breaks it.
4. **Substitute-a-fresh-index is a no-op:** `subst(shift(t, 1, c), c, r) == shift(t, 1, c)` for any `r` — because `shift(t,1,c)` has no free occurrence of index `c`, so the substitution finds nothing to replace. Sampled `c ∈ {0,1}`, `r ∈ {Z, S Z}`.

A violation returns `{:violation, {:shift_subst_law, which_law, lhs, rhs}}`. **Spec review must empirically confirm all four laws hold with ZERO exceptions over a large sample of generated terms before they ship** — a law that fails even once (most likely law 3's cutoff arithmetic) is either corrected to the form that actually holds for this kernel or removed; a false law here is the highest-severity possible finding (it would infect a sound kernel). Laws 1–2 and 4 are unconditionally true for this calculus; law 3 is the one whose exact indices the review pins down. (This requirement is already satisfied by a preview pass directly against the live kernel — see §8's first risk bullet for the numbers; Stage 4 re-proves it against the shipped `Antigen.Assays.KernelLaw` code via the TDD in §4.)

### 3b. `kernel/weakening` — unused-binder invariance

If `infer(ctx, t) = {:ok, v}`, then inserting an unused binding at the front and shifting `t` past it must still type, at the weakened type. Concretely, for a fresh domain `A` (reuse a menu type, e.g. `Nat` as a `Value` via the kernel's own evaluation of `{:data,:Nat,[],[]}`):

- Let `ctx' = Context.extend(ctx, A_value)` and `t' = Term.shift(t, 1, 0)`.
- **Success-preservation (floor):** `infer(ctx, t)` ok ⟹ `infer(ctx', t')` ok. A weakening bug that breaks typability is caught here.
- **Type agreement (if both succeed):** quoting both inferred type-values to terms — `q = Normalise.quote(v, Context.length(ctx))`, `q' = Normalise.quote(v', Context.length(ctx'))` — must satisfy `q' == Term.shift(q, 1, 0)`. The weakened context's inferred type is exactly the original type shifted past the new binder.

Violations: `{:violation, {:weakening_broke_typing, err}}` or `{:violation, {:weakening_type_mismatch, q, q'}}`. If `infer(ctx, t)` itself fails (a genuinely ill-typed generated term — possible if the generator's guarantee is imperfect), the law is **vacuously satisfied** (`:ok`) — this assay tests weakening, not the generator; a bare infer failure is not a weakening violation.

### 3c. `kernel/confluence` — reduction order-independence

`nf` reached via a `whnf` prefix must equal `nf` reached directly:

- `full = Normalise.nf(ctx, t, fuel: Assays.Term.assay_fuel())`
- `staged = case Normalise.whnf(ctx, t, fuel: …) do :fuel_exhausted -> :skip; w -> Normalise.nf(ctx, w, fuel: …) end`
- If either `full` or the inner `nf` is `:fuel_exhausted` (or `whnf` exhausts), return `:ok` (**vacuous** — fuel exhaustion is a resource bound, not a confluence violation; the existing health line already tracks fuel exhaustion separately).
- Otherwise assert `full == staged` (syntactic equality of normal forms). Violation: `{:violation, {:confluence_mismatch, full, staged}}`.

## 4. Testing (TDD, per Stage 4)

Unit tests in `test/antigen/assays/kernel_law_test.exs`, driving `Antigen.Assays.KernelLaw.run/1` on hand-built `:typed_term` challenges (no sampling in the unit tests — deterministic fixtures):

1. **shift_subst positive:** a fixture term (`λNat. S (var 0)` under empty ctx) satisfies all four laws → `:ok`. **shift_subst negative:** a *stubbed* violation is not directly constructible without a broken kernel, so instead assert the law-checker itself computes the identities correctly by re-deriving law 2/3's two sides in the test and asserting they match what the assay compares (guards against the assay tautologically returning `:ok`). (This is the same "does the check actually check" concern Run A's plan review raised; the real adversarial negative lives in Run C, which injects a broken kernel.)
2. **weakening positive:** a closed well-typed `t` (e.g. `S Z : Nat`) → `:ok`, and the type-agreement leg holds (`quote` of the weakened inference equals `shift(quote(orig),1,0)`). **weakening vacuous:** an ill-typed term → `:ok` (vacuous), not a false violation.
3. **confluence positive:** a redex fixture (`(λNat.var 0) (S Z)`) normalizes identically via `nf` and `whnf`→`nf` → `:ok`. **confluence vacuous:** if a fixture exhausts fuel, `:ok`.
4. **registry + guard:** `Runner.assay_module_for("kernel/shift_subst")` (and the other two) returns `Antigen.Assays.KernelLaw`; the updated `default_gen` group-guard test asserts **14** branches with `t: [4,5,6,9,10,11,12,13,14]`. Also: `Term.typed_term("kernel/shift_subst")` (and the other two) returns a `Gen.t()` instead of raising `FunctionClauseError` — this is the red test that drives the `typed_term/1` guard-widening in §2/§5 (write it first; it fails against current source, passes once the guard is `is_binary(assay_id)`).
5. **integration:** a short `Runner.explore` over `Term.typed_term("kernel/confluence")` (and the other two) runs to completion with 0 infections on the current (sound) kernel — evidence the assays don't false-positive on real generated terms.
6. **Stage 5:** full suite once + `mix antigen --count 800` showing the three new verticals participate (health lines unaffected; 0 infections).

## 5. Files

- **Create:** `lib/antigen/assays/kernel_law.ex`, `test/antigen/assays/kernel_law_test.exs`.
- **Modify:** `lib/antigen/generators/term.ex` (widen `typed_term/1`'s guard from `assay_id in @assay_ids` to `is_binary(assay_id)`; `@assay_ids` itself unchanged — see §2), `lib/antigen/runner.ex` (3 `assay_module/1` rows; **update `@group_table` + `gen_group_table/0` to 14 branches**), `lib/mix/tasks/antigen.ex` (`default_gen/0` +3 branches), `test/antigen/runner_test.exs` (update the group-guard test to 14).
- **Untouched:** `Cure.Core.*` (TCB), Coverage, Corpus, Challenge, Shrink, `Antigen.Generators.Term.@assay_ids`/`default_gen/0`, `test/antigen/health_gate_test.exs`.

## 6. Correctness ladder (what this run is, and the follow-ons)

De Bruijn correctness can live at four rungs of increasing rigor and cost. **This run is Tier 1 only** (operator decision: extrinsic property testing in Antigen for now). The rest are documented here as follow-ons — **not scheduled**, no work opened.

| Tier | Where the law lives | Bootstrapping? | Hardens the *real* Elixir kernel? | Status |
|---|---|---|---|---|
| **1** | **Elixir property tests (this run's §3a/b/c)** | no | yes, on tested inputs | **this run** |
| 2 | Cure proof about a *Cure-defined* term algebra (`Term : Nat → Type`, `shift`/`subst` proved in Cure) | no | no — certifies a paper model, not the running kernel | optional showcase |
| 3 | Self-hosted kernel + Cure proof binding it (extraction) | **yes** | yes, fully | deferred; research-scale (cf. CakeML, Agda-in-Agda) |
| 4 | Idris `Fin`-indexed reference, differential-checked against the Elixir kernel (rides the existing transliteration/differential-oracle harness; well-scoped *by construction*) | no | yes, vs a trusted oracle, on tested inputs | follow-on, own design gate |

The tell that motivated stating §3a's laws in prior-art form: Coq's **Autosubst** mechanically *proves* exactly the σ-laws §3a tests (including law 3's commutation) — so the correct statements are known; we borrow the statements (Tier 1) and defer borrowing the proofs (Tiers 2–4).

## 7. Non-goals (YAGNI)

- **Tiers 2–4 above** — no Cure code, no Idris reference, no bootstrapping in this run.
- A **new challenge kind** for kernel laws (reusing `:typed_term` gets all plumbing free).
- **Generating deliberately-ill-typed terms** to stress weakening — Run C (assay sensitivity) supplies the adversarial negative by injecting a broken kernel; here the kernel is trusted and the assays must be quiet on it.
- Confluence across *arbitrary* reduction strategies — only the two the kernel exposes (`whnf`, `nf`).
- **Parallel/simultaneous substitution laws** (the full σ-calculus with substitution *sequences*) — the kernel's `subst` is single-point, so §3a's single-point laws are the matching set.

## 8. Risks

- **A stated law is subtly false** → the assay infects a sound kernel (false positive) — the highest-severity failure mode. This is concentrated in §3a law 3 (commutation index arithmetic). Mitigation: laws 1–2 and 4 are unconditionally true; law 3 is lifted from prior art. **Spec review has already run all four (via ad hoc probes against the live kernel, standing in for the eventual `Antigen.Assays.KernelLaw` code) over 500 real generator-drawn terms plus dozens of hand-built terms — deep binders, dependent `Vec` indices, `case`, `eq` — with 0 exceptions.** Stage 4's TDD must still assert these as hard failures in the shipped assay, and ongoing fuzzing (`mix antigen --count 800`, §4 item 6) continues to exercise more terms; any future failure corrects or drops the law.
- **`default_gen` grows to 14 and Run A's guard test isn't updated** → guard goes red (by design). Mitigation: §2/§5 make the lockstep update explicit; the guard failing is the safety net working.
- **`quote` depth/shift mismatch in weakening** makes the type-agreement leg wrong. Mitigation: success-preservation is the floor (always sound). **Spec review has already pinned the exact form — `quote(v', len+1) == shift(quote(v, len), 1, 0)` — and confirmed it empirically over 500 real generator-drawn terms with 0 exceptions, including the dependent-index case (`Vec[var:1]` → `Vec[var:2]`)**; Stage 4 ships the type-agreement leg as-specified rather than degrading to success-preservation only.
- **Confluence is vacuous if the generator only emits normal forms** (no redexes → `whnf` = `nf` = `t` trivially). **Retired empirically: spec review measured that 189 of 500 real `Term.typed_term`-generated terms have `whnf(t) != t` (a genuine head redex) — the generator already produces reducible terms at a healthy rate, so no seeded-redex workaround is needed.** As a durable backstop rather than a one-time check, Stage 4 should still surface the redex/already-normal split on a health line so a future generator change that silently drove it toward vacuity would be visible rather than passing silently.
