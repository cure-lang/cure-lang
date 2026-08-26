# Antigen Beyond the Kernel — Property-Testing the Untrusted Dependent-Type Machinery

**Status:** design draft (operator-requested; NOT yet through the autopilot design gate)
**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03
**Relates to:** the Antigen metatheory engine; the SMT-out-of-TCB decision; the
erasure `{0,ω}` relevance-check decision.

## 1. Motivation

Antigen today tests the **kernel** — the trusted computing base (`Cure.Core.*`:
`Kernel`, `Conv`, `Normalise`, `Eval`, `Inductive`, …). But a dependent-type
implementation is far larger than its kernel, and the parts *outside* the TCB
carry real soundness risk. Two facts from the current codebase:

- **Coverage is kernel-concentrated.** Antigen assays/generators reference
  `Cure.Core.*` heavily but touch only two `Elab` modules superficially
  (`Elab.Relevance`, `Elab.Program`). These untrusted modules have **zero**
  Antigen coverage: `Elab.Elaborator`, `Elab.Unify`, `Elab.Erase`,
  `Elab.TotalityClosure`, `Elab.Emit`, `Elab.Subst`, `Types.Reduce` (a second,
  surface-level normalizer), `Types.Unify`, `SMT.Solver`, `SMT.Translator`.
- **The one elaborator assay is not a soundness assay.** `Antigen.Assays.Elab`
  checks elaborator *completeness* (a well-typed surface program must
  elaborate), *metamorphic* invariance (a typing-preserving transform must not
  flip the verdict), and the erasure *relevance* pin. It does **not**
  independently re-check the elaborator's emitted Core term against the kernel.
  It trusts `elaborate/2`'s own `{:ok, …}`.

"The kernel re-checks everything, so the rest is untrusted" is the standard
safety argument — but it only holds if (a) the emitted core is *actually*
re-checked, and (b) the untrusted components that the kernel does **not**
re-derive (the unifier's solutions, the totality-closure's certification, the
SMT lint's discharges, the surface normalizer's definitional-equality verdicts)
are independently sound. Neither is currently tested. This spec closes that.

## 2. The organizing principle — the kernel is the oracle

Every untrusted component `C` gets assays of at most two flavors:

1. **Consistency-with-oracle (differential).** Whenever `C` makes a claim
   (elaborates a term, solves a unification, normalizes an expression, certifies
   totality, discharges an obligation), the **trusted** TCB must independently
   agree. The oracle is `Cure.Core.Kernel` / `Conv` / `Normalise` — themselves
   already under test by the existing kernel assays. A disagreement is an
   **infection**: a bug in `C`, or — a valuable bonus — a *second* catch on the
   kernel (if the untrusted component is right and the oracle is wrong, that is a
   TCB soundness bug the kernel assays missed).

2. **Intrinsic algebraic law.** Properties that need no oracle: idempotence,
   determinism, occurs-check (no cyclic solution), well-scopedness, monotone
   size, round-trip. These pin `C`'s internal invariants directly.

The **infection/incompleteness polarity** from the kernel work carries over:
- an untrusted **accept** the oracle rejects, or an untrusted **claim** the
  oracle contradicts, is a *soundness* infection (the dangerous direction);
- an untrusted **reject** of something the oracle accepts is an *incompleteness*
  bug (a reach gap — surfaced, lower severity), exactly as the existing
  `elab/completeness` assay already frames it.

This mirrors the kernel assays' catalog design (known-label + negative controls)
and reuses the existing challenge/assay/generator/corpus architecture verbatim —
each vertical below is "one more assay family," not new infrastructure.

## 3. Verticals

Each vertical names its **target module(s)**, the **oracle**, the **soundness
property** (differential), and **intrinsic laws**. Signatures are quoted from the
current source so the eventual plan is groundable.

### V1 — Normalizer (headline; recommended Phase 1)

**Trusted side — deepen `Cure.Core.Normalise`.** Run B added shift/subst algebra,
weakening, and confluence. Remaining metatheoretic laws with no current assay:

- **NF idempotence:** `nf(ctx, nf(ctx, t)) ≡ nf(ctx, t)`.
- **WHNF↝NF agreement:** the head former of `whnf(ctx, t)` matches the head of
  `nf(ctx, t)` (whnf never disagrees with full nf on the outermost constructor).
- **Determinism:** `nf` is a function — same `(ctx, t)` → identical output across
  runs and fuel ≥ the fixpoint fuel.
- **Eval/quote round-trip:** `quote(eval(t)) ≡ nf(t)` for closed `t` (the NbE
  identity the kernel relies on).

**Untrusted side — `Cure.Types.Reduce`** (`normalize/2`, `equal?/3`,
`substitute/2`; operates on surface `ast()`). Its arithmetic is delegated to the
trusted kernel via `CoreBridge.to_core → Eval.eval → Quote.reify →
CoreBridge.from_core`, so the **untrusted surface is the bridge translation, the
`structural_congruence` fallback, and surface `do_substitute`.** Properties:

- **Differential vs the kernel (soundness):** for a surface expression `e` that
  the bridge can translate, `Types.Reduce.normalize(e, β)` reified to core must
  be `Conv`-equal to `Core.Normalise.nf` of the same expression's core image
  under the corresponding core bindings. A disagreement means the bridge or the
  congruence fallback corrupts meaning.
- **`to_core ∘ from_core` round-trip:** translating a reducible ast to core and
  back is stable on the translatable fragment.
- **substitute/normalize commute:** `normalize(substitute(e, β)) ==
  normalize(e, β)` (substitution before folding = folding with bindings).
- **`equal?` is a sound congruence:** reflexive, symmetric, and `equal?(a, b, β)`
  ⟺ `normalize(a, β) == normalize(b, β)`; **and** `equal?` never contradicts the
  trusted `Conv` on the translatable fragment (an untrusted "definitionally
  equal" the kernel says are distinct is the soundness direction).
- **Intrinsic:** idempotence (`normalize(normalize(e)) == normalize(e)`),
  determinism, and the module's own stated invariant *"result is always
  syntactically smaller-or-equal to the input"* (a monotone-size law — a real,
  checkable claim from its moduledoc).

### V2 — Unifier

**Target:** `Cure.Elab.Unify.unify(t, u, MetaCtx, Env) :: {:ok, MetaCtx} |
{:error, …}` (and `Cure.Types.Unify.unify/2,3`). **Oracle:** trusted `Conv`.

- **Soundness (differential):** if `unify(t, u, ctx, env) = {:ok, ctx'}`, then
  applying `ctx'`'s metavariable solutions to `t` and `u` yields terms that are
  `Conv`-convertible. A unifier that reports success with a substitution that
  does **not** actually unify is a soundness hole the kernel may not catch.
- **Intrinsic:** occurs-check (no returned solution is cyclic, `?m := f(?m)`);
  solutions are **well-scoped** (a solution for `?m` mentions no variable out of
  `?m`'s context); idempotent substitution (applying `ctx'` twice = once);
  determinism.
- **Incompleteness (surfaced):** two terms that are `Conv`-equal but that
  `unify` reports `{:error, …}` for is a reach gap (lower severity).

### V3 — Elaborator soundness

**Target:** `Cure.Elab.Elaborator.elaborate/2 :: {:ok, Term, Value} | {:error}`.
**Oracle:** trusted `Kernel.check/3`.

- **The master property:** if `elaborate(surface, env) = {:ok, core, ty}`, then
  `Kernel.check(ctx, core, ty) = :ok` — the emitted core term **independently**
  type-checks at the emitted type. This is precisely what the current
  `elab/completeness` assay omits (it accepts `elaborate`'s self-reported `:ok`).
  An elaborator that emits a core term the kernel rejects, or annotates it with a
  type the term does not have, is caught here.
- Reuses the existing `:elab_program` challenge kind and surface-program
  generators (`elab_complete.ex`), so V3 is a *new assay over existing
  generators* — the cheapest high-value vertical after V1.

### V4 — Erasure & relevance

**Target:** `Cure.Elab.Erase.erase/2`, `Cure.Elab.Relevance`. **Oracle:** kernel
acceptance + the existing erasure assay.

- **Erasure preserves acceptance (differential):** for a well-typed core term,
  its erasure is still well-formed and (where a runtime type applies) still
  kernel-acceptable — erasure drops *only* computationally-irrelevant
  (quantity-0) sub-terms, consistent with the locked `{0,ω}` relevance decision.
- **Intrinsic:** erasure idempotence (`erase(erase(t)) == erase(t)`); erasure
  only removes quantity-0 constructor arguments (differential vs `Relevance`);
  no hole survives erasure of a hole-free term (`has_hole?` stays false).

### V5 — Totality closure

**Target:** `Cure.Elab.TotalityClosure.certify_type_level(env) :: {:ok, Env} |
{:error, {:totality_required, name}}`. **Oracle:** the trusted totality checker /
the existing `Totality` assay + `Normalise` halting.

- **Soundness (differential):** if `certify_type_level` returns `{:ok, env}`,
  every type-level function it certified must genuinely terminate (its
  normalization halts within fuel on the generated arguments). A **diverging**
  function certified total is a type-level non-termination hole → logical
  inconsistency. Reuses the `totality/diverging` generators as the adversarial
  input (a known-diverging function must be *rejected*, not certified).
- **Incompleteness (surfaced):** a genuinely-total function the closure refuses
  to certify is a reach gap.

### V6 — SMT lint soundness

**Target:** `Cure.SMT.Solver.check_sat/2,3`, `prove_implication/4`,
`check_refinement_subtype/4`. **Framed by the locked decision that Z3 is OUT of
the TCB — the SMT layer is an untrusted lint, never a proof.** So the property is
*lint soundness*, not completeness.

**Z3 is a guaranteed part of the toolchain** (it ships with the language, not an
optional test-env dependency), so this vertical is **unconditional** — never
skipped/gated on solver availability. The only implementation concern is solver
*nondeterminism* (timeouts → `:unknown`): the assay treats `:unknown`/timeout as
a legal, non-infecting answer and pins determinism with a fixed solver config
and a committed fuel/timeout budget, exactly as the other assays fix their
kernel fuel constants — so a banked antibody replays identically.

Properties:

- **Never discharge a false obligation (soundness):** `prove_implication(p, q, …)`
  returning `true` (or `check_sat` returning `:unsat` for a negated goal) must
  agree with the kernel on the fragment both handle — the lint must never claim
  "proven" for an implication that is actually false. A false discharge would let
  an unsound refinement through.
- **Witness consistency (intrinsic):** when `check_sat` returns `:sat` with a
  model, the model actually satisfies the constraint; `:unknown` is always a
  legal, non-infecting answer (an untrusted lint is allowed to give up).
- Differential is scoped to the decidable overlap (linear integer arithmetic /
  boolean); outside it, `:unknown` is expected and never an infection.

## 4. Scope for the first implementation (Phase 1 = V1, the normalizer)

The operator asked specifically for the **normalizer**, so Phase 1 is V1. It is
also the most self-contained: the trusted-side laws reuse existing Core term
generators, and the untrusted-side differential has a ready oracle in
`CoreBridge` + `Core.Normalise`.

**New challenge kinds**
- `:nf_law` — a closed/typed Core term + a law tag (`:idempotent` |
  `:whnf_agrees` | `:deterministic` | `:nbe_roundtrip`). Trusted-side V1.
- `:reduce_diff` — a surface-level `ast()` + core bindings. Untrusted-side V1
  (`Types.Reduce` vs `Core.Normalise`).

**New generators**
- `lib/antigen/generators/nf_law.ex` — draws Core terms (reuses the Tier-B
  `Term` generator surface) tagged with a law; reducible/redex-bearing terms
  biased in so idempotence/whnf are non-vacuous.
- `lib/antigen/generators/reduce_diff.ex` — draws the *translatable* surface-ast
  fragment `Types.Reduce`/`CoreBridge` support (binary arithmetic/boolean ops,
  literals, variables, tuples/projections per `Reduce`'s moduledoc), plus
  bindings, so the differential lands on the bridge, not on untranslatable noise.

**New assays** (each `run/1 :: :ok | {:violation, term()}`, kernel calls
read-only)
- `lib/antigen/assays/nf_law.ex` — the four trusted-normalizer laws.
- `lib/antigen/assays/reduce_diff.ex` — the untrusted-normalizer differential +
  round-trip + substitute-commutes + `equal?`-congruence + monotone-size +
  idempotence/determinism.

**Wiring** (mirrors every prior vertical)
- `Antigen.Challenge` — register `:nf_law` / `:reduce_diff` kinds, their
  `to_pieces`/`from_pieces` clauses (both carry Core `Term` pieces, so they ride
  the corpus codec and — bonus — the Run D triage pass for free), and any new
  interned atoms.
- `Antigen.Runner` — assay registry entries (`"nf/idempotence"` etc.);
  `default_gen` group membership; health/vacuity metrics for the new subsets.
- Banked seeds + antibodies as the other verticals do.

**Non-goals for Phase 1** (become V2–V6, each its own spec→plan): the unifier,
elaborator-soundness re-check, erasure extensions, totality-closure, and SMT
lint. Also out: generating *arbitrary* surface programs for `Types.Reduce`
(Phase 1 stays inside the bridge-translatable fragment where the differential is
meaningful — untranslatable asts hit `structural_congruence` and have no core
oracle, so they are a documented follow-on, not a Phase-1 infection source).

## 5. Invariants (shared with the kernel assays)

1. **Read-only TCB.** No `Cure.Core.*` edits; the kernel/`Conv`/`Normalise` are
   invoked as the oracle only.
2. **Known-label totality + negative controls.** Every assay is a decision
   procedure over a committed ground-truth label, with at least one negative
   control per vertical (an intentionally-broken input the assay must catch),
   proving the assay is load-bearing — the sensitivity discipline from Run C.
3. **Deterministic, banked, replayable.** Fixed fuel constants; seeds/antibodies
   committed; corpus round-trip via `to_pieces`/`from_pieces`.
4. **StreamData quarantine.** New generators/assays live under
   `lib/antigen/{generators,assays}/` and contain no `StreamData` literal
   (`architecture_test.exs`). The backend stays swappable.
5. **No new dependency, no `:meck`.**

## 6. Open questions (for operator review)

1. **Phase-1 vertical.** ✅ **RESOLVED — lead with V3 (elaborator-soundness
   re-check)** (operator, 2026-07-03). It is the single highest-value gap: the
   untrusted elaborator emits core the trusted kernel never independently
   re-checks today, and it is the cheapest vertical (a new assay over *existing*
   `elab_complete` generators, no new generator surface). V1 (normalizer)
   follows as Phase 2.
2. **`Types.Reduce` differential reach.** ✅ **RESOLVED — include the
   intrinsic-law-only assay over the *untranslatable* fragment** (operator,
   2026-07-03), in addition to the bridge-translatable differential. Idempotence
   / monotone-size hold there with no oracle, so the untranslatable fragment is
   not left uncovered. (Applies to V1, Phase 2.)
3. **SMT vertical inclusion.** ✅ **RESOLVED — keep V6, unconditional.** Z3 is a
   guaranteed part of the language toolchain (always present), so V6 is *not*
   gated on solver availability. Solver nondeterminism (timeouts) is absorbed by
   treating `:unknown` as legal and pinning a fixed solver config + committed
   timeout budget (see V6).
4. **Second unifier.** ✅ **RESOLVED — V2 covers BOTH `Elab.Unify` (core+metas)
   and `Types.Unify` (surface)** (operator, 2026-07-03). They are distinct
   engines but folded into one vertical: `Elab.Unify` first (it feeds
   elaboration), `Types.Unify` in the same phase, not deferred.

## 7. Roadmap (phased, each phase its own spec→plan→autopilot run)

| phase | vertical | new generator surface | oracle | cost |
|---|---|---|---|---|
| 1 | V3 elaborator soundness | none (reuse `elab_complete`) | `Kernel.check` | low |
| 2 | V1 normalizer (+ intrinsic-law assay over the untranslatable fragment) | Core-term (reuse) + translatable surface-ast | `Normalise`/`Conv`/`CoreBridge` | medium |
| 3 | V2 unifier (`Elab.Unify` + `Types.Unify`) | Core terms + metavars; surface types | `Conv` | medium |
| 4 | V5 totality closure | reuse `totality/*` | `Normalise` halting | low |
| 5 | V4 erasure/relevance | reuse typed-term + relevance | `Kernel.check`/`Relevance` | low |
| 6 | V6 SMT lint | refinement-predicate asts | kernel decidable overlap | high (Z3 always present; determinism-pinned) |
