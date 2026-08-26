# Dependent-Kernel Cleanup — Execution Strategy

**Date:** 2026-07-07
**Branch:** `feature/idris-parity`
**Status:** approved strategy (design); implementation planned separately

## Purpose

This document fixes the *execution strategy* for the dependent-kernel cleanup —
the campaign that removes the nine divergences catalogued in
[`audit_categorised.md`](../audit_categorised.md) and its wave ordering
(Wave 0–5 + continuous hygiene). It does **not** re-specify the per-wave work;
that lives in the categorised audit. It records the cross-cutting decisions that
govern *how* we move through the waves, so that later plans and the individual
wave specs inherit a coherent frame instead of re-litigating it.

The end goal is unchanged: a small, trustworthy dependent-type kernel — enough
type theory to host the Safe FRP Types paper — with type-checking at compile
time and indices erased before BEAM/AtomVM. We chose to fix the Elixir kernel
rather than adopt lean4lean as the production checker; this strategy assumes that
decision.

## The seven decisions

### 1. Safety net: Antigen self-checks; the one legacy coupling is a K10 fixture fix

Antigen's oracles are overwhelmingly **known-label / generator-is-the-oracle**:
the generator constructs a term whose correct verdict is known by construction (a
canonical inhabitant that must typecheck, a deliberately ill-typed term that must
be rejected). Those labels stay valid as we change the kernel — a canonical
inhabitant should still typecheck after the primitives are gutted. Idris is a
*design-time* reference behind some fixtures, **not** a runtime dependency
("self-contained oracle, no Idris needed").

The **only** live coupling to the legacy dependent kernel is the
`normalizer/differential` assay (`lib/antigen/assays/normalizer.ex`), which uses
`Cure.Types.Reduce.normalize` + `Cure.Types.CoreBridge.to_core` against a
baked-in catalog of expected core values. Both are K10 legacy-collapse targets.

**Decision:** the safety net needs no special scaffolding. We keep Antigen honest
by **updating fixtures and labels per wave** as behavior changes (holes rejected,
primitive `{:eq}` gone, index-unifier fixed, data representation changed), and we
re-point/retire the single `normalizer/differential` assay when we reach K10.
The "measuring the ruler with itself" risk was overstated.

### 2. Green preservation: the compiler gate only — phase/ESP32 work is out of scope

The ESP32 / phase1–phase35 work is going to be overhauled after the compiler is
done. It does **not** have to stay green during the cleanup and is not a
constraint on any wave.

**Decision:** the only safety signal we keep meaningful is the compiler's own
gate — `mix test` + Antigen — updated per wave (per decision 1). The
dependent-type test corpus is *expected* to churn: it is the thing under
construction, it lives on `feature/idris-parity` not `main`, and letting it go
red mid-wave and re-greening it per wave is honest signal, not a broken product.
No mode-gating scaffolding is built to protect old behavior.

### 3. End state: one uniformly strict kernel — no permissive mode

The audit repeatedly qualifies removals with "in final mode" / "in sound modes."
That phrasing is inherited hedging from a codebase that was trying not to break
things. We do not carry it forward.

**Decision:** one kernel, one set of rules. The unsound machinery is **deleted,
not mode-gated**. There is no permissive tier inside the TCB where `Any`,
unproven SMT obligations, or holes sneak through. A looser/exploratory experience,
if ever wanted, lives *outside* the kernel (elaborator warnings, a lint pass),
never as a mode the trusted core must honor. This keeps the TCB small and makes
"sound" a property of the language, not of how the compiler was invoked.

#### `Any` under uniform strictness

Two different things travel under the name "Any"; only one dies.

- **Killed everywhere (this *is* uniform strictness):** `Any` as a **universal
  subtype** (`subtype?(:any, _)`, `Any` as both top and bottom, type holes / type
  vars behaving as universal subtypes), and **implicit / inferred** `Any` (parser
  turning unknown syntax into `{:type, :any}`, resolver fallback-to-`Any`,
  "unknown type silently becomes `Any`"). A type the programmer never wrote must
  never appear, and nothing is convertible-with-everything.
- **Survives (soundly):** `Any` as an **explicit, opaque dynamic type** — the
  Erlang `term()` role for genuine dynamic boundaries (`@extern`/FFI into AtomVM
  NIFs and OTP hand back untyped BEAM terms). You may *hold* one; you may not
  *use* it at a specific type by free unification. Its only sound elimination is a
  **checked coercion at a declared dynamic boundary** (a runtime tag check). It is
  a real type with one elimination rule, not a hole in conversion.

Net: `Any` remains usable in Cure programs only when explicitly written and only
eliminable by a checked cast; it is banned as an implicit fallback and as a
universal-subtype hole everywhere, kernel included. (Audit §18 #8; raw lines
219–226, 900, 998.)

### 4. Wave 0 is the whole grammar up front; validator clauses hard-enable per wave

The Final-Core validator enforces a *target grammar* whose final shape is exactly
what the later waves produce (typed primitive globals, qualified symbol IDs,
universe args, no holes, no `absurd`, data values with params/indices split). The
kernel will not *produce* that form until those waves land. Both priority notes
(§570 #1, §640 #1) put "define final Core syntax / validator everywhere" at step 1.

**Decision:** specify the **entire** Final-Core grammar in Wave 0 — on paper and
in code — including constructs we will not migrate for weeks. The validator is
written to check all of it, but each construct's check starts as a no-op/warn and
is **flipped to hard-reject as its wave lands**. The validator thereby becomes the
**executable checklist for the whole cleanup**: at any moment it names precisely
which constructs are still in legacy form, and "Wave N is done" means "the kernel
produces terms that pass the Wave-N validator clauses" (plus Antigen green +
fixtures updated per decisions 1–2).

The cost is real: Wave 0 is not just "write a validator," it is "design the
complete end-state Core term language." That design has to happen sometime, and
doing it first is what makes the rest sequenceable and kills the
"everything's half-migrated, nobody can define done" limbo.

### 5. Final Core is Idris/Agda-shaped, not Lean-shaped

Final Core carries **QTT-style multiplicities** on binders (`0 / 1 / ω`, per
Idris 2 / Atkey's Quantitative Type Theory). That single mechanism gives both
**erasure** (quantity 0 — usable in types, gone at runtime) and **linearity**
(quantity 1 — used exactly once), matching the existing `{0, ω}` relevance work
and the planned linear-types future. Lean's core has no multiplicity slot, no
linear types, and does erasure via `Prop`-irrelevance + whole-type compiler
erasure — a different, coarser mechanism with nowhere to put a quantity.

The directionality is the argument: projecting QTT → Lean is a **forgetful map**
(drop quantities, collapse `1` and `ω`, translate the pure skeleton) — lossy but
mechanical. Recovering linearity/erasure *from* a Lean term means inferring it —
generally undecidable. You build the rich core and whittle down; you cannot build
machine-checked linearity *inside* Lean's poorer core without forking Lean.

Consequent design commitments (keep the waves consistent with these):

- The **Wave-0 validator targets the rich core** (with multiplicities), not the
  Lean subset.
- Universes (Wave 4 / K7) are designed **Agda/Idris-predicative** — a predicative
  cumulative hierarchy with **irrelevance-via-quantity (0)** — not Lean's
  impredicative `Prop` + definitional proof-irrelevance. This projects into Lean
  cleanly (Lean's system is richer). Consistent with the inductive-`Eq` + K/UIP
  direction already chosen (task #90).

### 6. The Lean backend is a forgetful projection kept as a second checking backend

`Cure.Kernel.Backend` already forks *before* the TCB: `:elixir_core` (default)
vs `:lean`, selected by option/config/`CURE_KERNEL_BACKEND`. On the `:lean` path,
`check_ast_for_lean_backend` elaborates the admitted subset **without
`Cure.Core.Kernel` as the admission gate**, `Cure.Lean.ModuleEncoder` is the
trusted translator (Cure Core → Lean), and `Cure.Lean.Bridge.check_module` hands
off to lean4lean. lean4lean is therefore **not inside the Elixir kernel's TCB** —
it is the trust base of a *different* fork. That is the intended architecture and
we keep it.

**Decision:** supporting both backends long-term is a goal. `ModuleEncoder`
becomes a defined **lowering** — Final Core → erase multiplicities → Lean Core —
tracking Final Core as it is cleaned. The encoder rejects exactly the divergences
the cleanup removes (`{:eq}`/`{:refl}`, `{:prim}`, holes, `absurd`, bare atoms,
flat data values), so each wave that removes a divergence is also a node the
encoder no longer has to reject: the two forks **converge as a side effect of the
cleanup**, and lean4lean becomes an independent correctness witness.

Precise boundary — **lean4lean witnesses the dependent skeleton only, never the
quantitative layer.** Because multiplicities are erased before translation,
lean4lean validates "well-typed ignoring quantities." The linear/erasure
discipline is our kernel's sole, permanent responsibility (the `{0,1,ω}` check).
This is how QTT metatheory is structured (the underlying type theory is sound;
quantities are an additional layer). The "free correctness witness" only covers
the dependent core.

Current gaps (known, not blocking): there is **no de-translator** — the `:lean`
path returns the same Elixir `env` it encoded and codegen runs off that, so
lean4lean is a pure yes/no **gate** on a translation, not a round-trip feeding
codegen a Lean-verified artifact. This is acceptable while the encoded env is the
final elaborated term (it is). A de-translator is only needed if lean4lean is ever
asked to *elaborate* (fill implicits / produce the checked term) rather than
check. The encoder is also deliberately partial today for the same reason the
kernel is dirty; it completes as the cleanup lands.

### 7. Lean-compiler C-extraction is a future host target, distinct from ESP32

lean4lean is the **checker**, not the compiler — it can never emit C. Lean 4's
*compiler* is a separate, larger pipeline that lowers elaborated declarations to
C linking the Lean runtime (`libleanrt`: RC/boxed `lean_object*`).

**Decision (direction, not scheduled work):** the same faithful Cure Core → Lean
translation that enables decision 6 is also the on-ramp to **extracting the pure,
total, index-erasing fragment to native C via Lean's compiler** — classic
proof-assistant extraction (cf. Coq→OCaml, Agda→Haskell, Lean→C). This is a
**host/native** target, explicitly *not* a rehosting of ESP32 Cure:

- Lean's C links the Lean runtime (GC/RC/boxed) — a desktop story; putting that
  runtime on an ESP32 is its own project and cuts against why AtomVM was chosen.
  The embedded path stays BEAM/AtomVM.
- The hardware-useful parts — `@extern` into AtomVM NIFs (gpio/uart), the
  fsm/actor/sup concurrency family — have no natural Lean-compiler lowering; each
  primitive would need a Lean-side `@[extern]` C shim, and the concurrency model
  does not transfer. Only the pure fragment extracts cleanly.
- It needs the *compiler* bridge, not the current *checker* bridge — a meaningfully
  larger integration, deferred until the kernel is clean.

## What this strategy deliberately does not do

- No mode-gating / dual-kernel scaffolding to preserve old behavior (decision 3).
- No effort spent keeping ESP32/phase demos green (decision 2).
- No live lean4lean differential bolted onto Antigen — convergence is structural,
  via the shared grammar, not a runtime diff harness (decisions 1, 6).
- No Lean-compiler / C-extraction work now — direction recorded, deferred
  (decision 7).

## Relationship to the wave plan

The wave ordering and per-category scope are unchanged and remain in
[`audit_categorised.md`](../audit_categorised.md) (§ "Tackle order"). This strategy
adds the frame those waves execute inside:

- Wave 0 = design the full Idris/Agda-shaped Final-Core grammar (decision 5) +
  validator scaffold with per-wave-enabled clauses (decision 4).
- Waves 1–5 = each removal flips its validator clauses to hard-reject, updates
  Antigen fixtures/labels (decision 1), and shrinks the `ModuleEncoder` reject-set
  (decision 6); the dependent corpus re-greens per wave (decision 2).
- K7 (Wave 4) is designed Agda/Idris-predicative (decision 5).
- K10 (Wave 5) is where the `normalizer/differential` assay is re-pointed/retired
  (decision 1).
