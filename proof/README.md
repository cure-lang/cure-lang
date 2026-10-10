# Mechanised soundness proof for the Cure Core kernel

This directory holds **deliverable B**: a mechanised proof, in
[Agda](https://wiki.portal.chalmers.se/agda/), of the soundness of the Cure
Core kernel. It is the machine-checked counterpart of the written argument in
[`../docs/SOUNDNESS.md`](../docs/SOUNDNESS.md), whose §7 scopes exactly this
development.

> **Status: in progress.** The formalisation of the Core calculus and the
> typing judgment is complete and compiles clean. The canonical-form lemmas
> are **proved**. The Progress/Preservation/Soundness theorems are stated,
> with their remaining obligations isolated as `postulate`s, each carrying a
> named proof strategy. See [Status](#status) for the lemma-by-lemma
> breakdown.

## What is being proved

The object language is the **Core** calculus of `Cure.Core.Term`
(`../lib/cure/core/term.ex`): a bidirectional, intensional Martin-Löf type
theory with

- a fixed predicative universe hierarchy `Type 0 : Type 1 : Type 2`;
- graded dependent functions `Π`/`λ`/application, with the four-element QTT
  carrier `{0, 1, ≤1, ω}`;
- graded `let`, ζ-transparent;
- indexed inductive families with a dependent eliminator (`case`);
- global references, with δ-reduction **gated** behind a totality certificate;
- primitive base types and their literals;
- inert effect terms (`Effect`, `pure`, `bind`) with zero reduction rules;
- two development-only leaves (`hole`, `absurd`).

The theorem (docs/SOUNDNESS.md §1.4):

> **Theorem (Soundness).** Let `e` be a closed, hole-free, final-Core term
> with `· ⊢ e : T` for a closed type `T`. Then evaluation of `e` either
> reaches a value `v` with `· ⊢ v : T`; or raises; or diverges. In particular,
> evaluation never reaches a **stuck** state.

It is proved from two lemmas:

- **Progress** (§2): a well-typed closed term is either a value or it steps.
- **Preservation** (§4): if `· ⊢ e : T` and `e ⇝ e′`, then `· ⊢ e′ : T`.

## The three side conditions

Progress and Preservation are *conditional*. The kernel is sound **provided**
three properties hold, each enforced in code and each carried as a hypothesis
here (docs/SOUNDNESS.md §3):

| Side condition | Agda name | Kernel enforcement |
|---|---|---|
| Strict positivity (§3.1) | `StrictlyPositive` | `Inductive.positive?/2` (nested) |
| Totality gates δ (§3.2) | `Certified` | `Env.certified?` + `Normalise.unfold_certified_head` |
| Coverage (§3.3) | `Covers` | `check_coverage` + `branch_unify` |

The hole/absurd discipline (§3.4) is expressed by restricting the theorem to
**final** Core — hole-free and absurd-free terms (`Final` in
`Proof/Progress.agda`), mirroring `Validator.release_config/0`.

The single largest assumption is `Certified`: the size-change certificate
*generator* (SCC discovery and transitive closure) lives outside the TCB in
`Cure.Elab.TotalityGraph`, so a mechanised proof takes "certified ⇒
terminating" as a stated hypothesis. This is the split docs/SOUNDNESS.md §7.2
recommends.

## Module map

| Module | Contents | Status |
|---|---|---|
| `Core.Grade` | The QTT carrier `{0,1,≤1,ω}`; additive/multiplicative monoids; subusaging preorder; all laws by exhaustive case analysis | ✅ complete |
| `Core.Universe` | The three-element universe hierarchy `l0 : l1 : l2`; cumulativity `_≤ˡ_`; max `_⊔ˡ_`; `succLevel` | ✅ complete |
| `Core.Syntax` | `Term` (faithful to `Cure.Core.Term`); de Bruijn `shift`/`substT`; `Scoped`/`Closed` | ✅ complete |
| `Core.Value` | The NbE value domain: closures, neutrals, size-indexed so closures are structurally smaller | ✅ complete |
| `Core.Reduction` | The reduction relation `_⇝_` (β, ζ, ι, δ, congruence) and its reflexive-transitive closure | ✅ complete |
| `Core.Signature` | Inductive families, constructors, telescopes; nested strict positivity | ✅ complete |
| `Core.Typing` | The bidirectional `infer`/`check` judgment `_⊢_⇒_` / `_⊢_⇐_` | ✅ complete |
| `Proof.Values` | The `Canonical`/`Neutral`/`Value` split (a value includes neutrals) | ✅ complete |
| `Proof.Inversion` | Head-inversion lemmas; conversion injectivity | ⚠️ `invert-pi`/`invert-data` open; `invert-*-check` **proved** |
| `Proof.CanonicalForms` | `canonical-pi-value`, `canonical-ctor` | ✅ **proved** (= `invert-*-check`) |
| `Proof.Substitution` | shift/subst algebraic laws | ⚠️ `shift-0` **proved**; interaction laws open |
| `Proof.Progress` | `Final` Core; the three side conditions; `progress` | ⚠️ statement done, proof open |
| `Proof.Preservation` | `weaken`, `subst⇒`, `subst⇐`, `preservation` | ⚠️ statements done, proofs open |
| `Proof.Soundness` | `EvalResult`; `soundness` | ⚠️ statement done, proof open |

## Status

### Complete (machine-checked, no holes)

- The QTT grade carrier and all its algebraic laws.
- The universe hierarchy, cumulativity, and the max operation.
- The Core syntax: the full node taxonomy of `Cure.Core.Term`, with
  de Bruijn shift and substitution that mirror `Term.shift/3` and
  `Term.subst/3` exactly, and a well-scopedness predicate.
- The NbE value domain, size-indexed so that closure environments are
  structurally smaller (no postulates, no `{-# TERMINATING #-}`).
- The reduction relation `_⇝_`, with all four reduction rules and the
  congruence rules, matching docs/SOUNDNESS.md §1.3.
- The inductive-family signature with the nested strict-positivity checker.
- The bidirectional typing judgment, with every rule from
  `Cure.Core.Kernel`'s `infer`/`check`.
- **The canonical-form lemmas** `canonical-pi-value` and `canonical-ctor`
  (`Proof/CanonicalForms.agda`), proved by composing the checking-mode
  head-inversion lemmas.
- **The `shift-0` identity law** (`Proof/Substitution.agda`): shifting by
  zero is the identity at any cutoff.
- **The weakening lookup law** `wk-lookup` (`Proof/Preservation.agda`):
  under the `lift` renaming (which fixes index 0), a context lookup
  transforms correctly. Weakening `weaken⇒` is derived from it via the
  fundamental renaming lemma.

### In progress (statements given, proofs open)

These are the `postulate`s, each with a named proof strategy in the source:

1. **`invert-pi` / `invert-data`** (`Proof/Inversion.agda`) — inference-mode
   head inversion: a canonical value that infers a Π type is a λ; a canonical
   value that infers a data type is a ctor. *Strategy:* induction on the
   inference derivation; each canonical head has exactly one applicable
   infer rule.
2. **`conv-injective-data` / `conv-injective-pi`** (`Proof/Inversion.agda`) —
   conversion injectivity on type constructors. *Strategy:* the FSCD'25
   result; provable in a meta-theory weaker than the object theory.
3. **`lk-ext` / `lk-extⁿ`** (`Proof/Preservation.agda`) — the lookup lemma
   extends under a binder. *Strategy:* see "The context representation"
   below; this is the one place where the flat context representation
   bites, and the length-indexed context removes the obligation entirely.
4. **`ren⇒` / `ren⇐`** (`Proof/Preservation.agda`) — the fundamental
   renaming lemma (typing is stable under a context morphism). Once
   `lk-ext` is in hand the induction is mechanical; `weaken⇒` is its
   instance at `lift`.
5. **`subst⇒` / `subst⇐`** (`Proof/Preservation.agda`) — the substitution
   lemma. *Strategy:* induction on the derivation; `⇒-var` splits on
   whether the looked-up index is the substituted one.
6. **`progress`** (`Proof/Progress.agda`) — by cases on the typing
   derivation, consuming the canonical-form lemmas to show β and ι fire.
7. **`preservation`** (`Proof/Preservation.agda`) — the four cases β, ζ, ι,
   δ. β/ζ consume `subst⇐`; ι is the branch-coverage lemma; δ consumes
   `Certified`.
8. **`soundness`** (`Proof/Soundness.agda`) — the type-safety induction
   combining Progress and Preservation.

### Open research questions (docs/SOUNDNESS.md §7, §8)

- **The totality certificate.** `Certified` is a stated hypothesis. A
  separate, smaller proof that the *size-change certificate verifier* is
  sound (the "translation validation" discipline) is the recommended next
  step; see `docs/superpowers/specs/kernel/2026-08-14-agda-style-scc-totality-certificates.md`.
- **Erasure commutes with reduction.** `Erase.erase` is assumed to drop only
  `:erased`-graded binders; the argument here does not prove erasure commutes
  with reduction (docs/SOUNDNESS.md §8.3).
- **η and proof irrelevance.** If Cure's NbE has η-laws or definitional proof
  irrelevance, they are not covered and need an η-aware treatment.
- **The NbE evaluator.** This development formalises the reduction *relation*
  (the specification). A separate obligation is that the kernel's `Eval`
  function implements exactly that relation — the operational refinement
  the written argument assumes.

## The context representation (a finding from this slice)

The single hardest piece of de Bruijn bookkeeping in this development is
**weakening and substitution** — the lemmas that make the β and ζ cases of
Preservation go through. This slice established exactly why, and what the
fix is.

`Core.Typing` currently represents a context as a flat `List Term` with an
*inductive* lookup relation `_∋_at_`. With that representation, the
fundamental renaming lemma (`ren⇒`) cannot be proved: its binder case
requires the target context under `ext ρ` to be built by recursion on the
source (the head type is `rename ρ` of the source head, not
`rename (ext ρ)`), which a flat `renameCtx ρ Γ` cannot express. The
`lk-ext` obligation in `Proof/Preservation.agda` is precisely this gap.

The fix — confirmed by working prototypes during this slice — is a
**length-indexed context** with lookup as a total function on `Fin`:

```agda
data Context : Set where
  ⟨⟩  : Context
  _▷_ : Context → Term → Context

lookup : (Γ : Context) → Fin (lengthCtx Γ) → Term
```

With this representation:

- the weakening lookup law `lookup (extend Γ T) (suc i) ≡ lookup Γ i` is
  `refl`;
- the lookup lemma under a context morphism is a `refl`-based induction;
- the binder-order issue disappears because the morphism's target is built
  structurally.

The refactor touches `Core.Typing` and the seven modules that consume the
context; it is the recommended next step and unblocks the whole
weakening/substitution chain.

## Building

Requires Agda 2.8.0 and the Agda standard library.

```bash
# One-time: register the standard library.
mkdir -p ~/.config/agda
echo "/usr/share/agda-stdlib/standard-library.agda-lib" >> ~/.config/agda/libraries

# Type-check the whole development.
cd proof
agda Core/Grade.agda Core/Universe.agda Core/Syntax.agda Core/Value.agda \
     Core/Reduction.agda Core/Signature.agda Core/Typing.agda \
     Proof/Values.agda Proof/Inversion.agda Proof/CanonicalForms.agda \
     Proof/Substitution.agda Proof/Progress.agda Proof/Preservation.agda \
     Proof/Soundness.agda
```

The library descriptor is `cure-core.agda-lib`. Interface files (`_build/`)
are git-ignored.

## Relationship to the executable evidence

The written argument (docs/SOUNDNESS.md §9) maps each lemma to an executable
Antigen assay. This development is the *mechanised* counterpart: where Antigen
turns each lemma into a runnable, falsifiable claim, this development turns the
same lemmas into machine-checked theorems (or, for the open obligations, into
precisely stated goals). The two are complementary — Antigen can find
counterexamples but cannot establish the theorem; a mechanised proof can
establish the theorem but only for the calculus it formalises.

The `postulate`s here correspond exactly to the Antigen assays: `progress` ↔
`MetaCheck.progresses?/2`, `preservation` ↔ `MetaCheck.type_preserved?/2`,
`canonical-ctor` ↔ the `ι`-coverage assays, and `Certified` ↔ the
`Antigen.Assays.Totality` family.
