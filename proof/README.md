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
| `Core.Typing` | The bidirectional `infer`/`check` judgment `_⊢_⇒_` / `_⊢_⇐_`, over a length-indexed context with `Fin` lookup | ✅ complete |
| `Proof.Values` | The `Canonical`/`Neutral`/`Value` split (a value includes neutrals) | ✅ complete |
| `Proof.Inversion` | Head-inversion lemmas; conversion injectivity | ⚠️ `invert-pi`/`invert-data` open; `invert-*-check` **proved** |
| `Proof.CanonicalForms` | `canonical-pi-value`, `canonical-ctor` | ✅ **proved** (= `invert-*-check`) |
| `Proof.Substitution` | shift/subst algebraic laws | ⚠️ `shift-0` and `shift-var-1` **proved**; interaction laws open |
| `Proof.Context` | Length-indexed context laws: weakening lookup, `toℕ-wkFin` | ✅ **proved** |
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
- **The weakening lookup law** (`Proof/Context.agda`): with the
  length-indexed context, `lookup (extend Γ T) (suc i) ≡ lookup Γ i` is
  `refl`, and `toℕ-wkFin` gives the index arithmetic.

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
3. **`weaken⇒` / `weaken⇐`** (`Proof/Preservation.agda`) — weakening. The
   `⇒-var` case is the definitional lookup law; the binder case needs a
   context *morphism* (see "The context representation" below).
4. **`subst⇒` / `subst⇐`** (`Proof/Preservation.agda`) — the substitution
   lemma, conditioned on `WfCtx` (the well-formed-context invariant). The
   `⇒-var` cases split on whether the looked-up index is the substituted
   one; see "The substitution lemma" below for the remaining subtlety.
5. **`progress`** (`Proof/Progress.agda`) — by cases on the typing
   derivation, consuming the canonical-form lemmas to show β and ι fire.
6. **`preservation`** (`Proof/Preservation.agda`) — the four cases β, ζ, ι,
   δ. β/ζ consume `subst⇐`; ι is the branch-coverage lemma; δ consumes
   `Certified`.
7. **`soundness`** (`Proof/Soundness.agda`) — the type-safety induction
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

## The context representation

The hardest piece of de Bruijn bookkeeping is **weakening and
substitution** — the lemmas that make the β and ζ cases of Preservation go
through. This slice settled the representation question.

`Core.Typing` uses a **length-indexed context** with lookup as a total
function on `Fin`:

```agda
data Context : Set where
  ⟨⟩  : Context
  _▷_ : Context → Term → Context

lookup : (Γ : Context) → Fin (lengthCtx Γ) → Term
```

This makes the de Bruijn bookkeeping `refl`-level:

- the weakening lookup law `lookup (extend Γ T) (suc i) ≡ lookup Γ i` is
  `refl` (`Proof/Context.agda`);
- the type at index `i` is UNCHANGED by extension (well-scoped convention).

A flat `List Term` with an inductive lookup relation was tried first and
rejected: its binder case for the fundamental renaming lemma cannot be
expressed, because the target context must be built by recursion on the
source.

**Remaining obligation.** Weakening's binder case still hits a binder-order
issue: prepending the fresh binder `S` does not commute with prepending the
Π/λ binder `d`. The standard fix is to state weakening via a context
*morphism* (a `Fin`-preserving map), whose extension under a binder handles
the order automatically. The lookup law it rests on (`lookup-extend`) is
proved; the morphism plumbing is the next step.

## The substitution lemma

Substitution is the algebraic heart of the β and ζ cases of Preservation.
The development states it conditioned on `WfCtx` — the well-formed-context
invariant that the type at index `k` is scoped in the prefix below it.

The `⇒-var` cases are where the subtlety lives:

- **`k = j`** (the substituted variable): the term becomes `a`, and the
  type `lookup Γ j` is `j`-scoped by `WfCtx`, so `substT j a (lookup Γ j)`
  is `lookup Γ j` by `subst-id`. The goal is `Γ ⊢ a ⇐ A`, which is the
  hypothesis.
- **`k ≠ j`**: the term is unchanged. If `k < j`, the type `lookup Γ k` is
  `k`-scoped hence `j`-free, so it is unchanged by `subst-id`. **If
  `k > j`, the type may mention `j`**, so `substT j a (lookup Γ k)` differs
  from `lookup Γ k`, and the context itself must be adjusted by the
  substitution.

That last point is the remaining obligation: the substitution lemma needs
a **context-substitution** operation (`Γ` with index `j` removed and the
types above it adjusted), so that the statement reads

    Γ[j := a] ⊢ substT j a t ⇒ substT j a T

The syntactic pieces are all in place (`subst-id`, `subst-var-eq/neq`,
`rename-id`); what remains is the context surgery and threading it through
the induction.

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
