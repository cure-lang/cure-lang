# Mechanised soundness proof for the Cure Core kernel

This directory holds **deliverable B**: a mechanised proof, in
[Agda](https://wiki.portal.chalmers.se/agda/), of the soundness of the Cure
Core kernel. It is the machine-checked counterpart of the written argument in
[`../docs/SOUNDNESS.md`](../docs/SOUNDNESS.md), whose §7 scopes exactly this
development.

> **Status: in progress.** The formalisation of the Core calculus and the
> typing judgment is complete and compiles clean. The Progress and Preservation
> statements are given, with the load-bearing lemmas isolated. The proofs of
> those lemmas are the current research frontier — see
> [Status](#status) below for a lemma-by-lemma breakdown.

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
| `Proof.CanonicalForms` | The `Value` predicate; canonical-form lemmas | ⚠️ statements done, value-level lemmas `postulate` |
| `Proof.Progress` | `Final` Core; the side conditions; `progress`, `preservation`, `soundness` | ⚠️ statements done, proofs `postulate` |

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

### In progress (statements given, proofs open)

These are the `postulate`s, each with a named proof strategy in the source:

1. **`canonical-pi-value`** (`Proof/CanonicalForms.agda`) — a closed value of
   Π type is a λ. *Strategy:* case analysis on the typing derivation; the only
   infer rule yielding `tm-pi` from a canonical value is `⇒-lam`; the
   elimination rules produce neutrals, impossible for a closed canonical value.
2. **`canonical-ctor`** (`Proof/CanonicalForms.agda`) — a closed value of data
   type is a ctor. *Strategy:* the only infer rule yielding `tm-data` from a
   value is `⇒-ctor`; `⇒-data` yields a sort, not a data value.
3. **`progress`** (`Proof/Progress.agda`) — by cases on the typing derivation,
   consuming the two canonical-form lemmas to show β and ι fire.
4. **`preservation`** (`Proof/Progress.agda`) — the four cases β, ζ, ι, δ.
   β/ζ are substitution lemmas; ι is the branch-coverage lemma; δ consumes
   `Certified`.
5. **`soundness`** (`Proof/Progress.agda`) — the induction combining Progress
   and Preservation.

### Open research questions (docs/SOUNDNESS.md §7, §8)

- **Substitution commutes with typing.** The β and ζ Preservation cases need
  a substitution lemma: if `Γ, x:A ⊢ b : B` and `Γ ⊢ a : A`, then
  `Γ ⊢ b[x := a] : B[x := a]`. This requires a weakening lemma and a proof
  that `substT` agrees with the typing judgment's context manipulation.
- **Conversion is sound.** `Core.Typing` takes `_≈_` as an abstract
  `Conversion` record. A complete development must define it (as the
  syntactic counterpart of the kernel's NbE `Conv`) and prove it is an
  equivalence stable under substitution and reduction. Per Lennon-Bertrand's
  *What does it take to certify a conversion checker?* (FSCD'25), conversion
  soundness needs only injectivity of type constructors — provable in a
  meta-theory weaker than the object theory.
- **The totality certificate.** `Certified` is a stated hypothesis. A
  separate, smaller proof that the *size-change certificate verifier* is
  sound (the "translation validation" discipline) is the recommended next
  step; see `docs/superpowers/specs/kernel/2026-08-14-agda-style-scc-totality-certificates.md`.
- **Erasure commutes with reduction.** `Erase.erase` is assumed to drop only
  `:erased`-graded binders; the argument here does not prove erasure commutes
  with reduction (docs/SOUNDNESS.md §8.3).
- **η and proof irrelevance.** If Cure's NbE has η-laws or definitional proof
  irrelevance, they are not covered and need an η-aware treatment.

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
     Proof/CanonicalForms.agda Proof/Progress.agda
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
