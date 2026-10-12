# Confluence of the Cure Core reduction relation

**Status: in progress (~90% mechanised).** This document records the state of
the mechanised confluence development so it can be resumed cleanly. The
development lives in `proof/` (Agda 2.8.0) alongside the soundness argument
(`docs/SOUNDNESS.md`). The substitution-commutation lemma `⇉-substS` — the
crux — is **fully proved** (`proof/Proof/Confluence.agda`, in the build);
the remaining work is the diamond property `⇉-diamond` and the final
`confluence` assembly.

## Why confluence

The classical three-way soundness theorem (`docs/SOUNDNESS.md` §1.4,
`proof/Proof/Soundness.agda`) is derived from two named classical inputs. The
second, `never-reached→no-value`, needs **confluence** of the reduction
relation `_⇝_`: a never-reaching evaluation tree has no reachable value. The
relation is **not deterministic** (`(λx. b) a` both β-reduces and reduces under
the λ), so confluence is not immediate.

## The method

The Tait–Martin-Löf method, via the **parallel reduction** `_⇉_`
(`proof/Core/Parallel.agda`):

1. `⇉-diamond` — `⇉` has the diamond property;
2. `⇝ ⊆ ⇉` (`⇝→⇉`) and `⇉ ⊆ ⇝*` (`⇉→⇝*`) turn the diamond into confluence of
   `_⇝_`.

The crux is the **substitution commutation lemma** `⇉-substS`: parallel
reduction is closed under substitution. It is stated **multi-step** (`_⇉*_`)
because substituting into a neutral value can produce a redex.

## KEY FINDING (this slice): the `Value` side conditions are vestigial

Earlier formulations carried a `Value` side condition on β/ζ in **both**
`_⇝_` (`Core/Reduction.agda`) and `_⇉_` (`Core/Parallel.agda`), mirroring the
kernel's `Eval.apply(vlam, varg)`. This was believed to be load-bearing for
Preservation's β/ζ cases (via `value-infer`), and it was the *sole* source of
the hard `substS-Value-or-redex` case analysis in the substitution lemma —
because `⇉-substS` then had to show `Value (substS σ a)`, which substitution
does not preserve.

**The side conditions are not needed.** Inspection of the actual proofs shows:

- `preserve-β` (`Proof/Preservation.agda`) never uses `Value a` — it applies
  `substTop⇐` to the argument's *checking* derivation `da : Γ ⊢ a ⇐ d`
  directly.
- `preserve-ζ` used `Value v` only to call `value-infer`, but the general
  `check-infer` (a hole-free term that checks infers its type) subsumes it, and
  hole-freeness is supplied by the `Final t` hypothesis the preservation
  induction already threads.

So the `Value` premises were **removed** from `_⇝_`'s `β`/`ζ` and `_⇉_`'s
`p-β`/`p-ζ`. Consequences:

- `_⇉_` is now **value-free**, so `⇉-substS` is the **standard textbook proof**:
  no `substS-Value-or-redex`, no neutral/canonical case analysis, and `p-rename`
  needs no `Canonical`/`Neutral`/`Value` transport (it is a plain structural
  recursion).
- The whole existing development (`Core/*`, `Proof/*` including Progress,
  Preservation, FinalPreservation, Soundness) type-checks **green** with the
  value-free rules — verified by `proof/check.sh` (all 17 modules OK).

This is the single most important simplification of the confluence work: it
removes the entire hard case.

## What is done (all green, no new postulates)

### `Core/Reduction.agda`
- `_⇝_`'s `β`/`ζ` are **value-free** (`β : tm-app (tm-lam g d b) a ⇝ substTopT a b`,
  `ζ : tm-let g ty v b ⇝ substTopT v b`).
- `_⇝_`'s spine congruences are **element-indexed** (`ξ-ctor-at`,
  `ξ-data-params-at`, `ξ-data-indices-at`), using `len`/`lookupAt`/`setAt`
  (`Core/Syntax.agda`).
- `ξ-case-brs` (case reduces its branch bodies) with `_⇝*ᵇ_`.
- `findBranch-substBranchesS`, `findBranch-rename`.

### `Core/Parallel.agda`
- `_⇉_` (β/ζ/ι/δ + all congruences) is **value-free**; `_⇉*_`, `_⇉*ᵗ_`,
  `_⇉*ᵇ_`, `_⇉*ᵗ*_`.
- `⇝→⇉`, `⇉→⇝*` (both inclusions) — now simpler, with no value premises.
- Multi-step congruence lifters `⇉*-*`.
- Position-indexed spine lifters `p-ctor-at`/`⇉*-at-ctor`,
  `p-data-*-at`/`⇉*-at-data-*`, and the prefix-accumulator lifters
  `⇉*-ctor*`/`⇉*-data-*-*`.
- `findBranch-⇉*ᵇ`.

### `Proof/Substitution.agda`
- `subst-argsSub`, `rename-substArgs`, and the rename/subst interaction laws.

### `Proof/Preservation.agda`, `Proof/Progress.agda`,
### `Proof/FinalPreservation.agda`
- Updated to the value-free rules: `preserve-ζ` now takes only `HoleFree v`
  (not `Value v`) and uses `check-infer`; the `β`/`ζ` call sites in `progress`
  and `final-preservation` drop the value witness.

### `Proof/Confluence.agda` (IN the tree and the build)

The module type-checks clean (no holes, no new postulates) and contains, all
**proved**:

- `⇉-substS-refl` and its list helpers `⇉-substS-refl-terms` /
  `⇉-substBranchesS-refl` — the `⇉-refl` case of the substitution lemma, a
  **pure structural recursion on the term** (no redex can be created), which is
  what makes the termination of the main lemma structural.
- `⇉-extSub`, `⇉-extSub^`, `p-rename`, `p-rename-terms`, `p-rename-brs`,
  `p-rename-star`, `length-renameTerms` — `⇉` commutes with renaming, a plain
  structural recursion (no value transport).
- **`⇉-substS` — the substitution-commutation lemma, ALL cases proved**: every
  congruence, the **β/ζ cases** (standard, value-free), **all five ι cases**
  (`p-ι`, `p-ι-nat-zero`, `p-ι-nat-suc`, `p-ι-bounded-zero`,
  `p-ι-bounded-suc`), and δ.
- `⇉-substS-star`, `⇉-substS-terms`, `⇉-substS-terms-refl`,
  `⇉-substBranchesS`, `⇉-substS-ctor-tail*`, `length-substTermsS`.
- **`substTopT-⇉*`** (with `topSub-⇉`) — `substTopT` commutes with a
  MULTI-step parallel reduction: `a ⇉* a′ → b ⇉* b′ → substTopT a b ⇉*
  substTopT a′ b′`. This is the lemma the diamond's β/ζ redex cases need
  (the argument's reduct is reached in several steps, which the single-step
  hypothesis of `⇉-substS-star` cannot consume).

This is the crux the plan identified. **It is done.**

## What remains

1. **`⇉-diamond`** — the diamond property itself, from `⇉-substS`. This is the
   next concrete step. It is a large Tait–Martin-Löf double induction on the
   two derivations `t ⇉ u` and `t ⇉ v`. The case analysis splits into:

   - **same-constructor** cases (atomic forms, `p-pi`, `p-lam`, `p-let`,
     `p-app`, `p-data`, `p-ctor`, `p-case`, the effect formers): structural,
     using the IH on the premises. NOTE `p-lam`/`p-let`'s body premise is a
     SINGLE step (`_⇉_`), so the IH is `⇉-diamond`, not `⇉-diamond-star`.
   - **`p-ctor-head`/`p-ctor-tail`** mixed cases: the common reduct is
     `tm-ctor n (x′ ∷ xs′)`; both sides are re-derived by `p-ctor-tail` /
     `p-ctor-head`. The `p-ctor-tail`/`p-ctor-tail` case needs a
     **ctor-spine diamond** (`⇉-diamond-ctor`) that returns a `tm-ctor` witness
     (the plain `⇉-diamond` returns a `Term`, which Agda cannot see is a
     `tm-ctor`).
   - **`p-δ`/`p-δ`**: the two bodies are equal by `just-inj` of the two
     `Signature.body` equations; transport `⇉-refl`.
   - **β/ζ/ι vs β/ζ/ι** (the redex cases): both sides reduce to
     `substTopT`-forms; the diamond is closed by `⇉-substS` (this is where the
     substitution lemma is consumed).
   - **β/ζ/ι vs their congruence** (`p-β` vs `p-app`, `p-ζ` vs `p-let`,
     `p-ι*` vs `p-case`): the redex side steps by the rule, the congruence
     side steps by the rule applied to the reduced components; the two are
     reconciled by `⇉-substS` / `⇉-substS-star`.
   - **the list/multi-step diamonds** `⇉-diamond-star` (for `_⇉*_`),
     `⇉-diamond-terms` (for `_⇉*ᵗ_`), `⇉-diamond-brs` (for `_⇉*ᵇ_`), and the
     ctor-spine diamond `⇉-diamond-ctor`.

   A partial development exists in `/tmp/Confluence.diamond.wip.agda`
   (session-local): the same-constructor, `p-ctor-*`, and `p-δ` cases are
   proved; the redex cross-cases and the list diamonds are the remaining work.

   **DESIGN NOTE (the one real subtlety).** The diamond must be stated with
   MULTI-step conclusions (`∃ λ w → u ⇉* w × v ⇉* w`), because the redex cases
   are closed by the multi-step substitution lemma. `⇉-substS`'s hypothesis
   is SINGLE-step, while the diamond supplies a MULTI-step reduct for the
   argument. This gap is now BRIDGED by `substTopT-⇉*` (proved in
   `Proof/Confluence.agda`), so the β/ζ redex cases are a direct application:

       ⇉-diamond (p-β sd sb sa) (p-β sd′ sb′ sa′) =
         let (a‴ , ad , ae) = ⇉-diamond sa sa′
             (b‴ , bd , be) = ⇉-diamond-star sb sb′
         in substTopT a‴ b‴ , substTopT-⇉* ad bd , substTopT-⇉* ae be

   The remaining cases are the redex-vs-CONGRUENCE cases (β vs `p-app`, ζ vs
   `p-let`, ι vs `p-case`), the ι redex cases, and the list diamonds
   `⇉-diamond-star`/`⇉-diamond-terms`/`⇉-diamond-brs` plus the ctor-spine
   diamond `⇉-diamond-ctor`. Note `⇉-diamond-ctor`'s witness must be a
   `tm-ctor` (not a bare `Term`), which needs small `_⇉*ᵗ*_ → _⇉_` /
   `_⇉*_ → _⇉_` "head" projections for the `p-ctor`/`p-ctor-head` cases.

2. **`confluence : _⇝_`** from the diamond + the two inclusions, then
   discharging `never-reached→no-value` in `Proof/Soundness.agda`.

## Notes

- Two `{-# TERMINATING #-}` pragmas in `Core/Parallel.agda` cover the
  `⇉*-at-*` helpers (they recurse on the multi-step `ss`; the spine is
  re-indexed by `setAt`).
- The WIP `Confluence.agda` is now **in the tree and the build**
  (`proof/check.sh`); it type-checks clean with no holes and no new postulates.
  Snapshots of the intermediate states are in `/tmp/Confluence.routeA.wip*.agda`
  (session-local). The earlier value-or-redex approach is in
  `/tmp/Confluence.wip11.agda` and is now **superseded** by the value-free
  formulation.
- **Do not re-introduce the `Value` side conditions.** They are not needed and
  they re-create the `substS-Value-or-redex` obligation.
