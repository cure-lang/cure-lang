# Confluence of the Cure Core reduction relation

**Status: in progress (~85% mechanised).** This document records the state of
the mechanised confluence development so it can be resumed cleanly. The
development lives in `proof/` (Agda 2.8.0) alongside the soundness argument
(`docs/SOUNDNESS.md`).

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

### `Proof/Confluence.agda` (WIP, NOT in the tree)
The module is written and ~90% type-checks. It contains, all **proved**:

- `⇉-substS-refl` and its list helpers `⇉-substS-refl-terms` /
  `⇉-substBranchesS-refl` — the `⇉-refl` case of the substitution lemma, a
  **pure structural recursion on the term** (no redex can be created), which is
  what makes the termination of the main lemma structural.
- `⇉-extSub`, `⇉-extSub^`, `p-rename`, `p-rename-terms`, `p-rename-brs`,
  `p-rename-star`, `length-renameTerms` — `⇉` commutes with renaming, now a
  plain structural recursion (no value transport).
- `⇉-substS` proved for **all non-ι cases**: every congruence, the **β/ζ
  cases** (standard, value-free), and δ.
- `⇉-substS-star`, `⇉-substS-terms`, `⇉-substS-terms-refl`,
  `⇉-substBranchesS`, `⇉-substS-ctor-tail*`.

The latest snapshot is `/tmp/Confluence.routeA.wip2.agda` (session-local).

## What remains

1. **The ι cases of `⇉-substS`** (5 rules: `p-ι`, `p-ι-nat-zero`,
   `p-ι-nat-suc`, `p-ι-bounded-zero`, `p-ι-bounded-suc`). The proof shape is
   clear: reduce the scrutinee's args (`⇉*-ctor*`), the motive, and the
   branches; then apply the corresponding `p-ι*` rule with
   `findBranch-substBranchesS` (for `p-ι`) or `findBranch-rename`-style
   reasoning (for the literal peels), transporting the branch body's arity via
   `length-substTermsS` / `⇉-terms-length`, and closing with `subst-argsSub`.
   The remaining work is Agda implicit-argument plumbing, not mathematics.

2. **The four literal-peel cases of `p-rename`** (`p-ι-nat-zero`,
   `p-ι-nat-suc`, `p-ι-bounded-zero`, `p-ι-bounded-suc`). These currently
   leave unsolved `findBranch`-metas because the literal-peel rules' source
   branch list is unconstrained by the source term (a literal), so Agda cannot
   infer the reduct's branch list. The fix is to pass the implicit `brs`/`brs′`
   explicitly (and possibly bind the arity equation from `la` via a `where`).
   The `p-ι` (non-literal) case of `p-rename` is already proved.

3. **`⇉-diamond`** — the diamond property itself, from `⇉-substS`.

4. **`confluence : _⇝_`** from the diamond + the two inclusions, then
   discharging `never-reached→no-value` in `Proof/Soundness.agda`.

## Notes

- Two `{-# TERMINATING #-}` pragmas in `Core/Parallel.agda` cover the
  `⇉*-at-*` helpers (they recurse on the multi-step `ss`; the spine is
  re-indexed by `setAt`).
- The WIP `Confluence.agda` is kept out of the tree; snapshots are in
  `/tmp/Confluence.routeA.wip*.agda` (session-local). The earlier
  value-or-redex approach is in `/tmp/Confluence.wip11.agda` and is now
  **superseded** by the value-free formulation.
- **Do not re-introduce the `Value` side conditions.** They are not needed and
  they re-create the `substS-Value-or-redex` obligation.
