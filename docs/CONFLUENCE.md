# Confluence of the Cure Core reduction relation

**Status: in progress (~75% mechanised).** This document records the state of
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

## What is done (all green, no new postulates)

### `Core/Reduction.agda`
- `_⇝_`'s spine congruences are **element-indexed** (`ξ-ctor-at`,
  `ξ-data-params-at`, `ξ-data-indices-at`), using `len`/`lookupAt`/`setAt`
  (`Core/Syntax.agda`) — a definitionally-reducing length, since the stdlib's
  `length` is `foldr (const suc) 0` and cannot index a `Fin`.
- `ξ-case-brs` (case reduces its branch bodies) with `_⇝*ᵇ_`.
- `findBranch-substBranchesS`, `findBranch-rename`.

### `Core/Parallel.agda`
- `_⇉_` (β/ζ/ι/δ + all congruences, with `Value` side conditions on β/ζ and
  `findBranch` on the reduced branch list for ι), `_⇉*_`, `_⇉*ᵗ_`, `_⇉*ᵇ_`,
  `_⇉*ᵗ*_`.
- `⇝→⇉`, `⇉→⇝*` (both inclusions).
- Multi-step congruence lifters `⇉*-*`.
- Position-indexed spine lifters `p-ctor-at`/`⇉*-at-ctor`,
  `p-data-*-at`/`⇉*-at-data-*`, and the prefix-accumulator lifters
  `⇉*-ctor*`/`⇉*-data-*-*`.
- `findBranch-⇉*ᵇ`.

### `Proof/Substitution.agda`
- `subst-argsSub` — `substS σ (substArgs args b) ≡ substArgs (substTermsS σ args) (substS (extSub^ (length args) σ) b)`.
- `rename-substArgs` — the `rename` analogue.

### `Proof/Confluence.agda` (WIP, not in the tree)
- `⇉-substS` proved for **all congruence cases** (app, lam, pi, let, effect,
  ctor, data, case) and the **β/ζ cases**.
- Supporting: `⇉-extSub`, `⇉-extSub^`, `p-rename-wk`, `p-rename`,
  `⇉-substS-terms`, `⇉-substBranchesS`, `substS-Canonical`, `⇉-Canonical`.

## What remains

1. **`substS-Value-or-redex`** (the classic hard case). `⇉`'s `p-β`/`p-ζ`
   require `Value a`; `⇉-substS` must show `Value (substS σ a)`. This holds for
   canonical `a` (`substS-Canonical`), but for neutral `a`, `substS σ a` may be
   a value or a redex. The redex case must be stepped. The mutual recursion
   between the function's and argument's valuehood is the crux. A clean
   formulation is a three-way `SubstShape` (neutral / canonical / redex) for
   `substS σ t` on neutral `t`; the non-lambda canonical cases (`c-pi`,
   `c-data`, …) are impossible for well-typed applications but occur
   syntactically, so the lemma may need a well-typedness restriction.

2. **The ι cases** of `⇉-substS` (using `subst-argsSub`, `findBranch-*`).

3. **`⇉-diamond`** — the diamond property itself.

4. **`confluence : _⇝_`** from the diamond + the two inclusions, then
   discharging `never-reached→no-value` in `Proof/Soundness.agda`.

## Notes

- Two `{-# TERMINATING #-}` pragmas in `Core/Parallel.agda` cover the
  `⇉*-at-*` helpers (they recurse on the multi-step `ss`; the spine is
  re-indexed by `setAt`).
- The WIP `Confluence.agda` is kept out of the tree; the latest snapshot is in
  `/tmp/Confluence.wip11.agda` (session-local).
