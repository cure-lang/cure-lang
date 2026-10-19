# Confluence of the Cure Core reduction relation

**Status: COMPLETE.** The mechanised confluence development is finished:
`⇉-substS` (the substitution-commutation lemma), `⇉-diamond` (the diamond
property), and `confluence : _⇝_` are all **proved** in
`proof/Proof/Confluence.agda`, which type-checks clean (no holes, no new
postulates) and is in the build (`proof/check.sh`). The development lives in
`proof/` (Agda 2.8.0) alongside the soundness argument (`docs/SOUNDNESS.md`).

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

### `⇉-diamond` and `confluence` (also in `Proof/Confluence.agda`)

- **`⇉-diamond`** — the diamond property of `_⇉_`, with MULTI-step
  conclusions (`t ⇉ u → t ⇉ v → ∃ w → u ⇉* w × v ⇉* w`). All cases proved:
  the same-constructor cases; the `p-ctor`/`p-ctor-head`/`p-ctor-tail`
  cross cases (via the ctor-spine diamond `⇉-diamond-ctor`, whose witness is
  a `tm-ctor`); `p-δ`/`p-δ` (bodies equal by `just-inj`); the β/ζ redex cases
  (via **`substTopT-⇉*`**); the ι redex cases (via **`substArgs-⇉*ᵗ*`**); and
  the redex-vs-congruence cases (β vs `p-app`, ζ vs `p-let`, ι vs `p-case`,
  and the literal peels vs `p-case`).
- Supporting: `⇉-diamond-star` (multi-step), `⇉-diamond-terms`,
  `⇉-diamond-brs`, `⇉-diamond-ctor`, `ctor-of-step`, `ctor-spine`,
  `⇉-ctor-spine`, `ctor-inj`, `ctor-spine-rewrite`, `⇉-ctor-terms`,
  `⇉*-ctor-tail`, `findBranch-⇉*ᵇ-eq`, `findBranch-⇉*ᵇ-rev`,
  `findBranch-unique`, `substTopT-⇉*`, `substArgs-⇉*`, `substArgs-⇉*ᵗ*`,
  `argsSub-⇉`, `argsSub-go-⇉*`, `⇉-substS-refl*`, `⇉-substS-star*`.
- **`confluence : _⇝_`** — `_⇝_` is confluent, from `⇉-confluent` (= the
  diamond, iterated) and the two inclusions `⇝→⇉*` / `⇉→⇝*-star`.

**The confluence development is complete.**

## FINDING: `never-reached→no-value` is false as stated

With `confluence` proved, the natural next step is to discharge the classical
input `never-reached→no-value` in `Proof/Soundness.agda`. **It cannot be
discharged, because it is false** for the mechanised `_⇝_`:

- `_⇝_` reduces UNDER BINDERS (`ξ-lam-body`, `ξ-pi-cod`, `ξ-let-body`).
- Let `Ω = (λx. x x) (λx. x x)`. Then `Ω ⇝ Ω` (β, since
  `substTopT Ω (x x) = Ω`), so `Ω` diverges.
- `tm-lam g d Ω` is CANONICAL (`c-lam`), hence a `Value`, and it steps to
  itself via `ξ-lam-body (Ω ⇝ Ω)`. So `NeverReached (tm-lam g d Ω) T` holds.
- But `tm-lam g d Ω ⇝* tm-lam g d Ω` (refl) with `Value (tm-lam g d Ω)`.

So `never-reached→no-value` would give `⊥` from a consistent hypothesis. The
root cause is that `Value` (canonical/neutral) does NOT mean "cannot step":
a canonical λ with a diverging body is a `Value` that steps forever. The
statement is only true if "value" means a term that has FINISHED evaluating
(a stuck-free normal form), which is a strictly stronger predicate than
`Value`.

This is a comment on the SOUNDNESS development's classical input, not on
confluence: `confluence` is correct and complete as proved. Discharging
`never-reached→no-value` would require either (a) a reduction relation that
does not reduce under binders, or (b) a stronger "final value" predicate in
the statement.

## What remains

**Nothing in the confluence development itself.** `confluence : _⇝_` is
proved. The classical input `never-reached→no-value` in
`Proof/Soundness.agda` **cannot** be discharged using `confluence`, because
it is FALSE as stated for the mechanised `_⇝_` (see the finding above).

**RESOLVED (repair, not discharge).** `proof/Proof/SoundnessConfluence.agda`
replaces the false input by its true form, over NORMAL FORMS rather than
`Value`, and is proved with **zero new postulates**:

- `NormalForm t` — `t` admits no reduction step (strictly stronger than
  `Value`: every λ is a `Value`, but only a λ with a normal body is a
  `NormalForm`);
- `never-reached-not-nf` — a never-reaching tree is not a normal form. This
  is the honest form of the input: the original said "no VALUE is
  reachable" (false); "no NORMAL FORM is reachable" follows immediately
  from `NeverReached`'s step at every node;
- `DivergesNF` / `never-reached→divergesNF` — positive divergence over
  normal forms, by guarded corecursion;
- `soundness-nf` — the dichotomy `Reached ⊎ DivergesNF`, leaving
  `tree-decides` (LPO) as the ONLY classical input.

**The false postulate has been DELETED** from `Proof/Soundness.agda`,
together with the classical three-way `soundness` that depended on it. The
development now rests on exactly two axioms: `funext` and `tree-decides`
(`proof/scripts/check-postulates.sh` enforces this).

**A second negative result, recorded in that module.** The tempting
strengthening "reaches a NORMAL-FORM value, or diverges" is NOT provable
from `soundness-tree`. A `Reached` leaf supplies only `Value v`, and
`progress⇐` at `v` returns `Value v` again on its `inj₁` branch — never
`NormalForm v`. `tm-lam g d Ω` is exactly such a `Value` (reached in zero
steps, and still stepping). So the first disjunct stays `Reached` as-is.

**Also worth recording:** "a value's reduct is a value" is not available as a
shortcut either. It is not refuted by β — the redex `tm-app (tm-lam …) a` is
neither `Canonical` nor `Neutral` (there is no `Canonical` rule for `tm-app`,
and `n-app` requires a NEUTRAL head, while `tm-lam` is canonical), so it is
not a `Value` at all. But the lemma is not needed: `soundness-nf` above is
proved without it, and the `Ω` counterexample concerns a value stepping to
VALUES (`ξ-lam-body`), not to non-values.

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
