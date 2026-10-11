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
- **The `shift-0` identity law** and the rename/subst laws
  (`Proof/Substitution.agda`): `rename-id`, `rename-compose`,
  `rename-subst`, `subst-compose`, `subst-extSub-wk`, `topSub-rename`.
- **The weakening lookup law** (`Core.Typing`): with the length-indexed
  context, `lookup (extend Γ T) (suc i) ≡ rename wk (lookup Γ i)` is a
  clean `refl`-level induction.
- **The fundamental renaming lemma** `ren⇒`/`ren⇐` and its spine lifting
  `ren-spine` (`Proof/Preservation.agda`): a context morphism transports
  typing across a renaming. The `data` and `ctor` cases are proved from
  `ren-spine`.
- **Weakening** `weaken⇒`/`weaken⇐`: the instance of the renaming lemma at
  `wk`.
- **The substitution lemma** `subst⇒`/`subst⇐`: proved by mutual induction,
  with the binder cases resting on the extended coherence `coh-extend`
  (itself proved from `subst-extSub-wk` and weakening).

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
3. **The application/let/case/effect-bind cases** of the renaming and
   substitution lemmas (`ren-app`, `ren-let`, `ren-case`,
   `ren-effect-bind`, `subst-app`, `subst-data`, `subst-ctor`,
   `subst-case`, `subst-effect-bind`). *Strategy:* the `⇒-app` case needs
   the `substT`/`rename` commutation (which holds for shift-like
   renamings); the others are structural.
4. **`progress`** (`Proof/Progress.agda`) — by cases on the typing
   derivation, consuming the canonical-form lemmas to show β and ι fire.
5. **`preservation`** (`Proof/Preservation.agda`) — the four cases β, ζ, ι,
   δ. β/ζ consume `subst⇐`; ι is the branch-coverage lemma; δ consumes
   `Certified`.
6. **`soundness`** (`Proof/Soundness.agda`) — the type-safety induction
   combining Progress and Preservation.

### The `⇒-app` obstruction and its fix (a finding from this slice)

The `⇒-app` case of the renaming lemma needs

    rename ρ (substT 0 a c) ≡ substT 0 (rename ρ a) (rename (ext ρ) c)

where `c` is the codomain under the binder. At index `suc k` this requires
`ρ (suc k) ≡ suc (ρ k)` — the renaming must **preserve `suc`**. `wk` does
(`wk (suc k) = suc (suc k) = suc (wk k)`), but `ext wk` does **not**
(`ext wk 1 = 2 ≠ 1 = suc (ext wk 0)`), and `ext wk` is exactly the
renaming the codomain is subject to.

Two things make this bite:

1. **`ext` breaks `suc`-preservation unless `ρ 0 ≡ 0`.** `ext ρ` preserves
   `suc` iff `ρ 0 ≡ 0` *and* `ρ` preserves `suc`. `wk 0 = 1`, so the
   extension of the weakening renaming fails.
2. **The binder-order issue forces the general renaming lemma.** A direct
   weakening proof hits `extend (extend Γ S) (shift 1 0 d)` vs
   `extend (extend Γ d) S`, which differ; only a context morphism (a `Fin`
   map) handles the order — and that is exactly the lemma whose `⇒-app`
   case needs `suc`-preservation.

**The candidate fix** is to make the weakening *append* its binder at the
end with the **identity** renaming, while the substitution lemma's `extend`
*prepends*. In the *plain* de Bruijn convention the two commute
definitionally (`(Γ ++ [S]) ▷ d ≡ (Γ ▷ d) ++ [S]`, both `d ∷ (Γ ++ [S])`),
and the identity renaming trivially preserves `suc` and fixes `0`.

**But this conflicts with the global convention.** The typing judgment's
`extend Γ T = renameCtx wk Γ ▷ rename wk T` renames the existing types, so
`extend (Γ ++e S) d` is *not* `(Γ ++e S) ▷ d`, and the commutation fails.
Worse, the substitution lemma's binder case *needs* the global convention:
`lookup (extend Γ d) 0 = rename wk d`, and `subst-extSub-wk` turns
`substS (extSub σ) (rename wk d)` into `rename wk (substS σ d)`, matching the
target context's head. In the plain convention `lookup (extend Γ d) 0 = d`,
and the match fails.

So the two lemmas pull in opposite directions on the context convention:

- the **substitution** lemma needs `extend` to *rename* (global convention),
  so the head type lines up with the substituted binder;
- the **weakening** lemma needs `extend` to *not rename* (plain convention),
  so it commutes with the append-at-end view.

The concrete next step is to reconcile these — e.g. by giving the
append-at-end view its own renaming that matches `extend`, or by
reformulating the substitution lemma's binder case to not need the head to
line up (using the `appSub`-style simultaneous substitution throughout).

### Open research questions (docs/SOUNDNESS.md §7, §8)### Open research questions (docs/SOUNDNESS.md §7, §8)

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
Getting its *operation* right was the main finding of this slice.

Naively, substituting the head variable is `substT 0 a t`. But this is
wrong twice over:

1. Substituting index 0 **shrinks the context**, so a variable at index
   `suc k` in `extend Γ A` must become index `k` in `Γ`.
2. A post-hoc `rename pred` would also renumber the substituted term `a`,
   which lives in `Γ` and must be inserted unchanged.

The correct operation is a **simultaneous substitution** (`Core.Syntax`
`Sub = ℕ → Term`), which replaces every free variable at once:

    topSub a zero    = a
    topSub a (suc k) = tm-var k

so the substituted term is inserted as-is while every other variable is
renumbered down by one. Under a binder the substitution is extended by
`extSub` (the new binder maps to itself, everything else shifts).

This is the term-side counterpart of the context surgery `removeAt` /
`embedFin` in `Proof/ContextSubst.agda`. With it, the `⇒-var` cases are
clean:

- **index 0**: the term becomes `a`, and the type `A` is `0`-free (it is
  scoped in `Γ`, and the global convention keeps its free variables above
  the new binder), so `substTop a A = A`. The goal is `Γ ⊢ a ⇐ A`.
- **index `suc k`**: the term becomes `tm-var k`, and the type
  `rename wk (lookup Γ k)` becomes `lookup Γ k`. The goal is
  `Γ ⊢ tm-var k ⇒ lookup Γ k`, which is `⇒-var k`.

All the syntactic pieces are proved (`subst-id`, `subst-var-eq/neq`,
`rename-id`, `lookup-extend`, `lookup-remove`, `substS`/`extSub`). What
remains is the induction threading `substS` through every typing rule.

The one structural subtlety still to resolve is the interaction between
`extSub` and the weakening renaming. The "substitution undoes weakening"
law needs `substS (topSub a) (rename wk T) ≡ T`, but under a binder
`rename (ext wk)` maps `suc j ↦ suc (suc j)` while `extSub (topSub a)`
maps `suc (suc j) ↦ suc j` — the two extensions are *adjoint*.

The clean fix is to define the substitution's binder extension **relative
to the renaming**: for a simultaneous substitution `σ` and a renaming `ρ`,
the extension under a binder maps `zero ↦ var zero` and `suc (ρ j) ↦ σ j`.
Then the general law

    substS (extSub ρ σ) (rename (ext ρ) t) ≡ substS σ t

holds by induction, and the "undo weakening" law is its instance at
`ρ = wk` and `σ = topSub a`. The machinery (`extSub`, `extSub^`, `substS`)
is in place; the parameterisation of `extSub` by `ρ` is the concrete next
step.

## Building## Building## Building

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
