# Mechanised soundness proof for the Cure Core kernel

This directory holds the **deliverable B development**: an
[Agda](https://wiki.portal.chalmers.se/agda/) formalisation toward soundness
of the Cure Core kernel. It is the formal counterpart of the written argument in
[`../docs/SOUNDNESS.md`](../docs/SOUNDNESS.md), whose §7 scopes exactly this
development.

> **Status: foundation repair in progress.** The legacy full theorem interfaces
> were refuted and are now frozen only in `Proof.InterfaceAudit`. Active
> conversion compares TWO rigid type heads, not arbitrary raw syntax;
> universe cumulativity belongs to declarative typing, not equality.
> `Proof.ReductionConversion` now inhabits every conversion-record field
> AND full `ReduceConv`, using common reducts after compact-literal
> expansion. `Proof.SoundnessModel` jointly instantiates the current
> soundness hypotheses on a nonempty closed-entry fragment with a finite
> typed global table. This is NOT executable NbE/η refinement.
> The old `ClosedSig` oracle is frozen:
> active consumers use
> inhabited `ClosedFragmentSig`, restricted to individually closed entries,
> **not** full dependent telescopes. The old global coverage oracle is now frozen
> only as a negative regression: each admitted case carries local coverage.
> A fourth historical contradiction, global literal
> arities, is now retained only as a frozen negative regression: the active
> reduction rules carry local arity witnesses and `Conf` no longer assumes it.
> The existing derivations below are retained for repair, not certification.
> Coverage is migrated into case typing. `Core.Verification` and
> `Proof.VerificationExamples` still provide unintegrated scoping/conversion
> candidates; those remaining interfaces have not been migrated.
> Their examples are not an instance of the full soundness theorem.
> Exact-arity closed-entry branch order IS migrated to last-field-first,
> with heterogeneous preservation regressions and a proved frame bridge.
>
> The following is the **conditional derivation status**, subject to that
> applicability warning. The current restricted Core typing specification
> compiles cleanly; full dependent-signature support is unfinished.
> The canonical-form, renaming and substitution lemmas, **Progress**, **`Final`-preservation**,
> and **`preservation` (every case, including ι and δ)** are all **proved**,
> and so are the constructive soundness theorems: the **fuel-indexed
> `soundness-fuel`** and the **coinductive `soundness-tree`**.
>
> The classical statement is `soundness-nf` in `Proof/SoundnessConfluence.agda`
> — the dichotomy **`Reached ⊎ DivergesNF`** over NORMAL FORMS, proved with
> **zero postulates**. The whole development now rests on exactly **two**
> named postulates: `funext` (standard function extensionality) and
> `tree-decides` (LPO on the outcome path). This inventory does not account
> for the remaining model/refinement obligations. All five historical
> termination overrides are eliminated. Confluence now uses a strong
> strict-parallel diamond and checked closure recursion.
>
> **Correction.** An earlier revision derived a classical three-way
> `soundness` from a second input, `never-reached→no-value`. That input is
> **FALSE** for the mechanised `_⇝_` (it reduces under binders, so
> `tm-lam g d Ω` is a canonical `Value` that steps to itself forever, and is
> therefore both `NeverReached` and `Reached`). Both the postulate and the
> theorem built on it have been **removed**; `soundness-nf` is the honest
> replacement.
> See [Status](#status) for the lemma-by-lemma breakdown.

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
| Totality gates δ (§3.2) | `Certified` + `CertifiedTyped` | `Env.certified?` + `Normalise.unfold_certified_head` |
| Coverage (§3.3) | `CaseCoverage` in each `⇒-case` | `check_coverage` + `branch_unify` (indexed omissions still outside the model) |
| Builtin ctor names | `BuiltinCtors` | `@builtin_ctor_aliases` |

The hole/absurd discipline (§3.4) is expressed by restricting the theorem to
**final** Core — hole-free and absurd-free terms (`Final` in
`Proof/Progress.agda`), mirroring `Validator.release_config/0`.

The legacy `Certified` predicate is only body finality, now also named
`BodiesFinal`; it does **not** express semantic termination.
`CertifiedTyped` separately supplies closedness and body typing.
The executable checks untrusted SCC/closure proposals using trusted finite
verifiers. Extraction soundness, the size-change termination principle, and
its connection to certified unfolding remain unproved here.

## Legacy module map (historical derivation status, not certification)

| Module | Contents | Status |
|---|---|---|
| `Core.Grade` | The QTT carrier `{0,1,≤1,ω}`; additive/multiplicative monoids; subusaging preorder; all laws by exhaustive case analysis | ✅ complete |
| `Core.Universe` | The three-element universe hierarchy `l0 : l1 : l2`; cumulativity `_≤ˡ_`; max `_⊔ˡ_`; `succLevel` | ✅ complete |
| `Core.Syntax` | `Term` (faithful to `Cure.Core.Term`); de Bruijn `shift`/`substS` (simultaneous substitution); `Scoped`/`Closed` | ✅ complete |
| `Core.Value` | The NbE value domain: closures, neutrals, size-indexed so closures are structurally smaller | ✅ complete |
| `Core.Reduction` | The reduction relation `_⇝_` (β, ζ, ι, δ, congruence, and the `ι-nat-*`/`ι-bounded-*` literal peels) and its reflexive-transitive closure | ✅ complete |
| `Core.Signature` | Inductive families, constructors, telescopes; nested strict positivity | ✅ complete |
| `Core.Typing` | Declarative infer/check judgments with conversion and cumulative-sort closure, over a length-indexed context with `Fin` lookup | Conditional specification; not executable minimal synthesis |
| `Proof.Values` | The `Canonical`/`Neutral`/`Value` split (a value includes neutrals) | ✅ complete |
| `Proof.Inversion` | Accumulated-conversion inversion; constructor/literal metadata | Derived from rigid-head separation and exposed Π injectivity; raw `conv-injective-*` removed |
| `Proof.CanonicalForms` | `canonical-pi-value`, `canonical-ctor` | ✅ **proved** (= `invert-*-check`) |
| `Proof.Substitution` | shift/subst algebraic laws | ✅ `shift-0`, `shift-var-1`, the rename/subst interaction laws, and the branch-field lemmas **proved**; only `shift-subst` (app case) open |
| `Proof.Context` | Length-indexed context laws: weakening lookup, `extendⁿ` lookup, branch morphism `extF` | ✅ **proved** |
| `Proof.Progress` | `Final` Core; the four side conditions; `progress` | ✅ **proved** |
| `Proof.Preservation` | `weaken`, `subst⇒`, `subst⇐`, `check-infer`, `preservation` | ✅ **fully proved** (all cases incl. β/ζ/ι/δ) |
| `Proof.FinalPreservation` | `substS-final` (closure of `Final` under a final substitution); `final-preservation` | ✅ **proved** |
| `Proof.Soundness` | `EvalResult`; `soundness-fuel` (constructive); `Diverges`/`EvalTree`/`soundness-tree` (coinductive); `tree-decides` (the only classical input) | ✅ **`soundness-fuel` and `soundness-tree` proved**; the classical `soundness` and its false postulate were **removed** (see `Proof.SoundnessConfluence`) |
| `Proof.Confluence` | Exposes `Proof.StrictConfluence` under the original `Conf sig ClosedBody` interface | Specification confluence checked without bypasses; not executable refinement |
| `Proof.SoundnessConfluence` | `NormalForm`; `never-reached-not-nf` (the TRUE form of classical input 3, over normal forms); `DivergesNF` + `never-reached→divergesNF`; `soundness-nf` — the dichotomy `Reached ⊎ DivergesNF`, leaving `tree-decides` as the only classical input | ✅ **complete** (zero postulates; replaces the false `never-reached→no-value`) |

## Status

### Historical derivations (machine-checked, applicability under repair)

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
- The declarative typing judgment built from bidirectional rules, explicitly
  closed under conversion and cumulative sorts. It is not the graph of
  `Cure.Core.Kernel`'s minimal type synthesis.
- **The canonical-form lemmas** `canonical-pi-value` and `canonical-ctor`
  (`Proof/CanonicalForms.agda`), proved by composing the checking-mode
  head-inversion lemmas.
- **The head-inversion lemmas** `invert-pi` / `invert-data`
  (`Proof/Inversion.agda`), proved by induction on the inference derivation:
  conversion witnesses are accumulated across arbitrary intermediate types.
  Only at introduction rules are two rigid type heads compared; no
  converted raw term is forced to have literal Π/data syntax.
  `invert-data` is stated as a three-way
  disjunction — a `tm-ctor` OR a builtin `tm-nat_lit`/`tm-bounded_lit` —
  because a nat/bounded literal is canonical and infers a data type but is
  not a `tm-ctor` (see [The `invert-data` finding](#the-invert-data-finding)).
- **The `shift-0` identity law** (`Proof/Substitution.agda`), proved from
  `shiftRen-0` and `rename-id` — no term induction needed.
- **The rename/subst interaction laws** (`Proof/Substitution.agda`):
  `rename-id`, `rename-compose`, `rename-subst`, `subst-compose`,
  `subst-extSub-wk`, `subst-extSub^-shift` (the `ar`-fold generalisation),
  `rename-raise`, `rename-topSub`, and the branch-field lemmas
  `renameTerms-field-vars` / `substTerms-field-vars` / `rename-branch-motive`
  / `subst-branch-motive`.
- **The `extendⁿ` context laws** (`Proof/Context.agda`): the field-hole and
  `raise`-lookup laws, and the branch context morphism `extF` with its
  coherence `extF-coh` and lookup law `lookup-extF`.
- **The weakening lookup law** (`Core.Typing`): with the length-indexed
  context, `lookup (extend Γ T) (suc i) ≡ rename wk (lookup Γ i)` is a
  clean `refl`-level induction.
- **The fundamental renaming lemma** `ren⇒`/`ren⇐` and its spine/branch
  liftings `ren-spine`/`ren-branches` (`Proof/Preservation.agda`): a context
  morphism transports typing across a renaming. The `data`, `ctor`, `let`,
  `case`, and `effect-bind` cases are all proved — the `case` case via
  `ren-branches` and the branch morphism `extF`, the `let` case via
  `rename-topSub`, and `effect-bind` via `ext-wk-rename`.
- **Weakening** `weaken⇒`/`weaken⇐`: the instance of the renaming lemma at
  `wk`.
- **The substitution lemma** `subst⇒`/`subst⇐`: proved by mutual induction,
  with the binder cases resting on the extended coherence `coh-extend`, the
  `case` case on the `ar`-fold coherence `coh-extendⁿ`, and the spine/branch
  liftings `subst-spine`/`subst-branches`. The `data`, `ctor`, `let`, `case`,
  and `effect-bind` cases are all proved.
- **The conversion congruences** `rename-conv`/`subst-conv`: now fields of
  the `Conversion` record (`Core/Typing.agda`), re-exported as projections —
  conversion is specified as a syntactic congruence.
- **`check-infer`** (`Proof/Preservation.agda`): a hole-free term that CHECKS
  against a type has a matching DECLARATIVE inference derivation, not a
  claim about executable minimal synthesis. This generalises `value-infer`,
  needs no value structure, and dissolves the β/ζ inference-preservation
  gaps: the checking-mode `preserve-β`/`preserve-ζ` reducts infer their type
  once the redex is `Final` (`substTop-hole-free`).
- **`branches-conv`** (`Proof/Preservation.agda`): branch typing is stable
  under CONVERSION of the motive (via `≈-rename`), which types the
  `ξ-case-motive` congruence.
- **`preservation` — every case** (`Proof/Preservation.agda`, **no
  postulates**): the `ξ-*` congruence cases, the β/ζ cases (via
  `preserve-β`/`preserve-ζ` + `check-infer`), the checking-mode λ/hole cases,
  the δ case (via `CertifiedTyped` + `weaken-closed`), and the ι case
  (including all four literal-peel variants), threading a `Final t`
  hypothesis. The former `preservation-other`, `preservation⇒-β`,
  `preservation⇒-ζ`, `preservation⇒-case`, `preservation⇒-case-motive`,
  `preservation-δ`, and the five `preservation-ι*` postulates are all gone.
- **The `brs∷` field-telescope change** (`Core/Typing.agda`): the branch rule
  now types the field binders with the constructor's argument telescope
  (`extendTele Γ (ctor-args ct)`) and stores `length (ctor-args ct)` as the
  branch arity, so the ι substitution lemma relates the field variables to
  the constructor's actual arguments. The supporting context machinery
  (`extendTele`, `teleField`, `fieldFin`, `lookup-extendTele-*`, `extF-tele`,
  `lookup-extF-tele`) is in `Core/Typing.agda` / `Proof/Context.agda`.
- **The compact-literal identification** (`Core/Typing.agda`): the
  `Conversion` record gains `≈-nat-zero`/`≈-nat-suc`/`≈-bounded-zero`/
  `≈-bounded-suc`, recording that a compact `tm-nat_lit`/`tm-bounded_lit` is
  definitionally the constructor term it peels to (as the kernel's
  `Eval.nat_to_ctor`/`bounded_to_ctor` do). `BuiltinCtors` is strengthened to
  give the builtin constructors' argument telescopes.
- **`weaken-closed`** (`Proof/Preservation.agda`): a CLOSED term that types
  in the empty context types in any context (the context morphism
  `Fin 0 → Fin n` is vacuous, and renaming is the identity on closed terms).
- **`CertifiedTyped`** (`Proof/Preservation.agda`): the well-typedness half
  of the totality certificate — a certified global's body is closed and
  infers the global's declared type in `⟨⟩`. This is what makes the δ
  (certified unfolding) case type-preserving.
- **`Final`-preservation** (`Proof/FinalPreservation.agda`): `Final` is
  closed under renaming (`rename-final`) and under a substitution whose every
  image is final (`substS-final`, via the `FinalSub` predicate). The two
  substitutions the β/ζ/ι rules use are final when their inputs are
  (`topSub-final`, `argsSub-final`), and `final-preservation` itself consumes
  `Certified sig` for the δ case — the body's finality is exactly what the
  totality certificate supplies.
- **The fuel-indexed soundness theorem** `soundness-fuel`
  (`Proof/Soundness.agda`): by induction on the fuel `n`, consuming
  `progress⇐`, `preservation`, and `final-preservation`, it returns either a
  reached value (with its type, value witness, and multi-step reduction) or
  `exhausted`. Its positive outcome is the classical first disjunct
  (`reached→eval`), and `never-stuck` records the "never stuck" corollary.
- **The coinductive soundness theorem** `soundness-tree`
  (`Proof/Soundness.agda`, under `--guardedness`): the outcome as a
  coinductive tree `EvalTree`, proved by guarded corecursion. Divergence is
  given positively by the greatest fixed point `Diverges`, inter-derivable
  with the tree's never-reaching spine `NeverReached`
  (`never-reached→diverges` / `diverges→never-reached`), and the fuel-indexed
  run is exactly the depth-`n` truncation of the tree
  (`soundness-fuel≡truncate`).

### Historical proof-development notes (superseded by the interface audit)

These are historical proof-development inputs, not the current postulate inventory:

1. **`conv-injective-data` / `conv-injective-pi`** (`Proof/Inversion.agda`) —
   were based on raw syntax reflection, later refuted with reduction.
   Those helpers are now removed. Generalized inversion accumulates
   conversion and uses separation only when both heads are rigid.
2. **The application case** of the renaming and substitution lemmas
   (`ren-app`, `subst-app`). This was the **one documented obstruction**; it
   is now **resolved** by using the top substitution `substTopT` for the
   codomain instantiation (see
   [The `⇒-app` obstruction](#the--app-obstruction-and-how-it-dissolves-a-finding-from-this-slice)).
   All cases of the renaming and substitution lemmas are now proved.
3. **The closedness axioms for the signature** (`rename-global-type`,
   `tele-closed`, `rename-ctor-result`, `tele-closed-subst`,
   `subst-ctor-result`, `subst-global`). These are well-formedness
   assumptions: a global's declared type and the signature's telescopes are
   *closed*, so renaming/substitution leaves them unchanged. They are now
   **derived for the explicit closed-entry fragment** from
   `ClosedFragmentSig ind sig`, using actual lookup/membership witnesses and
   `rename-closed` / `substS-closed`. The original arbitrary-record
   `ClosedSig` hypothesis was refuted and is frozen only in the audit.
4. **`progress`** (`Proof/Progress.agda`) — **PROVED** by mutual cases on the
   typing derivation (infer and check), consuming the canonical-form lemmas to
   show β and ι fire. See [The `progress` inputs](#the-progress-inputs).
5. **`preservation`** (`Proof/Preservation.agda`) — **FULLY PROVED** (no
   postulates). The `ξ-*` congruence cases, the β/ζ cases, the checking-mode
   λ/hole cases, the δ (certified unfolding) case, and the **ι (branch
   substitution) case** (including all four literal-peel variants) are all
   proved, generalised to an arbitrary context `Γ` and threading a `Final t`
   hypothesis. The former inference-preservation gaps are dissolved by
   `check-infer`; the `ξ-app₂`/`ξ-let`/`ξ-case`/`ξ-case-motive` conversions
   by `ReduceConv` and `branches-conv`; δ by the `CertifiedTyped` hypothesis
   and `weaken-closed`; and ι by the `brs∷` field-telescope change (below).
   See [The `preservation` findings](#the-preservation-findings).
6. **`soundness`** — the type-safety induction combining Progress and
   Preservation. **Both constructive forms are PROVED**: the **fuel-indexed
   `soundness-fuel`** and the **coinductive `soundness-tree`**
   (`Proof/Soundness.agda`). The **classical** statement is
   **`soundness-nf`** (`Proof/SoundnessConfluence.agda`), the dichotomy
   `Reached ⊎ DivergesNF` over normal forms, resting only on `tree-decides`;
   see
   [The `soundness` finding](#the-soundness-finding-resolved-by-fuel-indexing-and-coinduction).
### The `progress` inputs

The coverage input is now repaired and local to each admitted case. The
following derivation inputs remain subject to the conversion applicability
warning above:

- **Canonical-form lemmas** (`canonical-pi-value` / `canonical-ctor`): turn a
  canonical Π/data value into a λ / constructor-like head, so β and ι fire.
- **`spine-length`** (`Core.Typing`) and local `CaseCoverage` evidence:
  match checked constructor arguments to the selected branch's arity.
- **`ctor-info`** (`Proof.Progress`): connects an inferred constructor to
  its actual owning family, so coverage asks only for that family's branches.
- **The literal-peeling reduction rules** (`ι-nat-zero` / `ι-nat-suc` /
  `ι-bounded-zero` / `ι-bounded-suc` in `Core.Reduction`): a `case` on a
  compact `tm-nat_lit` / `tm-bounded_lit` scrutinee is NOT stuck — it peels
  one layer to `Z`/`S` / `First`/`Next`, exactly as the kernel's
  `Eval.nat_to_ctor_if` / `bounded_to_ctor_if` do. This closes the gap the
  `invert-data` finding exposed: without it, a well-typed case on a literal
  would be stuck.
- **Neutral terms are `Value`s** (the `inj₁` branch), so the elimination
  rules are never stuck; `⇒-var` is vacuous (`Fin 0` is empty).

`CaseCoverage` (`Core.Coverage`) now belongs to each `⇒-case` derivation.
It provides named lookup and arity witnesses, with compact-literal branches
required only for the relevant builtin family identity. The impossible old
global `Covers` interface exists only in `Proof.InterfaceAudit`.

### The `preservation` findings

Proving `preservation` surfaced three genuine tensions in the framework,
all resolved by extending it:

- **β / ζ do not preserve INFERABILITY — DISSOLVED.** The β reduct
  `substTopT a b` has its continuation only *checked* (`b` checks the
  codomain, it does not infer it), so it cannot be shown to infer `T`
  directly. The resolution is `check-infer` (`Proof/Preservation.agda`):
  **a hole-free term that CHECKS against a type INFERS it.** The only
  checking rule without a matching inference rule is `⇐-hole`, and a
  hole-free term is never a hole; every other rule (`⇐-lam`, `⇐-infer`,
  `⇐-conv`, `⇐-cumul`) has an inference rule with the same premises. So the
  checking-mode `preserve-β` / `preserve-ζ` reducts infer their type as soon
  as the redex is `Final` (hence the reduct is hole-free,
  `substTop-hole-free`). The former `preservation⇒-β` / `preservation⇒-ζ`
  postulates are gone.
- **The `ξ-app₂` / `ξ-let` / `ξ-case` / `ξ-case-motive` result types name
  their subterm SYNTACTICALLY** (`⇒-app` returns `substTopT a c`, `⇒-case`
  returns `tm-app m s`), so the reduced subterm's type differs unless the
  two are convertible. Resolved by the `ReduceConv` hypothesis (`⇝ ⊆ ≈`):
  the kernel's `conv?` normalises both sides, so a reduct is definitionally
  equal to its redex. `≈-subst-cong` (substitution congruence) relates
  `substTopT a c` to `substTopT a′ c`, and `branches-conv` (conversion
  stability of branch typing, via `≈-rename`) handles the motive.
- **The `ξ-lam-body` / `ξ-pi-cod` congruences reduce UNDER A BINDER**, so
  `preservation` is generalised from `⟨⟩` to an arbitrary context `Γ`; the
  `ξ-lam-dom` / `ξ-pi-dom` cases (which change the binder's domain) are
  transported by the CONTEXT CONVERSION lemma (`conv⇒` / `conv⇐`).

The `preservation` function threads a `Final t` hypothesis (needed by
`check-infer`), and handles the checking-mode λ/hole cases directly. **Every
case is now proved** — the δ (certified unfolding) case via the
`CertifiedTyped` hypothesis (below), and the ι (branch substitution) case via
the `brs∷` field-telescope change:

- **The ι (branch substitution) case.** The `⊢*brs` rule originally typed a
  branch's field binders with `tm-hole "field"` (`extendⁿ`), but the ι
  reduction substitutes the constructor's REAL arguments (typed by
  `ctor-args ct`), so the substitution lemma could not relate the hole-typed
  field variables to the actual args. **Resolved** by changing `brs∷` to type
  the field binders with the constructor's argument telescope
  (`extendTele Γ (ctor-args ct)`), and by making the branch arity literally
  `length (ctor-args ct)`. The ι proof is then a direct application of the
  substitution lemma with the coherence `argsSub-coh` (field positions map to
  the constructor arguments, base-environment positions are the identity).
  The four literal-peel variants (`ι-nat-zero`/`ι-nat-suc`/`ι-bounded-zero`/
  `ι-bounded-suc`) additionally use the `Conversion` record's compact-literal
  identification (`≈-nat-zero`/`≈-nat-suc`/`≈-bounded-zero`/`≈-bounded-suc`)
  and the `BuiltinCtors` telescope facts.

### The `CertifiedTyped` hypothesis (the δ case)

`Certified` (`Proof.Progress`) says a certified global's body is FINAL, but
δ preservation needs it to INFER the global's declared type. This is the
well-typedness half of the kernel's `Env.certified?`, and it is carried as a
separate hypothesis `CertifiedTyped` (`Proof/Preservation.agda`):

```agda
CertifiedTyped ind sig conv =
  ∀ {f body′ T} → body sig f ≡ just body′ → type-of sig f ≡ just T
    → Scoped 0 body′ × ⟨⟩ ⊢ body′ ⇒ T
```

It is separate from `Certified` because it mentions the typing judgment,
which `Certified` cannot (being defined before the judgment). The body is
CLOSED, so `weaken-closed` types it in any `Γ` (the context morphism
`Fin 0 → Fin n` is vacuous and the renaming is the identity on closed
terms). `preservation-δ` is then a direct application, and the former
postulate is gone.

### The `soundness` finding, resolved by fuel-indexing and coinduction

`soundness` as stated ("reaches a value, OR raises, OR diverges") is a
**classical** disjunction: the `diverges` outcome is a negative statement
(no value is reachable), and deciding which disjunct holds requires
coinduction (or a well-founded measure). The module supplies **both
constructive views**, and keeps the classical statement as the
(non-constructive) collapse of them.

**The bounded unfolding: `soundness-fuel`.** The fuel-indexed theorem

```agda
soundness-fuel :
  ∀ (n : ℕ) {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → FuelResult t T
```

returns either a **reached** value (with its type, value witness, and the
multi-step reduction to it) or **exhausted** (the fuel ran out), by
induction on the fuel `n`. At each step it consumes exactly the three
lemmas the argument needs:

- **`progress⇐`** — a well-typed final term is a value or it steps;
- **`preservation`** — the reduct keeps the type;
- **`final-preservation`** — the reduct is still final, so `progress⇐`
  applies again.

**The coinductive completion: `soundness-tree`.** The full outcome is a
(possibly infinite) tree, defined as a coinductive record:

```agda
record EvalTree (t T : Term) : Set where
  coinductive
  field outcome : Reached t T ⊎ (∃ λ t′ → _⇝_ sig t t′ × EvalTree t′ T)

soundness-tree : ⟨⟩ ⊢ t ⇐ T → Final t → EvalTree t T
```

proved by **guarded corecursion** (`{-# OPTIONS --guardedness #-}`): a
`Reached` leaf is a terminating evaluation, and a `Stepped` node continues
at the reduct (which keeps its type and stays final). An INFINITE
evaluation is now a finite (cyclic) proof object — divergence is given
POSITIVELY by the greatest fixed point

```agda
record Diverges (t : Term) : Set where
  coinductive
  field diverges-step : ∃ λ t′ → _⇝_ sig t t′ × Diverges t′
```

`Diverges` and the tree's never-reaching spine `NeverReached` are
inter-derivable (`never-reached→diverges` / `diverges→never-reached`), and
the fuel-indexed run is exactly the depth-`n` truncation of the tree
(`soundness-fuel≡truncate`).

**The classical statement** now lives in `Proof/SoundnessConfluence.agda` as
`soundness-nf`, the dichotomy `Reached t T ⊎ DivergesNF t` over NORMAL FORMS.
It rests on ONE classical input:

- **`tree-decides`** — the outcome tree is finite or infinite. The tree is a
  PATH (each node has at most one child, because `progress` returns a specific
  reduct), so this is exactly the limited principle of omniscience (LPO) on
  that path — not constructive.

**REMOVED — `never-reached→no-value`.** An earlier revision derived a
classical three-way `soundness` here from a second input, a never-reaching
tree has no reachable value. **That input is FALSE** for the mechanised
`_⇝_`, which reduces UNDER BINDERS (`ξ-lam-body`): `Ω = (λx. x x) (λx. x x)`
satisfies `Ω ⇝ Ω`, so `tm-lam g d Ω` is a canonical `Value` that steps to
itself (hence `NeverReached`), yet `tm-lam g d Ω ⇝* tm-lam g d Ω` with
`Value (tm-lam g d Ω)`. Confluence (`Proof.Confluence.confluence`, PROVED)
does not rescue it — the counterexample is a value stepping to values
forever. Both the postulate and the `soundness` built on it have been
**deleted**; the true form over normal forms is `never-reached-not-nf` /
`soundness-nf`. See docs/CONFLUENCE.md for the full finding.

The constructive content is unchanged: a `Reached` node gives the first
disjunct (`tree-reached→eval`), and a `NeverReached` tree gives positive
divergence (`never-reached→diverges`). The `raises` outcome is the coverage
guard, unreachable with case-local coverage (so never produced). The "never stuck"
corollary is `never-stuck` (= `progress⇐`): a well-typed final term is never
stuck.

### `Final`-preservation (the new module `Proof.FinalPreservation`)

The fuel-indexed induction needs the reduct of a final term to still be
final. `Final` is "hole-free and absurd-free"; its congruence cases are
structural, and the β/ζ/ι cases rest on the closure of `Final` under a
substitution whose every image is final (`substS-final`, with the
`FinalSub` predicate `∀ k → Final (σ k)`). The two substitutions the rules
use are final when their inputs are (`topSub-final`, `argsSub-final`).

The **δ case is where the totality certificate's well-formedness half is
needed**: a `Final` global carries no information about its body, so
`final-preservation` takes `Certified sig` as a hypothesis — exactly the
predicate Progress already assumes (`∀ {f body′} → body sig f ≡ just body′
→ Final body′`) — and reads the body's finality off it. This is the same
hypothesis that gates δ in the kernel's `Env.certified?`.

A supporting refactor: `argsSub`'s worker `go` is now the top-level
`argsSub-go` (`Core/Reduction.agda`), so the metatheory can reason about
the shape of `argsSub`'s images (the first `length args` indices map to the
fields, the rest to variables).

### The `invert-data` finding

The naive canonical-form lemma "a canonical value of data type is a
`tm-ctor`" is **false**. `tm-nat_lit m` and `tm-bounded_lit k` are canonical
(`c-nat_lit` / `c-bounded_lit`) and infer `tm-data Nat [] []` /
`tm-data Bounded [] []` (via `⇒-nat_lit` / `⇒-bounded_lit`), but they are not
`tm-ctor`s. The kernel resolves this by treating a `{:vnat, n}` as
*definitionally* the `Z`/`S` tower (`Eval.nat_to_ctor`; `bounded_to_ctor` for
bounded), so a `case` on a literal still fires ι after peeling the literal to
a constructor.

The honest lemma is therefore the three-way disjunction

    invert-data : ... → (Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args)))
                      ⊎ (Σ ℕ (λ m → t ≡ tm-nat_lit m))
                      ⊎ (Σ ℕ (λ b → t ≡ tm-bounded_lit b))

which `progress`'s `case` branch consumes by peeling the literal disjuncts to
a ctor. `canonical-ctor` (`Proof/CanonicalForms.agda`) is restated to match.
### The `⇒-app` obstruction, and how it dissolves (a finding from this slice)

The `⇒-app` case of the renaming lemma needs

    rename ρ (cod[a]) ≡ cod[rename ρ a]

where `cod` is the codomain under the binder. The README previously recorded
this as the one hard obstruction: with the naive codomain instantiation
`substT 0 a c`, the identity at index `suc k` requires the renaming to
preserve `suc`, which `ext wk` does not — and `ext wk` is exactly the
renaming the codomain is subject to.

**The obstruction dissolves once the codomain instantiation is the RIGHT
operation.** The kernel's `Eval.apply_closure(cod_closure, a_value)` evaluates
the codomain in the environment `[a_value | env]` — it PREPENDS the argument
at index 0 and shifts everything else. That is the **top substitution**
`substTopT a c = substS (topSub a) c`, NOT `substT 0 a c` (which leaves the
indices above 0 dangling). With `substTopT`:

    rename ρ (substTopT a c) ≡ substTopT (rename ρ a) (rename (ext ρ) c)

is exactly `rename-topSub` (Proof/Substitution.agda), proved from
`rename-subst` + `subst-rename` — no `suc`-preservation needed. The
substitution side is the dual `subst-topSub`.

Two further rule fixes make the remaining cases well-scoped and provable:

- **`⇒-app` and the β/ζ rules use `substTopT`** (matching the kernel's
  `apply_closure`), not `substT 0`.
- **`⇒-lam` CHECKS the body** and **`⇐-lam` shares its premises**, so a
  checked λ can be turned into an inferring one (`value-infer`), which the
  β/ζ cases need (the argument of `⇒-app` is only checked).

### The β/ζ `Value` side conditions are vestigial (a finding from this slice)

An earlier formulation carried a `Value` side condition on β/ζ in **both**
`_⇝_` (`Core/Reduction.agda`) and `_⇉_` (`Core/Parallel.agda`), mirroring the
kernel's `Eval.apply(vlam, varg)`. This was believed load-bearing for
Preservation's β/ζ cases. Inspection of the actual proofs shows it is **not**:

- `preserve-β` never uses `Value a` — it applies `substTop⇐` to the argument's
  *checking* derivation `da : Γ ⊢ a ⇐ d` directly.
- `preserve-ζ` used `Value v` only to call `value-infer`, but the general
  `check-infer` (a hole-free term that checks infers its type) subsumes it, and
  hole-freeness comes from the `Final t` hypothesis the induction threads.

So the `Value` premises were **removed** from `_⇝_`'s `β`/`ζ` and `_⇉_`'s
`p-β`/`p-ζ`. The strict-parallel `_⇛_` used for confluence is also value-free.
Its one-step substitution proof needs no `substS-Value-or-redex` case
analysis or value transport. The older wide `_⇉_` remains checked
simulation machinery, not the strong-diamond relation.
**Do not re-introduce the side conditions.**

### Structural erasure with administrative let collapse
- **Structural erasure with let collapse is idempotent.** `Proof.Erase`
  proves `erase-idem` with no new postulates, holes, or termination overrides.
  Lets collapse when their **erased body** is variable zero; surviving lets
  receive the unrestricted runtime grade, matching the executable let rules.
  The proof uses a direct fixed-point lemma for the Boolean-dispatched let
  constructor. Definitional regressions cover direct/nested collapse and
  nonzero-variable bodies. This theorem does **not** include signature-based
  argument filtering: `eraseSpine` is separate and is not called by
  `eraseTerm`. It is not an idempotence proof for the full executable eraser.

### Interface audit and replacement examples
`Proof.InterfaceAudit` proves:
- The frozen historical `Covers ind` and `BuiltinCtors ind` are incompatible;
  no active theorem accepts that oracle anymore.
- The frozen historical `ClosedSig ind sig` is uninhabited; active consumers
  now require the membership-indexed closed-entry fragment.
- The frozen historical `RawPiReflection conv` and `ReduceConv sig conv`
  are incompatible. Active `Conversion` no longer accepts raw reflection.
- The frozen historical `LiteralArity` is uninhabited; it is no longer an
  active confluence parameter.

These are refutations, not additional axioms. Successful compilation alone
does not establish full soundness-model applicability. The independent
specification confluence theorem now has a checked, inhabited interface.

The local literal-arity repair is connected to the existing proof consumers:
small-step and parallel literal rules require arity witnesses, and progress
derives these from the actual checked branches and builtin constructor
telescopes. Renaming, substitution, finality, preservation, and confluence
are migrated. `Proof.LiteralCases` contains positive/negative rule tests
and a concrete confluence peak using only an inhabited `ClosedBody`
signature parameter. That confluence theorem now has a termination-checked
strong-diamond/closure proof with no bypass.

### Active case-local coverage
`Core.Coverage` defines `CaseCoverage ind family branches`, required by the
`⇒-case` typing rule. Progress and the soundness modules no longer take
`Covers`; renaming, substitution, context conversion, and all case-reduction
preservation consumers carry or transport local coverage. The interface
requires full-family coverage and canonical compact-literal branch
names/arities; index-based impossible-branch omission remains outside it.

`Proof.CoverageExamples` provides positive Nat coverage in an environment
with unrelated Bool constructors, empty-family coverage, missing-constructor,
wrong-arity and duplicate-first-match rejection, and preservation under
renaming, substitution and a real branch reduction. It also rejects an empty
Nat case at the inference-derivation level, including `⇒-conv` wrappers.
This refutation is parameterised by abstract `Conversion`; these examples
do not instantiate the full soundness theorem.

`Core.Verification` still defines candidate preceding-binder-scoped
telescopes and constraints on actual signature members. It also defines executable-order field instantiation and
reduction-based Π/data exposure. `Proof.VerificationExamples` provides a
scoped dependent constructor, a nonempty scoped signature, missing/wrong-arity
rejection, empty-family coverage, distinguishable field substitutions,
result-index instantiation, and a let exposing a Π.
These establish inhabited predicates, **not declaration typing, a verified
conversion relation, or a repaired progress/preservation theorem**.

### Active closed-telescope signature fragment
`Core.ClosedFragment` defines `ClosedFragmentSig`: global types and
registered family/constructor entries/results are closed, with obligations
restricted to actual members. Preservation's renaming/substitution helpers
and its branch transports now require actual lookup/membership evidence.
The preservation and both soundness module parameters are migrated.

`Proof.ClosedFragmentExamples` proves the invariant for registered
Nat/Bool/Void families and a nonempty global type table. It rejects
registered open parameters/fields/results without constraining unregistered
open records. A well-scoped dependent telescope is deliberately rejected by
this fragment, while its candidate `ScopedFamily` witness remains inhabited.
**This does not complete dependent telescope/result instantiation or prove
that full Cure signatures satisfy this closed-entry restriction.**
Those dependent typing/scoping migrations and executable refinement remain open.

### Checked forward-dependent spine foundation
`Core.LocalFrame` models declaration-order arguments pushed into a
most-recent-first frame. It proves agreement with reversed-field
simultaneous substitution for **arbitrary bodies**, parameter-plus-field
result instantiation, last-field-at-zero and preservation of outer slots.
`Core.Verification` now uses that proved frame and exposes parameter-aware
result-parameter/index instantiation.

`Proof.LocalFrame` proves local declaration instantiation stable under
ambient renaming/substitution, using the essential preceding-binder scope
premise. `Proof.DependentSpine.Spines.Checked` requires scope, an actual kind
derivation and argument checking for every instantiated entry, threading
preceding values forward. It derives telescope scoping/arity and preserves
the judgment under the existing context-morphism/coherent-substitution laws.
For individually closed declarations it produces the ACTIVE flat spine
judgment; an example feeds an existing registered constructor rule.

`Proof.DependentSpineExamples` supplies `(A : Type0, x : A)` and
parameter-seeded witnesses, result vectors, caller-variable transport and
capture-avoidance under lambdas/nested branches. It rejects bad argument
types, forward references, wrong arities and an ill-kinded `Type2` entry.
A companion witness shows why the reverse adapter is not claimed: the old
flat rule can check an argument at Type2 without proving Type2 itself has
a kind. Scoping alone is not signature declaration validity.

Sixteen independent tests in `test/cure/core/dependent_frame_correspondence_test.exs`
kernel-check genuine dependent families, constructors and positive programs
before evaluation. They pin result indices, first/last/ambient slots,
captured fields under lambdas, parameter seeding and malformed inputs.
Primitive Atom avoids depending on the modern Int facade's builtin seeding.

**Migration boundary:** active branch typing, reduction and preservation now
use last-field-first order for exact-arity closed-entry fields (below).
The dependent judgment is not yet a constructor-admission rule or a
replacement `ClosedFragmentSig`. Incoming parameters still need their own
checking. Parameter-spine filtering, missing erased slots and full
Eval/NbE correspondence are not proved by the frame algebra or these tests.
### Active exact-arity closed-entry field order
`substArgs` reverses surface fields before simultaneous substitution.
`argsSub` remains an ALREADY de-Bruijn-ordered prefix helper, and local
declaration instantiation uses the unreversed prefix laws.
`Core.LocalFrame.fields-agree` now proves agreement directly with active
`substArgs` for arbitrary bodies.

`branch-context Γ tele = extendTele Γ (reverse tele)` puts the last field at
zero. `surface-field-vars` reconstructs constructors with fields in original
declaration order. Branch arity is the reversed length definitionally, with
`length-reverse` proving equality to ordinary arity. Renaming, substitution,
context conversion and preservation are migrated together with reduction.
`Proof.FieldOrder` reverses checked spines, closed entries and final terms.
Preservation's generic `contract-fields` replaces positional ordinary and
all four literal ι proofs by reversed-spine coherent substitution, restoring
the surface-order constructor after substitution.

Strict-parallel substitution/diamond/closure confluence, finality, literal
expansion simulation and the full reduction-conversion/soundness instances
remain checked. `Proof.FieldOrderExamples` uses heterogeneous
`Next(Nat, Bounded)` fields to check both slot types, reject the wrong slot
at Bounded, invoke actual ordinary/literal preservation, transport the case
under weakening and preserve a captured field beneath a lambda. The raw
confluence example separately distinguishes two Nat values.
This completes the exact-arity CLOSED-entry order migration, not dependent
constructor/data admission, parameter-spine filtering, missing erased slots,
η, erasure simulation or full evaluator refinement.

### Typed dependent declaration instantiation
`Proof.DependentInstantiation.Telescopes.Declared` records a forward-extended
local declaration context with preceding-binder scope and a checked kind for
every entry. It derives telescope scoping and the final context size.
`Arguments` checks actual arguments using the accumulated local prefix,
without repeating the entry-kind premises.

`Instantiation.instantiate` derives the existing `DependentSpine.Checked`
judgment AND a coherent substitution into the complete declaration context.
Its `coherent-push` lemma replaces one declaration binder by an actual term
without extending the caller context. Actual arguments must be `Final`:
checking-only holes do not in general infer their expected types. No value
or termination premise is required.

`result-frame` checks parameters first, then seeds field checking with their
reversed local frame. `instantiate-result⇒` and `instantiate-result⇐` transport
ANY locally typed term and its type through the parameter-plus-field frame.
These are typed substitution theorems, stronger than the earlier untyped
frame equalities, but they still use the existing closed-signature
preservation infrastructure.

`Proof.DependentInstantiationExamples` supplies `(A : Type0, x : A)`,
parameter/field result typing, two distinct Atom/Float parameters and fields,
computed-index typing/conversion, reducible actual parameters, closed/open
caller capture avoidance and checking-mode transport. It rejects swapped parameter frames, forward
references, bad arities and ill-kinded declarations even when argument
checking alone succeeds. A checking-only hole explicitly refutes automatic
argument finality.

The executable frame suite adds six kernel-checked regressions for distinct
parameters and field projections, dependent and computed result indices,
parameter uniformity and result-index typing. Those typed-frame theorems
alone do not validate complete result declarations; the following checkpoint
adds LOCAL uniformity, universe-bound and result-vector evidence.
Active constructor/data/branch rules and their soundness hypotheses have not
been broadened. Full dependent preservation and executable refinement remain
open; no runtime/library source changes are involved.

### Local dependent result declarations
`Proof.DependentResult.Results.LocalDeclaration` ties one family/constructor
to kind-checked parameter, index and field telescopes, scoped result vectors,
field-universe bounds, uniform result parameters and checked result spines.
`LevelsBelow` constrains the levels in the actual field-kind derivations;
raw `universe-ok`/`positive` booleans are not used to supply that evidence.
This is a local certificate shape, not global signature registration.

`ResultSpines` checks result parameters first, then dependent indices seeded
with those parameters; it derives both vector arities. `subst-result-spines`
transports the WHOLE judgment through a coherent substitution, including
dependencies between earlier and later indices. `uniform-instantiates`
proves the fresh parameter slots instantiate to the caller's supplied
parameters exactly, not merely up to conversion. `instantiate-results`
combines the typed parameter/field frame with these facts to produce checked
computed indices under those same actual parameters.

`Proof.DependentResultExamples` uses a local family
`D(A : Type0; x : A, B : Type0, y : B)`, distinct Atom/Float actual types,
computed result syntax and open caller variables. Missing/surplus indices,
wrong parameter/index types, and an undersized field budget are rejected.
A typed-but-swapped parameter vector fails the separate uniformity premise.
The concrete declaration witnesses and all transport laws are inhabited
over the existing soundness model, without adding axioms or changing it.

`active-result-kind` connects result spines to existing data formation ONLY
for registered families with individually closed parameter/index entries.
The examples exercise this adapter on registered Bounded and explicitly
refute its closedness premise for the genuinely dependent local family.
Consequently no dependent global constructor is silently admitted through
the old rules.

Sixteen independent tests in
`test/cure/core/dependent_result_correspondence_test.exs` kernel-check the
corresponding declarations and positive result types. They exercise whole
dependent/computed vectors, prior-index type dependencies, well-typed result
mismatch, exact result arity, universe bounds, non-uniform parameters and
out-of-frame references. No kernel/runtime implementation changes are made.
These local theorems still use the current closed-signature substitution
infrastructure. The next checkpoint connects them to a separate bounded
registry; unified dependent typing/preservation and refinement remain open.

### Base-checked dependent registry admission
`Proof.DependentRegistry.Layer base sig conv registry` keeps two environments
explicit. Declaration types and caller arguments are checked in `base`;
genuinely dependent records live in `registry`, not in the base signature
whose closed-entry hypothesis the existing substitution proof requires.

`Registry` attaches checked family and constructor declaration certificates
to actual `findFamily`/`findCtor` results. It also requires visible ownership
and fresh family/constructor identities relative to the base. Those guards
are proved policies of this bounded layer, not an assertion that every
executable registration path enforces these exact policies.

`Application` and `Formation` are explicit bounded admission judgments,
**not `Core.Typing._⊢_⇒_`**. They carry registry validity, real lookup
evidence and checked parameter/field or result spines. Actual arguments are
final. `result-formation` derives a checked registered result from an
admitted constructor application; `subst-formation` transports formation
through a coherent BASE caller substitution. No closedness or new
preservation oracle for the dependent registry is assumed.

`Proof.DependentRegistryExamples` registers both ordinary and computed
dependent constructors and exercises closed/open application, result
formation and caller substitution. Missing names/fields, bad indices,
base-name shadowing and inconsistent visible ownership are rejected.
The module REFUTES both `ClosedFragmentSig registry sig` and base typing of
the new data type, explicitly preventing a claim that the old soundness
theorem has been broadened.

The executable result suite adds lookup/visible-owner, missing registration
and same-shaped foreign-family rejection controls. It now has sixteen tests,
including the fixed-goal reduction checks below;
the separate frame suite retains sixteen. No kernel/runtime library source
changes. Recursive extension checking, positivity certification, dependent
elimination, unification of these judgments with full Core typing,
preservation/refinement and release certification remain open. In
particular, final actual arguments alone do not certify finality of every
declaration/result term.

### Fixed-goal registered constructor preservation
`Proof.DependentPreservation` proves operational preservation for constructor
congruence in the bounded registry layer. `arguments-preserve-at` preserves
dependent argument checking when ANY selected final field reduces. A changed
earlier field transports the tail's expected types by convertible local
prefixes, rather than falsely assuming those instantiated types are equal.
Argument finality is preserved as well.

`result-update-converts` proves the computed result data types convert across
the field update. `CheckedApplication` records a registered application at a
FIXED checking goal. `preserve-at` and `preserve-step` retain that SAME goal
for a field step and any small step from a constructor term; `preserve-star`
extends it to finite constructor reduction paths by checked input-path
recursion. Recomputing a different result type alone is not presented as
preservation.

`Proof.DependentPreservationExamples` reduces the type-valued `B` field in
`(x : A, B : Type0, y : B)`, so the later `y` goal really changes. Ordinary
and computed constructors, open callers, and a two-step type/value path
exercise the theorem. Raw result identity is refuted separately from
their positive conversion; nonconvertible replacement and wrong-family
controls reject spurious preservation.

Five executable regressions check source/intermediate/reduced terms at ONE
original, kernel-checked goal and independently evaluate their values.
The two correspondence suites now contain sixteen tests each.
No runtime/kernel implementation changes. This is not preservation for
dependent case elimination, recursive extension checking or the unified
`Core.Typing` judgment. Those integration and implementation-refinement
obligations, and release certification, remain open.

### Parameter-specialised selected-branch contraction
`Core.LocalFrame.specializeParameters` substitutes actual parameters beneath
the protected field binders. `Proof.LocalFrame.staged-contraction` proves
that this stage followed by active fields-only `substArgs` equals the full
parameter-plus-field `instantiateResult` for ARBITRARY bodies and open
caller terms. Nested binders use the existing capture-avoiding substitution
algebra. The pure push/weakening helper is shared with typed instantiation,
without changing its public theorem.

`Proof.DependentBranch.Contract` obtains the selected constructor's local
declaration from the checked registry. `contract-typed` transports a body
checked in that local parameter/field context to its fields-only contracted
form, at the instantiated local goal. `contract-final` preserves finality
for a final local body; `contract-infers` derives inference for that reduct.
`selected-step` exhibits the actual ordinary ι rule using the declared
FIELD arity, not the parameter-plus-field context size.

`Proof.DependentBranchExamples` checks last-field projection, parameter
replacement, lambda field capture/own-binder protection and open caller
parameters shifted past the fields then restored. Negative controls show
that unspecialised parameters become unrelated ambient variables, unprotected
specialisation can select a field value, and parameters cannot inflate
branch arity.

Ten tests in `test/cure/core/dependent_branch_correspondence_test.exs`
independently kernel-check whole positive cases and compare declaration-frame
evaluation with fields-only case evaluation. They include open parameters,
lambda capture, own variables and malformed slot/arity controls.
No kernel/runtime implementation changes.

**This is selected-branch typed substitution plus a raw ι witness, NOT
preservation of a typed whole source case.** The formal body is checked in
the local declaration context. The next checkpoint supplies typed fresh
caller contexts; motive/index agreement, coverage and integration with
unified typing remain open. Neither proves that elaboration emits the
specified specialisation.
Parameter-prefix filtering and missing erased slots remain outside the
exact-arity fields-only contract.

### Typed fresh caller branch contexts
`Proof.DependentOpening.build` extends the AMBIENT caller context forwards,
specialising each field type with the parameter substitution lifted through
preceding fresh fields. The context size is exactly caller size plus field
arity; parameters do not become additional branch binders.

`open-coherent` and `open-kinded` derive a coherent declaration-to-caller
embedding and actual field-kind witnesses from the registered local
declaration. `local-to-branch` types the earlier parameter-specialised body
in this fresh context. `close-coherent` proves a general closing law from
checked actual fields and an ambient context substitution.
`branch-coherent`, `contract-branch` and `contract-branch⇒` then close ANY
body typed in the fresh context, including direct unrelated ambient-variable
references absent from the local declaration context. Both the term and
its dependent type use active fields-only substitution.

The examples distinguish a literal first field from an ambient Atom caller
variable, protect that caller under a lambda, retain the lambda's own
binder, and embed/close open parameters and parameter-dependent lambdas.
Fresh dependent field types remain symbolic until closing.
Two added executable tests independently kernel-check whole cases returning
or capturing the unrelated ambient value. The branch suite now has ten
tests; the frame and result suites retain sixteen each.

This closes the fresh caller-context/contraction bridge, not the remaining
motive/index and coverage obligations or unified dependent case typing.
The base and registry environments remain explicit, with the same
conditional base substitution infrastructure. No kernel/runtime source
changes, full compiler refinement or new release/termination claim.

### Active rigid-head conversion and separate cumulativity
`Core.TypeHeads` records exposed type formers, including exact universe
levels and data family names. `Conversion.≈-heads` compares two such heads;
it never recovers raw syntax for an arbitrary convertible term.
`Proof.Inversion` accumulates conversion through inference/checking
derivations and extracts constructor/literal metadata without raw reflection.
All active progress/preservation consumers are migrated.

The old `≈-type` field is removed. `⇒-cumul` explicitly closes DECLARATIVE
inference under cumulative sorts; renaming, substitution, context conversion,
progress and preservation handle it. `check-infer` targets this declarative
closure, not executable synthesis. Unequal universe levels cannot convert.

`Proof.ConversionModel` inhabits every field using a total ζ-only
interpretation. It preserves rigid heads and proves rename/substitution
commutation with existing `funext`; it deliberately collapses all
constructors/literals to one opaque leaf and leaves applications
uninterpreted. It is not faithful value equality or an NbE implementation.
`Proof.ConversionExamples` exercises inference/checking conversion chains
through let-wrapped types, family metadata, a global with a let-wrapped
type, exact sorts, grades and distinct holes, and separate upward typing.
A well-typed β counterexample explicitly rejects full `ReduceConv` for
this witness. These are non-vacuous RECORD/typing examples, not a joint
preservation/soundness model. It is retained as historical bounded evidence;
the stronger reduction model below now supplies full β/ζ/ι/δ compatibility.

### Full formal reduction conversion and an inhabited soundness fragment
`Core.LiteralExpansion` expands compact Nat/Bounded literals into distinct
constructor towers without evaluating β/ζ/ι/δ or erasing/collapsing values.
It proves renaming/substitution commutation, scoping and closed global bodies,
and lookup/top/field-substitution identities.
`Proof.ExpansionSimulation` simulates EVERY existing reduction rule into
the expanded signature, including all four literal peels and all congruences.

`Proof.ReductionConversion.Model sig closed` compares expanded terms by a
common reduct. Checked confluence proves transitivity; rigid-head
preservation and Π-path decomposition prove head separation/component
injectivity. Structural term induction handles pointwise substitutions
without assuming uniformly bounded path lengths. Every `Conversion` field,
including compact-literal equations, is supplied. `reduce-converts`
inhabits full `ReduceConv` for the ORIGINAL signature. This is a relational
model, not a normalization algorithm or decision procedure.

`Proof.SoundnessModel` jointly inhabits positivity, local coverage,
`BuiltinCtors`, `ClosedFragmentSig`, body finality, `CertifiedTyped`,
`Conversion` and `ReduceConv`. It has registered Nat/Bounded families and
a finite nonempty global table whose declared type is let-wrapped, with a
checked kind. It invokes actual β/ζ/ι/δ preservation and the existing
constructive fuel theorem. These are now non-vacuous specification results,
not merely independently inhabited predicates.

The fixture's BuiltinCtors-compatible Bounded family is deliberately
**unindexed**. Full dependent signatures, filtered/erased frames,
indexed coverage omission, totality, erasure and evaluator/readback
refinement remain open. `Proof.ReductionConversionExamples` rejects
unequal Nat/Bounded/Int values, universe/grade/family confusion and distinct
holes. It explicitly refutes η between well-typed open functions in this model, so
full executable η conversion has NOT been covered.

### Structurally checked parallel spine lifting
`Core.Parallel` no longer uses any termination override. Its generic
`⇉*-at-spine` / `⇝*-at-spine` lifters carry source alignment separately
and recurse on an unchanged tail derivation; the six constructor/data spine
wrappers and the complete parallel-to-small-step simulation now pass Agda's
termination checker. The original statements are preserved.
`Proof.SpineLifting` exercises genuine two-step non-head updates, fixed
neighbours and opposite data spines, zero-step paths, symbolic alignment,
and conversion of a lifted parallel path to small steps. This proof layer
does not use the confluence theorem or any of the refuted typing hypotheses.
The hygiene guard forbids reinstating any parallel-module check bypass.

### Termination-checked specification confluence
The last `Proof.Confluence` override is removed. `Core.StrictParallel`
defines `_⇛_` with only one-step recursive premises, including branch bodies.
`Proof.StrictConfluence` proves one-step renaming/substitution and a strong
diamond with one joining step on each side. `Core.Relation` derives closure
confluence using strip/closure recursion on input paths, not generated joins.
The proved diamond supplies that generic theorem's parameter.

`Proof.Confluence.Conf.confluence` retains its original small-step statement
and `ClosedBody` hypothesis. Both simulations are checked; original
`ξ-case-brs` paths remain arbitrary finite paths and translate into
strict-parallel closure. No small-step rule was weakened, no termination
oracle was added, and the old wide-parallel relation is used only for its
checked simulation. The unchecked implementation and its obsolete helper
API are replaced by the strict laws, not retained as trusted derivations.
The wide-parallel `⇉-diamond`, `⇉-diamond-star` and `⇉-confluent` entry
points remain as checked consequences, with a compatibility regression.

`Proof.ConfluenceExamples` exercises β/ζ overlaps, argument duplication,
newly exposed branch redexes, distinct fields/non-head updates, literal peels
and malformed arities, recursive δ, and normal-form uniqueness.
The recursive signature makes explicit that closedness is not termination.
These are raw specification results, independent of typing/conversion.
Full filtered/erased-frame and NbE correspondence remain open.
The hygiene allowlist is empty: no bypass pragma is accepted anywhere.

### Inert effects
`Proof.EffectInert` proves one-step inversion and arbitrary finite-step
head preservation for `Effect`, `pure`, and `bind`, tracking child reductions.
It has no coverage, conversion, finality, or well-formed-signature premise and
is independent of the refuted legacy hypotheses. This closes inertness for
the present Core reduction specification, not BEAM effect execution.

### Open research questions (docs/SOUNDNESS.md §7, §8)
- **The totality certificate.** `Certified` means body finality, not
  termination. Verifier acceptance, call-extraction soundness, well-founded
  descent and the size-change principle must be linked to termination;
  finite certificate replay alone is insufficient.
- **Typed erasure simulation.** `Erase.erase` needs a source/runtime
  simulation accounting for filtered signatures, runtime binder maps and
  divergence; raw commutation is not the target (docs/SOUNDNESS.md §8.3).
- **η and proof irrelevance.** Cure's NbE DOES implement function η.
  Its soundness/refinement remains open. Proof erasure does not establish
  definitional proof irrelevance; no blanket rule is assumed.
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
proved; the morphism plumbing is the next step. (The simultaneous
substitution presentation removes the *adjoint-extension* half of this
tension — see the substitution section — leaving only the plain
binder-order bookkeeping.)

## The substitution lemma

Substitution is the algebraic heart of the β and ζ cases of Preservation.
Getting its *operation* right was the main finding of this slice.

The development uses a **single** substitution presentation: the
**simultaneous substitution** `substS : Sub → Term → Term` (`Core.Syntax`,
`Sub = ℕ → Term`), which replaces every free variable at once. The legacy
*targeted* substitution `substT` (replace one de Bruijn index) has been
**removed** — the whole development is now on the simultaneous presentation.

Targeted substitution is wrong twice over:

1. Substituting index 0 **shrinks the context**, so a variable at index
   `suc k` in `extend Γ A` must become index `k` in `Γ`.
2. A post-hoc `rename pred` would also renumber the substituted term `a`,
   which lives in `Γ` and must be inserted unchanged.

The simultaneous operation fixes both: the head substitution

    topSub a zero    = a
    topSub a (suc k) = tm-var k

inserts the substituted term as-is while every other variable is renumbered
down by one. Under a binder the substitution is extended by `extSub` (the new
binder maps to itself, everything else shifts).

With it, the `⇒-var` cases are clean:

- **index 0**: the term becomes `a`, and the type `A` is `0`-free (it is
  scoped in `Γ`, and the global convention keeps its free variables above
  the new binder), so `substTopT a A = A`. The goal is `Γ ⊢ a ⇐ A`.
- **index `suc k`**: the term becomes `tm-var k`, and the type
  `rename wk (lookup Γ k)` becomes `lookup Γ k`. The goal is
  `Γ ⊢ tm-var k ⇒ lookup Γ k`, which is `⇒-var k`.

The inductive obligations are all discharged: `subst-id`/`rename-id`,
`substS-scoped` (a `d`-scoped term is fixed by any substitution that fixes
the indices `< d`), `substS-closed` (a closed term is fixed by every
substitution), `rename-closed`, the `extSub`/`extSub^` laws, and the
substitution/renaming interaction `rename-subst` / `subst-rename`.

### The adjoint-extension obstruction, resolved

The one structural subtlety was the interaction between `extSub` and the
weakening renaming. The "substitution undoes weakening" law needs
`substS (topSub a) (rename wk T) ≡ T`, but under a binder `rename (ext wk)`
maps `suc j ↦ suc (suc j)` while `extSub (topSub a)` maps
`suc (suc j) ↦ suc j` — the two extensions are *adjoint*.

The obstruction **dissolves** once the substitution's binder extension is
taken relative to the renaming. For a simultaneous substitution `σ` and a
renaming `ρ`, the extension under a binder maps `zero ↦ var zero` and
`suc (ρ j) ↦ σ j`, so the general law

    substS (extSub ρ σ) (rename (ext ρ) t) ≡ substS σ t

holds by induction, and "undo weakening" is its instance at `ρ = wk`,
`σ = topSub a`. The `⇒-app` codomain instantiation is the same top
substitution `substTopT a c = substS (topSub a) c`, matching the kernel's
`Eval.apply_closure` — so the app case is exactly `rename-topSub` /
`subst-topSub`, with no `suc`-preservation obligation.

### Signature closedness

The current closedness lemmas (`rename-global-type`, `tele-closed`,
`rename-ctor-result`, `tele-closed-subst`, `subst-ctor-result`) are derived
from membership-indexed `ClosedFragmentSig ind sig`, not the refuted
arbitrary-record oracle. `rename-closed` / `substS-closed` apply only after
actual lookups justify the relevant family/constructor memberships.
This remains an explicit individually-closed-entry fragment; a dependent
telescope scoped under preceding binders is not automatically closed.

### The `ι` branch substitution, on the simultaneous presentation

The `ι` rule's field substitution (`Core.Reduction.substArgs`) is now one
simultaneous substitution `substS (argsSub (reverse args))` instead of the former
sequence of targeted `substT`s. This is not merely stylistic: the sequential
form could capture a field inserted under a binder when a later `substT`
re-scanned it, whereas one simultaneous substitution inserts every field at
once. The active substitution now matches the exact-arity fields-only
kernel frame `reverse fields ++ base_env`, with the last field at zero;
branch contexts, motive constructor variables and preservation are migrated
together. `argsSub` alone is an environment-prefix helper, not a surface-field
API. Dependent result instantiation, parameter filtering and missing erased
slots remain explicit implementation-correspondence obligations.

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
     Proof/Substitution.agda Proof/Context.agda \
     Proof/Progress.agda Proof/Preservation.agda Proof/FinalPreservation.agda \
     Proof/Soundness.agda
```

The library descriptor is `cure-core.agda-lib`. Interface files (`_build/`)
are git-ignored.

The maintained complete runner, including interface refutations, candidate
model examples, and effect inversion, is `./proof/check.sh` from the repository
root. Also run `./proof/scripts/check-postulates.sh`,
`python3 proof/scripts/test_hygiene.py`, and
`python3 proof/scripts/check-hygiene.py`. The last guard enforces an EMPTY
bypass allowlist, rejects new holes/unreviewed trust mechanisms, and does
not turn compilation success into an implementation-refinement proof.
All these checks run in `.github/workflows/proof.yml`.

## Relationship to the executable evidence

The written argument (docs/SOUNDNESS.md §9) maps each lemma to an executable
Antigen assay. This development is the *mechanised* counterpart: where Antigen
turns each lemma into a runnable, falsifiable claim, this development turns the
same lemmas into machine-checked theorems (or, for the open obligations, into
precisely stated goals). The two are complementary — Antigen can find
counterexamples but cannot establish the theorem; a mechanised proof can
establish the theorem but only for the calculus it formalises.

The assays complement derived lemmas, not an inventory of postulates:
`progress` is compared with `MetaCheck.progresses?/2`, `preservation` with
`MetaCheck.type_preserved?/2`, and `canonical-ctor` with the coverage assays.
`Certified` means only body finality and must not be identified with the
semantic termination obligations tested by `Antigen.Assays.Totality`.
