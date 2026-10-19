# Mechanised soundness proof for the Cure Core kernel

This directory holds the **deliverable B development**: an
[Agda](https://wiki.portal.chalmers.se/agda/) formalisation toward soundness
of the Cure Core kernel. It is the formal counterpart of the written argument in
[`../docs/SOUNDNESS.md`](../docs/SOUNDNESS.md), whose §7 scopes exactly this
development.

> **Status: foundation repair in progress.** The legacy full theorem interfaces
> cannot be jointly instantiated. `Proof.InterfaceAudit` machine-checks
> contradictions in global coverage, signature closedness, syntax-head
> reflection with reduction conversion. A fourth contradiction, global literal
> arities, is now retained only as a frozen negative regression: the active
> reduction rules carry local arity witnesses and `Conf` no longer assumes it.
> The existing derivations below are retained for repair, not certification.
> `Core.Verification` and `Proof.VerificationExamples` provide candidate local
> interfaces and concrete instances; the broad typing/proof migration has not
> happened. They are not an instance of the full soundness theorem.
>
> The following is the **historical derivation status**, subject to that
> applicability warning. The formalisation of the Core calculus and the typing
> judgment is complete and compiles clean. The canonical-form lemmas, the
> renaming and substitution lemmas, **Progress**, **`Final`-preservation**,
> and **`preservation` (every case, including ι and δ)** are all **proved**,
> and so are the constructive soundness theorems: the **fuel-indexed
> `soundness-fuel`** and the **coinductive `soundness-tree`**.
>
> The classical statement is `soundness-nf` in `Proof/SoundnessConfluence.agda`
> — the dichotomy **`Reached ⊎ DivergesNF`** over NORMAL FORMS, proved with
> **zero postulates**. The whole development now rests on exactly **two**
> named postulates: `funext` (standard function extensionality) and
> `tree-decides` (LPO on the outcome path). This inventory does not account
> for the refuted module hypotheses or the five existing `TERMINATING`
> pragmas in `Core.Parallel` (four) and `Proof.Confluence` (one).
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
| Coverage (§3.3) | `Covers` | `check_coverage` + `branch_unify` |
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
| `Core.Typing` | The bidirectional `infer`/`check` judgment `_⊢_⇒_` / `_⊢_⇐_`, over a length-indexed context with `Fin` lookup | ✅ complete |
| `Proof.Values` | The `Canonical`/`Neutral`/`Value` split (a value includes neutrals) | ✅ complete |
| `Proof.Inversion` | Head-inversion lemmas; conversion injectivity | ✅ `invert-pi`/`invert-data`/`invert-*-check` **proved**; `conv-injective-*` open |
| `Proof.CanonicalForms` | `canonical-pi-value`, `canonical-ctor` | ✅ **proved** (= `invert-*-check`) |
| `Proof.Substitution` | shift/subst algebraic laws | ✅ `shift-0`, `shift-var-1`, the rename/subst interaction laws, and the branch-field lemmas **proved**; only `shift-subst` (app case) open |
| `Proof.Context` | Length-indexed context laws: weakening lookup, `extendⁿ` lookup, branch morphism `extF` | ✅ **proved** |
| `Proof.Progress` | `Final` Core; the four side conditions; `progress` | ✅ **proved** |
| `Proof.Preservation` | `weaken`, `subst⇒`, `subst⇐`, `check-infer`, `preservation` | ✅ **fully proved** (all cases incl. β/ζ/ι/δ) |
| `Proof.FinalPreservation` | `substS-final` (closure of `Final` under a final substitution); `final-preservation` | ✅ **proved** |
| `Proof.Soundness` | `EvalResult`; `soundness-fuel` (constructive); `Diverges`/`EvalTree`/`soundness-tree` (coinductive); `tree-decides` (the only classical input) | ✅ **`soundness-fuel` and `soundness-tree` proved**; the classical `soundness` and its false postulate were **removed** (see `Proof.SoundnessConfluence`) |
| `Proof.Confluence` | Parallel reduction `⇉` (value-free); the substitution-commutation lemma `⇉-substS` (all cases), `p-rename`, the diamond `⇉-diamond`, and `confluence : _⇝_` | ✅ **complete** (`⇉-substS`, `⇉-diamond`, `confluence` all proved) |
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
- The bidirectional typing judgment, with every rule from
  `Cure.Core.Kernel`'s `infer`/`check`.
- **The canonical-form lemmas** `canonical-pi-value` and `canonical-ctor`
  (`Proof/CanonicalForms.agda`), proved by composing the checking-mode
  head-inversion lemmas.
- **The head-inversion lemmas** `invert-pi` / `invert-data`
  (`Proof/Inversion.agda`), proved by induction on the inference derivation:
  the only rule whose conclusion type is the target former is the matching
  introduction rule; every other rule is ruled out by the type index or by
  the head being neutral (`Canonical` excludes it). The `⇒-conv` case recurses
  via conversion injectivity. `invert-data` is stated as a three-way
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
  against a type INFERS it. This is the generalisation of `value-infer` that
  needs no value structure, and it dissolves the β/ζ inference-preservation
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

These are the `postulate`s, each with a named proof strategy in the source:

1. **`conv-injective-data` / `conv-injective-pi`** (`Proof/Inversion.agda`) —
   conversion injectivity on type constructors. *Strategy:* the FSCD'25
   result; provable in a meta-theory weaker than the object theory. These are
   now the ONLY inputs the head-inversion lemmas depend on (see below).
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
   **derived** from the single hypothesis `ClosedSig ind sig` (a `Scoped 0`
   predicate on signature entries) via `rename-closed` / `substS-closed` —
   no longer postulated.
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

The `progress` proof is not blocked on a design question — every input it
needs is now proved or present:

- **Canonical-form lemmas** (`canonical-pi-value` / `canonical-ctor`): turn a
  canonical Π/data value into a λ / constructor-like head, so β and ι fire.
- **`spine-length`** (`Core.Typing`) and **`brs-arity`** (`Proof.Progress`):
  match the ι branch's arity to the constructor's argument telescope.
- **`findBranch-complete`** (`Core.Reduction`): turns the coverage witness
  into the `findBranch c brs ≡ just (c , ar , b)` premise of ι.
- **The literal-peeling reduction rules** (`ι-nat-zero` / `ι-nat-suc` /
  `ι-bounded-zero` / `ι-bounded-suc` in `Core.Reduction`): a `case` on a
  compact `tm-nat_lit` / `tm-bounded_lit` scrutinee is NOT stuck — it peels
  one layer to `Z`/`S` / `First`/`Next`, exactly as the kernel's
  `Eval.nat_to_ctor_if` / `bounded_to_ctor_if` do. This closes the gap the
  `invert-data` finding exposed: without it, a well-typed case on a literal
  would be stuck.
- **Neutral terms are `Value`s** (the `inj₁` branch), so the elimination
  rules are never stuck; `⇒-var` is vacuous (`Fin 0` is empty).

`Covers` (`Proof.Progress`) is strengthened to yield a branch NAMED `c`
(not merely some branch in the list) — the honest reading of "a branch for
constructor `c`", and what `findBranch` needs.

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
guard, unreachable under `Covers` (so never produced). The "never stuck"
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
`p-β`/`p-ζ`. The whole development still type-checks green. The payoff is for
the confluence development (`docs/CONFLUENCE.md`): `_⇉_` is now **value-free**,
so its substitution-commutation lemma is the standard textbook proof with no
`substS-Value-or-redex` case analysis, and `p-rename` needs no
`Canonical`/`Neutral`/`Value` transport. **Do not re-introduce the side
conditions.**

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
- `Covers ind` and `BuiltinCtors ind` are incompatible.
- `ClosedSig ind sig` is uninhabited.
- Legacy `Conversion` and `ReduceConv sig conv` are incompatible.
- The frozen historical `LiteralArity` is uninhabited; it is no longer an
  active confluence parameter.

These are refutations, not additional axioms. Do not interpret successful
compilation of the legacy soundness/confluence modules as applicable proofs.

The local literal-arity repair is connected to the existing proof consumers:
small-step and parallel literal rules require arity witnesses, and progress
derives these from the actual checked branches and builtin constructor
telescopes. Renaming, substitution, finality, preservation, and confluence
are migrated. `Proof.LiteralCases` contains positive/negative rule tests
and a concrete confluence peak using only an inhabited `ClosedBody`
signature parameter. The existing termination overrides still need proofs.

`Core.Verification` defines local full-family coverage,
preceding-binder-scoped telescopes, and constraints on actual signature
members. It also defines executable-order field instantiation and
reduction-based Π/data exposure. `Proof.VerificationExamples` provides a
scoped dependent constructor, a nonempty scoped signature, missing/wrong-arity
rejection, empty-family coverage, distinguishable field substitutions,
result-index instantiation, and a let exposing a Π.
These establish inhabited predicates, **not declaration typing, a verified
conversion relation, or a repaired progress/preservation theorem**.

### Inert effects
`Proof.EffectInert` proves one-step inversion and arbitrary finite-step
head preservation for `Effect`, `pure`, and `bind`, tracking child reductions.
It has no coverage, conversion, finality, or well-formed-signature premise and
is independent of the refuted legacy hypotheses. This closes inertness for
the present Core reduction specification, not BEAM effect execution.

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

The former closedness *postulates* (`rename-global-type`, `tele-closed`,
`rename-ctor-result`, `tele-closed-subst`, `subst-ctor-result`) are now
**derived** from a single hypothesis `ClosedSig ind sig`: the signature's
globals, family telescopes, and constructor telescopes are `Scoped 0`
(closed). `rename-closed` / `substS-closed` turn that witness into the
identity facts the renaming and substitution lemmas consume.

### The `ι` branch substitution, on the simultaneous presentation

The `ι` rule's field substitution (`Core.Reduction.substArgs`) is now one
simultaneous substitution `substS (argsSub args)` instead of the former
sequence of targeted `substT`s. This is not merely stylistic: the sequential
form could capture a field inserted under a binder when a later `substT`
re-scanned it, whereas one simultaneous substitution inserts every field at
once — matching the kernel's single `eval(body, reverse fields ++ base_env)`.

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
`python3 proof/scripts/check-hygiene.py`. The last guard inventories the five
legacy termination bypasses rather than silently treating them as checked.
All these checks run in `.github/workflows/proof.yml`.

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
