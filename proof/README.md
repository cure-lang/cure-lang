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
> legacy consumers use
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
> compiles cleanly; its dependent-signature migration is not performed.
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

The separate native development now proves general dependent transport,
recursive preservation and closed final-term progress for
`Core.DependentTyping`. `Proof.DependentSoundness` combines them into
constructive fuel, finite-trace and guarded outcome-tree safety.
`Proof.DependentSoundnessModel` jointly inhabits the native assumptions with
dependent declarations, typed globals and real unindexed builtin layouts.
These remain specification results, not executable kernel refinement.

## Maintainer validation policy — 21 October 2026

At the maintainer's explicit request, Mix/ExUnit test verification,
documentation-snippet checks and stdlib/example verification are **not
required for this soundness-proof work or its checkpoint commits**.
Do not automatically run `mix test`, ExUnit suites, documentation checks or
the `mix check` stdlib/example gate unless the maintainer requests them.
Their omission is a deliberate validation-scope decision, not an unfinished
proof task or a claim that those suites passed. Earlier recorded test results
and cancellations remain historical evidence only.

Required local checks remain the complete Agda runner, exact postulate and
proof-hygiene guards, hygiene regression tests, applicable static analysis,
formatting and whitespace checks. The waiver changes no theorem assumptions,
trust roots, test selections/exclusions, performance thresholds, CI workflows
or existing release requirements. See
[`NEXT-STEPS.md`](NEXT-STEPS.md#validation-and-non-regression-requirements)
for the proof-validation commands.

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
| `Core.Value` | Historical indexed value shape; closure bodies are arbitrary unindexed terms | Not evaluator termination, representation adequacy or Eval/Quote refinement |
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
- The historical indexed value domain has smaller-index captured
  environments but arbitrary unindexed bodies. It adds no postulate or
  checking override; it does NOT prove evaluator recursion decreases or
  evaluation terminates. The checked fuelled closure model is described below.
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

Fourteen tests in `test/cure/core/dependent_branch_correspondence_test.exs`
independently kernel-check whole positive cases and compare declaration-frame
evaluation with fields-only case evaluation. They include open parameters,
lambda capture, own variables and malformed slot/arity controls.
No kernel/runtime implementation changes.

**This is selected-branch typed substitution plus a raw ι witness, NOT
preservation of a typed whole source case.** The formal body is checked in
the local declaration context. The next checkpoint supplies typed fresh
caller contexts; the curried goal agreement is supplied below, while motive
well-formedness, coverage and unified typing remain open. None proves that
elaboration emits the specified specialisation.
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
or capturing the unrelated ambient value. The branch suite reached ten
tests here and now has fourteen after the motive
checks below. The frame and result suites retain sixteen each.

This closes the fresh caller-context/contraction bridge. The following
checkpoint proves curried goal agreement, but motive well-formedness,
coverage and unified dependent case typing remain open.
The base and registry environments remain explicit, with the same
conditional base substitution infrastructure. No kernel/runtime source
changes, full compiler refinement or new release/termination claim.

### Curried motive/index goal agreement
`Proof.MotiveAgreement` models motive application to the constructor's
computed INDICES followed by its scrutinee value, matching the executable
curried contract. In the fresh branch, result indices are specialised under
protected fields, the motive is weakened over the field binders and the
constructor uses surface-order field variables.

`goal-agreement` proves that fields-only contraction gives EXACTLY the
actual motive goal with computed indices and the actual constructor spine.
It derives index-vector staging, restoration of the ambient motive and
surface-field substitution; no conversion oracle is assumed.
`contract-at-motive` combines that equality with fresh-context contraction
to type the selected reduct at this goal. A separate theorem exhibits ι.

The examples use `D(A; x:A, B:Type0, y:B)` eliminating to B. Ordinary and
computed indices, open caller parameters and alternate B values are checked.
The two resulting Float/Atom goals are proved nonconvertible, ruling out a
constant-motive shortcut.

Four executable tests independently kernel-check nonconstant B-dependent
motives, open parameters and a function result depending on B, and reject
using y/the scrutinee in the type-valued motive slot. The branch suite has
fourteen tests.

**This is goal-substitution agreement and selected-reduct typing, not
motive well-formedness or whole-source-case preservation.** The algebra
holds for raw motives; the executable's motive validation is still not
mechanised. The old `Core.Typing` case goal applies the motive only to the
scrutinee, so migrating it to this curried indexed contract remains open.
Coverage, unified typing and the other refinement/release obligations are
not discharged. No runtime/kernel implementation changes.

### Motive well-formedness boundary audit
`Proof.MotiveBoundaryAudit` shows why the old BASE judgment cannot serve as
a motive checker for the separate registry. A raw caller context may contain
a registry-only scrutinee type. The old case rule then derives a sort-valued
final empty case with vacuous base coverage. The actual registry admits
`LocalMk`, so empty coverage there is refuted; base coverage cannot be
transferred to it.

The registered constructor has no base inference derivation. Closing that
caller binder with the constructor therefore fails the base `Coherent`
premise, and the closed case has no base typing derivation. This does not
refute existing conditional preservation: it exposes exactly the missing
premise. A raw context extension is not evidence of a well-formed base type.

Three further executable tests pin registry coverage, unary-versus-indexed
motive validation, and the difference between fresh-value validation and
ordinary application typing. In the last test an Atom-annotated scrutinee
lambda passes case motive validation but cannot be ordinarily applied to
the data scrutinee. The positive whole case is kernel-checked and its value
is independently evaluated. The branch suite now has seventeen tests;
frame and result suites retain sixteen each.

The executable gate applies evaluated closures to fresh indices and a
scrutinee, then checks the resulting type value. A typed-Π motive contract
would be stricter, not a proved correspondence with that gate. A unified
typing migration must explicitly resolve or retain this refinement gap.
No unchecked motive certificate, closed-registry assumption, new typing
rule or kernel/runtime change is introduced by this audit.

### Native unified typing interfaces — review checkpoint
`Core.DependentTyping` is the replacement judgment under review, not a
migration of existing soundness consumers. Forward declarations, dependent
argument spines, constructor result instantiation, well-formed callers,
ordinary typed curried motives and fresh branch bodies all use ONE inductive
environment. Coverage uses that same environment. No closed-base typing,
`ClosedFragmentSig` premise or preservation callback certifies the new terms.
Signature validity checks actual lookups, ownership, native declaration kinds,
field universe bounds, uniform parameters, result vectors and global typings.
It is not a finite signature verifier or a positivity/termination proof.

`Proof.DependentTypingExamples` inhabits that validity for
`D(A; x:A, B:Type0, y:B)`, with ordinary and computed constructors, plus a
wrapper whose field AND index declarations use D. It types the constructors,
family formation, a B-dependent whole case and an open caller case natively.
`Admitted` bundles actual signature, context, scope and goal-kind witnesses.
The formerly unavailable constructor-closing premise is inhabited natively;
that fixture alone does not supply substitution. The general native
transport theorem described below now discharges that separate obligation.
The fixture has no globals or builtin identities; those validity clauses
are vacuous here, not a new inhabited builtin/global soundness instance.

`Proof.DependentTypingControls` rejects missing registration/fields, bad
kinds/scope, insufficient field universes, wrong dependent parameters/indices,
nonuniform results, missing/wrong-arity coverage and foreign-owner branches.
`Proof.DependentMotiveControls` rejects unary motives and the executable's
extensionally accepted misannotated motive under the stricter native contract.
Those proofs use `Proof.DependentTypingInversion`, whose generic inversions
are checked under a conversion parameter and exported as abstract proofs.
This prevents elaboration from unfolding the concrete reduction-conversion
model. No proof is replaced by a postulate or a checker bypass.

The original combined controls consumed all available memory during checking.
After splitting and abstracting the conversion-parametric inversions, the
three separate checks completed in about four seconds each, with GHC reporting
454–559 MiB total memory in use, under `+RTS -M24G -s -RTS`.
`check.sh` now caps every Agda process, including pre-flight probes, at a
24 GiB GHC heap by default; `AGDA_HEAP_LIMIT` overrides that budget.
This is a heap cap, NOT a hard process-RSS or total-allocation limit.
For diagnostics, run Agda with `--profile=definitions` and `+RTS -M24G -s -RTS`,
under `timeout --signal=TERM --kill-after=10s 120s` on Linux.

Validation of this interface checkpoint passed all 68 Agda modules without
warnings, the exact `funext`/`tree-decides` postulate guard, nine hygiene
scanner tests and the empty bypass inventory. The full default ExUnit replay
completed with seed 420051: 6,772 tests, zero failures and eight excluded, followed by
355 documentation snippets passed and zero failed. `VISUAL` was unset only
in the test subprocess. The replay took about twelve minutes; earlier
interrupted runs were not counted as successful validation.
Strict Credo, formatting, shell syntax and whitespace checks also pass.
No executable source or test selection/exclusions changed for this checkpoint.

Existing legacy soundness consumers remain on the old closed-entry theorem.
The later modules below supply general native transport, progress,
preservation and constructive soundness separately.
The typed motive contract is a conservative restriction, not refinement of
all executable fresh-value validation. Recursive validity/positivity,
indexed omission, eta/NbE, erased/filtered frames, erasure simulation and
semantic totality remain open. No kernel/runtime implementation changed.

### General native transport and conversion inversion
`Proof.DependentGeneralTransport` proves native inference/checking
renaming and coherent substitution, including nested cases in terms,
motives, branch bodies and well-formed fresh contexts. Images are native
inference derivations, without case-free support certificates. Context
conversion and fields-only branch contraction are derived from that
substitution theorem. Target callers carry actual native well-formedness.
`Proof.DependentScoping`, `Proof.DependentScopedAlgebra` and
`Proof.DependentContextSuffix` supply scope-aware frame/motive equalities
and structural traversal of the original context-kind derivations.

`Proof.DependentDataConversion` proves data-component injectivity for the
existing reduction-conversion model, separately from the legacy
`Conversion` record. `Proof.DependentConstructorInversion` accumulates
conversion through arbitrary inference/checking intermediates and exposes
the actual registered constructor, owning family and checked parameter/field
spines. `Proof.DependentSpineConversion` rebases convertible local prefixes
and computed result vectors. No raw syntax reflection or closed dependent
declaration premise is assumed.

`Proof.DependentGeneralIota` consequently preserves ordinary native whole
cases even when the constructor's hidden parameter witness and the case's
parameter witness are convertible but syntactically different, and the
selected body contains a nested case. `Proof.DependentCongruence` provides
all nineteen compositional congruence closures; the following theorem
derives their child endpoint typings recursively rather than assuming them.

### Recursive native preservation and literal compatibility
`Proof.DependentSubjectReduction.Preserve` proves inference/checking
preservation for the complete existing small-step reduction relation,
including all four compact-literal peels and every congruence. The checking
goal is fixed, not recomputed after reduction. The mutually checked
induction also handles selected dependent-spine updates, finite paths and
finite branch-body paths. `preservation-infers` recovers native inference
for the final reduct; `preservation-star⇐` preserves one checking goal
through an arbitrary supplied finite path.

Its explicit inputs are native `SignatureValid`, data-component inversion,
raw reduction-to-conversion compatibility, `BodiesFinal sig` and static
`BuiltinShapes ind`. Callers are natively well formed and source terms are
`Final`. `BodiesFinal` means global body finality, not semantic termination.
The data-component and reduction-conversion inputs are inhabited by the
existing specification model. No child preservation callback, new
postulate or check bypass supplies a recursive case.

The builtin-layout input is necessary. `Proof.DependentLiteralBoundaryAudit`
inhabits native validity, closed final source typing and coverage for an
unindexed Nat whose successor field is Float. Its real literal ι step
produces `nat_lit 0`, which cannot check at the source's Float goal.
Thus native declaration validity alone does not justify literal peeling.
`Proof.DependentPreservationControls` proves the new static layout contract
rejects this registered metadata.

`Proof.DependentLiteralPreservation` exposes static evidence for actual
builtin identities, family/constructor lookups, argument telescope shapes,
result indices and the Nat dependency used by Bounded peeling, and proves
literal preservation from those witnesses. This is not an executable
layout verifier. Its contract has no typing or preservation callback.
It permits ordinary field names and is conditional,
so builtin-free environments need not register these families.
`Proof.DependentLiteralExamples` inhabits it for real native Nat/Bounded
declarations. These are the explicitly unindexed literal families, not a
certificate for the executable indexed-Bounded interface.

The recursive examples invoke preservation on source derivations for
nested selected cases, lambda-body/domain changes, non-head field/index
updates, conversion/cumulativity wrappers, typed global unfolding and
multi-step branch-body paths. The following native soundness theorem now
combines this specification preservation with native progress. This is not
compiler/evaluator refinement. The old closed-entry soundness consumers,
native typing rules and reduction rules are unchanged.

`Proof.DependentSubjectReductionLiterals` invokes all three one-step
preservation entry points for each actual literal-peel rule, using source
literal inference with conversion chains. Field-sensitive cases return the
Nat predecessor, the Bounded predecessor or its distinct Nat bound, and
also exercise the zero/fallback branches. Target typings are obtained only
from the recursive theorem, not supplied as premises.

### Native progress and constructive soundness
`Proof.DependentCanonical` derives canonical function/data forms from
native inference and checking, accumulating arbitrary conversion
intermediates. Canonical functions at exposed Π types are lambdas;
canonical data values may be constructors or compact Nat/Bounded literals.
No arbitrary raw type is reflected back into exposed syntax.

`Proof.DependentProgress.Progress` proves closed final native terms are
either existing `Value`s or admit an actual small step. Source-local
coverage supplies constructor/literal branch names and exact arities.
This result needs no signature-validity, positivity, builtin-layout or
data-component premise. Signature validity, data components and builtin
layouts are separate preservation inputs.

`Proof.DependentSoundness.Specification` packages the explicit native
preservation inputs. `Sound.trace-safe` preserves native checking at one
fixed goal and finality along any supplied finite specification path, and
gives a value/step witness at its endpoint. `soundness-fuel` follows a
proof-producing observation policy and returns either a reached native
typed/final value with its source path or a typed/final prefix endpoint
when fuel is exhausted. Exhaustion does not imply divergence or that the
endpoint is not a value.

`soundness-tree` constructs a guarded coinductive outcome tree whose nodes
retain native typing and finality. `soundness-fuel≡truncate` proves its
finite truncations agree with the actual fuel-indexed construction.
Supplied positive infinite paths can be annotated by native typing through
`annotate-divergence`. No `tree-decides`, LPO or claim that divergence
excludes reachable values is used by these native constructions.

`Proof.DependentObservation` only produces actual raw value/step
witnesses. It checks first-match branch lookup and exact local arity; if
its partial policy cannot choose, native progress supplies the fallback.
It is not a type validator or an executable NbE implementation.
`Proof.DependentObservationExamples` exhibits a final ill-typed β redex
with a valid raw reduction but no native inference/checking derivation,
so observation success cannot replace source typing.

### Joint native model and outcome controls
`Proof.DependentSoundnessModel` uses ONE native environment, signature and
conversion model for `D(A; x:A, B:Type0, y:B)`, ordinary/computed
constructors, unindexed Nat/Bounded layouts and a nonempty typed global
table. The global body is a computed dependent constructor and its
declared type is let-wrapped. Every local declaration/global typing,
universe bound, uniformity, result spine, body-finality and layout witness
is native; the assumptions are jointly inhabited, not assembled from
different typing judgments.

Its Nat and Bounded programs each follow three actual reductions:
literal peeling, global unfolding inside the dependent case, and computed
constructor contraction. `Proof.DependentSoundnessExamples` invokes the
actual fuel/tree/trace theorems on these source derivations. Fuel zero
stops at the source, fuel three stops at an already-final Float value,
and fuel four observes that value as reached. Endpoint typings come from
soundness, not independent target checks. Fuel/tree agreement holds at
every budget.

`Proof.DependentSoundnessControls` deliberately admits a recursive raw
specification global to distinguish body finality from semantic
termination. Its supplied infinite path is natively typed and all fuel
budgets exhaust, while the global is also a neutral `Value` reachable in
zero steps. This refutes the tempting no-reachable-value strengthening.
An opaque typed global is reached immediately. This recursive fixture is
not an executable totality certificate.

Native safety is now integrated constructively. Kernel/NbE/η refinement,
the executable fresh-value motive gate, indexed-Bounded/coverage omission,
erased or filtered frames, erasure simulation, positivity/recursive
validity certification and semantic totality remain separate obligations.

### Canonical snapshot and conservative syntax boundary
`Core.CanonicalSnapshot` defines finite named tables, constructive unique-key
evidence, separate global types/optional visible bodies and a builtin-free
snapshot view. Family-table and flattened constructor-table lookup agreement
with the formal registry are DERIVED for arbitrary query names. Membership
implies successful lookup under uniqueness; successful lookup implies
membership. Visible constructor ownership is derived from family-key
uniqueness and actual lookup membership, and feeds the native validity fixture.
Duplicate inputs retain defined first-match lookup behavior but cannot supply
the snapshot's unique-key evidence.

`Core.AdmissionBoundary.Fragment` supplies a scoped, exact-key syntax
judgment for terms, branch bodies, caller types, forward-scoped declaration
telescopes, result vectors and global payloads. Branch arities match actual
registered constructor field counts. It derives `Scoped` and `Final`
structurally. The first grammar includes graded binders, applications,
ordinary data/cases/globals, Atom literals and Float/Binary type formers.
It excludes Int nodes, payload-free Float literals, all compact literals,
effects, holes and absurd terms, including nested occurrences.

`Eligible` SEPARATELY REQUIRES native `Admitted`, supported payloads, caller,
source and goal. Its typing projection is not a checker-soundness theorem:
syntax does not establish declaration kinds, goal kinds, typed motives,
coverage, subtyping or conversion soundness. Exact string identities are
opaque keys here; atom/string encoding, owner-name validation, Elixir map
extraction, alias resolution, opaque/quantity metadata, certification
visibility and semantic environment/frame correspondence are NOT proved.
The snapshot must not be used to silently drop those executable obligations.

`Proof.AdmissionBoundaryExamples` jointly inhabits these interfaces for
`Boundary#Packed(A : Type0)` and `Boundary#Pack(A, x : A)`, a nonempty typed
global table and a genuinely dependent motive returning A. The whole Atom-only
case is natively admitted at its original Atom goal; existing native progress
consumes its eligibility projections and an actual ordinary iota step returns
the payload. Missing/foreign/bare names, escaped caller/branch variables,
wrong branch arity and excluded syntax have negative controls.
`Proof.CanonicalSnapshotExamples` rejects duplicate family/constructor/global
keys, distinguishes first-match owners, and retains opaque global types
without exposing bodies.

Eleven tests in `test/cure/core/admission_boundary_audit_test.exs` independently
pin the corresponding dependent Atom fixture, canonical versus bare lookup,
declaration order, immutable snapshots, directional Any/List widening,
non-eliminable opaque families, graded effects, Float payload distinction and
fresh/let/branch frames. These are executable regressions, not a proof of
Elixir-to-Agda refinement. Native typing/reduction/conversion and executable
admission are unchanged. The next obligations are tracked in
[`NEXT-STEPS.md`](NEXT-STEPS.md); Stage 0's complete acceptance-rule ledger,
finite declaration checking and evaluator/readback refinement remain open.

### Bounded executable snapshot capture and metadata replay
`Cure.Core.ProofSnapshot` is an opt-in capture/render API, not an admission or
release gate. It inspects the entire supplied Core registry, checks exact
owner-qualified keys and key/name/owner/order consistency, and sorts family
and global keys while retaining constructor declaration order. Its initial
encoding is printable ASCII; quoted strings are escaped without creating
atoms. It rejects builtins, primitives, aliases, opaque families, externs,
unknown declaration metadata and erased/implicit constructor layouts.
Global layout metadata must be absent or explicit and unrestricted with the
right syntactic Pi arity. Every type, declaration vector and raw body is
scanned for scope and supported syntax, INCLUDING uncertified/hidden bodies.
This is intentionally narrower than ordinary executable acceptance.

`Core.ExecutableSnapshot` models the exported constructor/family/global
metadata, including raw bodies and separate certification/totality flags.
Its `check` returns a constructive `Dec (Accepted source)` after checking
layout restrictions and finite family/constructor/global key uniqueness.
Accepted input projects to `Core.CanonicalSnapshot.Snapshot`. Ordinary body
availability is gated by the certification flag; generic laws preserve
declared types and distinguish uncertified hidden bodies from certified
visible bodies. This concerns default certified-body availability, not
delta options, lazy normalization, fuel or evaluation strategy.
Neither certification semantics nor declaration typing is inferred.
The projected positivity and universe-check flags are FALSE, not fabricated
certificate booleans.

`proof/Fixtures/ExecutableSnapshot.agda` is exact data generated from
`Cure.Test.ProofSnapshotFixture`: one dependent family, two constructors
(including a computed result index) and four globals, with both visible and
hidden raw bodies. ExUnit kernel-checks its declarations/definitions and
regenerates this file byte-for-byte. `Proof.ExecutableSnapshotExamples`
independently runs the formal replay, derives lookup/ownership/visibility
consequences and supplies supported-payload evidence, including the hidden
raw dependent case. Rejection controls exercise duplicate tables, opaque
families, erased/implicit or malformed layouts, missing certified bodies,
inconsistent visibility and builtin registrations.

This is a concrete checked cross-language artifact, NOT a universal theorem
that Elixir capture/render implements the formal model. In particular,
formal metadata acceptance alone does not check canonical name encoding,
syntax support, declaration kinds, motive typing or coverage. Separate
controls deliberately allow capture of an ill-typed application and of a
low-level recursive certification CLAIM, preventing either capture or flags
from being mistaken for typing/termination proofs.

The new exporter suite and prior boundary/frame/result/branch suites passed
89 isolated pure-kernel tests (seed 938458) without the normal stdlib startup.
This is not a replacement claim for the default Mix/ExUnit documentation
alias or the separately cancelled stdlib/example gate. Those gates are not
required for this proof effort under the maintainer policy above; the default
test configuration and exclusions are unchanged.

### Acceptance-contract ledger for the first capture slice
- **Represented, not admitted by capture:** universes through Type2,
  scoped variables, all graded Pi/lambda/let binders, applications, ordinary
  data/constructors/cases/globals, Atom literals and Float/Binary type formers.
  Data/result vector lengths and exact fields-only branch/constructor arities
  are checked; kinding, uniformity and actual parameter/index types are not.
- **Names and environments:** direct canonical ASCII keys only; bare/import
  alias resolution, broader name encodings and general Elixir-to-formal
  snapshot correspondence remain outside the proof.
- **Checking-mode behavior still unproved:** expected-goal lambda checking,
  let-defined semantic values, parameter recovery in constructor checking,
  infer/check conversion and cumulative-sort fallback. Syntactic support
  must not be used as evidence of these rules' soundness.
- **Cases still unproved as executable admission:** fresh-value motive
  validation versus native typed motives, same-family branch ownership,
  full or refined coverage, impossible-branch omission and coherent branch
  substitution. The formal native `Admitted` requirement remains separate.
- **Excluded rather than equated with conversion:** builtin Any top checking,
  List covariance, compact Nat/Int/Bounded and Char literal rules, all effect
  formation/pure/bind paths, holes and absurd terms. An empty builtin registry
  prevents hidden builtin-dependent acceptance/folding from entering capture.
- **Runtime/normalization still unproved:** eta, builtin arithmetic,
  certified delta and semantic totality, filtered/erased frames, typed erasure,
  emission and BEAM behavior. Parameter-prefix constructor spellings are
  explicitly rejected even when executable checking accepts them.

This ledger covers current syntax categories and dispatch differences for
the capture slice, not a completed rule-by-rule admission derivation.
The constructive syntax/payload stage below discharges support replay,
and the finite native certificate stage derives validity/admission from
checked native proof objects. Algorithmic certificate production/replay and
its implementation-refinement relation remain next; fixture-only claims
cannot replace those proofs.

### Constructive syntax and complete raw payload replay
`Core.AdmissionReplay.Replay snapshot` decides the EXISTING formal
`Supported` judgment for arbitrary terms, term vectors and branches.
It also decides forward-scoped telescope support, family/constructor/global
payload support and finite caller support. Every positive decision carries
the actual support derivation; every negative decision refutes one.
Lookup failure and branch-layout inversion use the selected first-match
equations and injectivity, not assumed agreement. Mutual recursion passes
the ordinary Agda termination checker.

From complete projected-payload evidence, it derives supported/scoped
declared global types and supported/closed/final visible global bodies using
actual finite lookup membership. `BodiesFinal` is therefore obtained by a
theorem rather than an exporter-supplied callback. This remains body
FINALITY, not semantic totality or native global typing.

`Core.ExecutableReplay.Replay source metadata` is a second staged check,
parameterized by the actual metadata evidence from the first stage. It
decides both projected payload support AND support for every raw global
body, even when uncertified. Fixing the metadata evidence explicitly avoids
assuming proof irrelevance between different accepted-snapshot records.
Raw support, closedness and finality are also available by actual input
membership. The metadata-only checker remains deliberately separate.

`Proof.ExecutableSnapshotExamples` now obtains its generated fixture's
projected payloads and hidden-program support from this replay rather than
handwritten trees. Its derived visible-body closedness instantiates the
existing reduction-conversion model, with an actual global delta-conversion
example. Declared-goal closedness and visible/hidden body finality consume the
same checked finite payloads. Generated bytes and executable export behavior
are unchanged.

`Proof.AdmissionReplayControls.Hidden` proves for ANY raw term that an
uncertified projection can still pass projected-payload support; complete
replay nevertheless rejects hidden holes, absurd/effect terms and escaped
variables, including under erased binders. Visible-hole, forward-reference,
result/branch scope, missing-name and wrong-branch-arity controls exercise
rejection paths. Nested cases, lambda capture, dependent callers and valid
hidden lets exercise positive decisions.

Syntax replay is NOT a type checker or a theorem about Elixir capture.
Its existing grammar deliberately permits a represented ill-typed Atom
application, Type2, missing constructor arguments and uncovered/non-data
cases; controls retain those distinctions. Data/constructor vector lengths
and ASCII/canonical encoding checks can be stricter in the exporter than in
this formal grammar. Native declaration kinding, universe/uniformity bounds,
typed motives, coverage, conversion/NbE refinement, semantic certification
and whole-kernel admission remain unproved here. Native typing, reduction,
release policy and theorem assumptions are unchanged.

Both trust guards now discover ALL Agda source subdirectories under `proof/`,
including generated `Fixtures/`, rather than scanning only `Core/` and
`Proof/`. The exact two-name axiom inventory and empty bypass allowlist are
unchanged. A tenth hygiene test covers generated/future-directory discovery
and their rejection of postulates and termination overrides.

### Finite native certificates and exported-snapshot safety
`Core.NativeCertificate.Certificates` consumes one exported input, its actual
metadata/complete-payload replay evidence and conversion. Its finite
`Evidence` contains `All` proofs for each family declaration and every actual
constructor declaration, plus each raw global's kind and optional body
inference at its declared goal. Hidden raw definitions are included.
`SignatureValid`, arbitrary lookup-typing functions, preservation and
soundness callbacks are NOT certificate fields.

The module derives native `SignatureValid` by actual family/constructor lookup
membership, projected-to-raw global membership and finite proof lookup.
Ownership comes from canonical snapshot uniqueness; scoping comes from
complete replay. For any present raw body, it derives native `Admitted` and
representation `Eligible` at that body's EXACT declared type, with actual
goal kind, scope and caller evidence. This is a theorem about finite native
PROOF OBJECTS checked by Agda, not an algorithm that reconstructs them from
syntax or an executable checker returning success.

`Proof.NativeCertificateExamples` inhabits the interface over the EXACT
generated/replayed snapshot: the dependent Packed family, both ordinary and
computed-index constructors, four raw globals, a typed curried motive and
full same-family coverage. Its field-universe bounds, uniformity, result
spines and global kinds/body typings are native. The projected metadata
booleans remain false; no positivity or universe certificate is fabricated
from a flag. Validity and ordinary/hidden-body admission are obtained from
the general finite theorem rather than fixture-specific validity callbacks.

`Proof.NativeCertificateSafety` jointly instantiates native specification
soundness using that finite validity theorem, replay-derived body finality,
the existing reduction conversion/data-component model and the snapshot's
empty builtin registry. The exported dependent case and a computed-index
alternative each have an actual iota trace whose endpoint retains the
original Atom goal. A supplied certified-global delta trace is also safe.
Fuel zero stops at the source; fuel one exhausts at an already-final Atom
value; fuel two reaches it. Fuel/tree agreement holds at every budget.
Endpoint typings come from the safety theorem, not independent target checks.

`Proof.NativeCertificateControls` gives complete replayable inputs with NO
finite native certificate: an ill-kinded Type2 published type and a HIDDEN
Atom body declared at Float. Abstract conversion-parametric inversions prove
these failures. Missing constructor fields, omitted alternative coverage and
an undersized field-universe budget are rejected; finite evidence must also
contain the second constructor even when the ordinary source selects the
first one. Two executable regressions independently pin the computed case
and capture-versus-kernel failures. The focused isolated suite now has
91 passing tests with seed 938458.

This connects checked finite native evidence for a concrete exported artifact
to existing SPECIFICATION safety. It does not prove that Elixir capture or
kernel acceptance produces such evidence, define a complete serialized native
derivation protocol, validate semantic totality/positivity or refine NbE/eta,
erasure, emission or BEAM execution. Mix/ExUnit/docs and stdlib/example
verification are not required for this proof effort at the maintainer's
request; earlier cancellations are not passing results.
Native typing/reduction, executable capture and generated fixture bytes
are unchanged.

### Bounded data-only native recipe replay
`Core.SyntaxEquality` provides constructive `Dec (t ≡ u)` for the COMPLETE
current formal Core syntax. It preserves grades, exact universe levels,
names, signed literals, parameter/index partitioning and branch arities/bodies.
Equality is derived from decidable internal code equality and a proved
encode/decode retraction, without raw-head reflection or new axioms.
The auxiliary total decoder may default on malformed internal codes:
it is NOT an external decoder or validation boundary. Only equality of
actual encoded Terms is used. Structural equality is not conversion.

`Core.NativeRecipe.Recipe` and `Packet` are plain data: rule tags, child
recipes, constructor parameter witnesses, asserted types and cumulative
target levels. They contain no native derivations, conversion proofs,
lookup evidence or target-typing callbacks. The total replayer checks an
ACTUAL term/context and constructs native inference/checking/kind/spine
derivations on success. It verifies assertions by structural equality,
checks variable bounds and actual lookups, checks dependent spines with
the local-prefix frame, exposes only syntactic Pi/sort heads, and proves
the direction of explicit universe cumulativity.

Supported rules are sorts, variables, global references, Atom literals,
Atom/Float/Binary type formers, Pi/lambda/application/let and ordinary
parameter-seeded data/constructors. There is no case, effect, hole/absurd,
primitive Int or compact-literal rule, eta/NbE or non-reflexive conversion.
`Nothing` means the supplied recipe failed this bounded protocol; it is
NOT a refutation of all native typing. Relative inference success alone
also does not establish signature/caller validity, goal kinding, release
eligibility or termination.

The global adapter checks kind/body recipes against the ACTUAL entry type
and raw body, including hidden bodies. Missing or surplus body recipes
fail. Success yields the existing finite `GlobalEvidence`, not a claim
that a client-supplied annotation was correct.
`Proof.NativeRecipeExamples` computes native evidence for the exported
answer, held and packed globals, the local computed-index expression and
dependent Pi/lambda/let examples. At THIS stage the certificate was still
mixed: three replayed globals, manual family/constructor evidence and the
manual dependent-case proof, with a copied case packet failing. Later
sections replace both remaining halves with recipes, so the historical
mixed certificate is no longer what the composed theorem consumes.
A separate parameter-bearing Box registry exercises a genuine nonempty
constructor witness and rejects a Float seed for an Atom field; this is
relative native typing evidence, not an automatically certified registry.

`Proof.NativeRecipeControls` computes failures for forged types/kinds/grades,
bad indices, non-function applications, unknown names, missing/surplus
spine recipes, invented parameters, downcasts and dropped hidden bodies.
It proved that ANY recipe failed on a case node at THIS stage; after case
replay lands, the honest statement is that only a recipe CONTAINING an
`r-case` node can replay a case (the `NoCase` grammar in the same module). A beta-converted goal has an actual native
typing derivation but fails exact-syntax replay, while a typed eta expansion
remains structurally distinct from its neutral. Neither is silently promoted
to supported conversion.

This is a verified replayer for arbitrary values of a PROOF-FREE RECIPE AST,
not yet a byte/JSON parser, Elixir recipe producer, complete certificate
assembler or checker-acceptance refinement theorem. The following checkpoint
adds checked conversion evidence; dependent case/declaration recipes are still
required before claiming automatic replay of the complete exported
certificate. Existing exporter/fixture bytes, native rules and trust
inventories are unchanged.

### Checked non-reflexive conversion replay
`Core.NativeRecipe` replays CONVERSION. `ConvRecipe` is plain, proof-free data
whose constructors mirror exactly the laws of the abstract `Conversion` record
(`≈-refl`, `≈-sym`, `≈-trans`, the Π/application/data/constructor/effect
congruences and the compact-literal identifications) PLUS the premise-free β/ζ
rules and a δ rule whose only premise is a body lookup in the signature
supplied to the replayer. There is no asserted-conversion constructor, no
normalization or reduct oracle and NO η RULE, so a recipe can only NAME a
derivation the replayer reconstructs.

`Derive` therefore takes an explicit reduction witness
`reduce : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u` (inhabited by the
existing reduction-conversion model) and exposes
`conversion : (t u : Term) → ConvRecipe → Maybe (t ≈ u)`. Every success is a
checked `Conversion._≈_` derivation: `c-beta`/`c-zeta` additionally require
the asserted target to be the ACTUAL reduct, `c-delta` consumes the real body
equation, `c-trans` checks BOTH halves against its untrusted intermediate
term, and the compact-literal rules are the record's own identifications, not
a decision procedure. A wrong direction, a forged target, a mismatched grade
or family name, a spine-arity mismatch, a disconnected intermediate term and
an absent or non-visible body all fail.

`r-convert : Term → ConvRecipe → Recipe → Recipe` is an INFERENCE rule: it
replays a child in inference mode and reports the ASSERTED target only when
the recipe reconstructs a conversion from the type the child actually
synthesizes, emitting an `⇒-conv` node. The asserted target stays recipe data,
so `at` still compares it with the requested goal by exact syntax: a
well-justified conversion to a DIFFERENT type cannot be substituted for the
goal. `kind` consequently sees only asserted targets, so universe inflation
fails even when a genuine conversion exists.

`Proof.NativeRecipeExamples` replays a β-converted goal, a Π codomain redex
(conversion under a binder), a dependent computed result index (`(λ A → A) A`
versus `A`), a ζ/β transitivity chain, compact-literal identifications, a δ
goal against a local alias signature and kind discovery through a β-redex
declared type. `Proof.NativeRecipeControls` retains the exact-syntax failure
for the same β-converted goal and adds the rejections above plus both attempts
to manufacture η. At THIS stage the certificate was still mixed, with the
exported dependent case manual; the case-replay section below removes that
last manual proof.

### Replayed family and constructor declarations
`Core.NativeRecipe` also replays the DECLARATION evidence the finite
certificate needs. A `ConstructorRecipe` supplies one kind derivation per
parameter entry, one per field entry, and one per result-parameter/index
position; a `FamilyRecipe` adds one kind derivation per parameter/index entry
and one constructor recipe per constructor. The TELESCOPE itself is never
recipe data: it is read from the actual `Family`/`Ctor` declaration, and
recipes are consumed in declaration order, so a surplus or missing recipe
fails.

`declare`/`declare-below` rebuild `Declared` entries forwards, checking scope
with a decision procedure (`sc-var` needs `k < d`) and replaying each entry's
kind in the context accumulated so far. `declare-below` additionally checks
every field's universe level against the family's declared level.
`constructor-declaration` also checks the result vector's scope, the
`parameterSlots` uniformity equation and both result spines. `family-table`,
`constructors`, `definitions` and `certificate` assemble the finite evidence
in lockstep with the actual tables, so the resulting `Evidence` covers every
entry by construction.

`Proof.NativeRecipeExamples` replays the exported `Boundary#Packed` family and
both of its constructors (including the computed result index) plus the
parameter-bearing `Box` declaration, and the mixed certificate now takes its
whole FAMILY half from those recipes instead of the manual proof objects.
`Proof.NativeRecipeControls` rejects short field vectors, a non-kind field
derivation, surplus/missing constructor recipes, a wrong result-index recipe,
a field universe overflow and a non-uniform result-parameter vector.

This removes the manual declaration proofs from the exported certificate; the
dependent CASE is replayed by the next section. Scope is decided for the whole
current Core syntax, but the branch context is reconstructed through per-field
kind recipes (a typed-substitution derivation of specialised field kinds is a
separate theorem, not assumed).

### Replayed dependent case and the complete exported certificate
`Derive` also replays case ELIMINATION. `r-case` carries the scrutinee recipe,
both scrutinee spines, the motive LEVEL (asserted), a kind recipe for
`motiveType … level`, a motive recipe and one `(field kind recipes, body
recipe)` pair per branch, in branch order. The replayer derives:

- the scrutinee's inference, exposing a syntactic `tm-data` shape through a
  checked view (no reflected raw type is trusted);
- `WellFormed` of the ambient context, reconstructed for the EMPTY context
  only — a case under a binder is outside this bounded context;
- the family lookup and both parameter/index spines;
- `Motive`: scope decided, the motive type's sort replayed, and the motive
  inferred at that exact curried contract;
- `Branches`: for each branch, its constructor lookup, the owner-name check,
  the branch arity against the constructor's field count, a branch context
  REBUILT by `opened-fields` (each specialised field type re-scoped and
  re-kinded with a recipe), and the body checked at its `branchGoal`;
- `CaseCoverage`, replayed by ENUMERATING registered constructors of the
  selected family and matching branch arity, without requiring unrelated
  families' branches. A builtin-registered environment is outside this
  protocol (the snapshot has none), so no canonical builtin branches are
  guessed.

The `Branches` rule's `owner ≡ family` premise needs constructor/family name
uniqueness. `Derive` therefore takes an explicit `owner-visible` hypothesis,
which the canonical snapshot discharges through `Snapshot.owner-visible`;
`singleton-owner` discharges it for a one-family table. It is an interface
change, not an axiom.

Because a branch body is checked at `branchGoal` — the motive applied to the
specialised result indices and the surface constructor — each branch recipe
needs a CONVERSION recipe for that curried application. The exported fixture
needs two β steps for the ordinary constructor and three for the computed
index; the recipe names the interior redex, and `c-trans` checks both halves.

`Proof.NativeRecipeExamples` now replays the whole exported artifact: the
family, both constructors, all four globals — including the dependent case
whose synthesized type is proved EQUAL to the curried motive application at
the scrutinee's index and value — and every branch body, branch context and
local coverage. `certificate` assembles one `Evidence` value from those
recipes, `validity` derives the full signature validity from it, and the
fixed-goal safe trace is composed from the replayed certificate rather than
any manual proof object. `Proof.NativeRecipeControls` proves that ONLY a case
recipe can replay a case (a `NoCase` grammar rejects every wrapper of a
non-case recipe), and rejects a missing/surplus branch recipe, a wrong motive
recipe/level/kind, short field recipes, an unchecked branch body, a wrong
branch arity, an unknown branch constructor, real missing coverage, a
non-data scrutinee, a case under a binder and a well-justified conversion
smuggled in as the case's assertion.

Successful recipe replay constructs a native derivation for the represented
term; it is not a complete native type decision procedure or a theorem that
Elixir acceptance produces such a recipe. Semantic positivity, totality
certification, typed erasure and lowering are untouched. The character codec
and bounded producer are described below; snapshot/executable correspondence
and η/NbE refinement remain separate.

This is a replayable conversion-derivation language for the EXISTING abstract
`Conversion` record. It is not an NbE/readback refinement, a normalization
algorithm or decision procedure, and it has no byte/JSON parser or Elixir
producer at that checkpoint. η remains outside the record, so an η-only
conversion still fails the protocol, and the executable `Conv`'s η behaviour
is not covered. Case/declaration replay has since been implemented above;
serialization of those recipe layers has since been implemented below.
General representation fidelity and the kernel-acceptance-to-native-evidence
connection remain open. Native typing, reduction, executable source and
generated fixture bytes are unchanged.

### Wire-format core with a checked codec (first serialization increment)
`Core.Wire` fixes a SERIALISED FORMAT for certificate data and proves the
properties a decoder must have. A tree is flattened to a prefix-free
INSTRUCTION stream (`instructions`: `i-atom n`, `i-open`, `i-close`) and the
stream is decoded by a STACK MACHINE (`run`) whose recursion is structural on
the stream — no fuel, no termination override, no well-foundedness side
condition. `run-instructions` proves `run (instructions t) ≡ just t` for every
tree, so decoding inverts encoding.

The stream is then RENDERED to characters (unary naturals terminated by `;`,
`(` / `)` for list structure) and `render-injective` proves that a single
instruction's rendering determines the instruction, so the characters cannot
be read two ways; `Proof.WireExamples` fixes one worked example down to its
exact character string and records the rejections (`i-close` with an empty
stack, an unclosed list, trailing junk after the root, a nested unclosed
list).

NAMES ARE INTERNED, and this is a finding rather than a convenience: a
character-faithful `String` round-trip is NOT provable here. The standard
library provides only injectivity of `primStringToList`/`primStringFromList`;
the missing direction (`fromList∘toList`) exists solely as a `trustMe`
postulate in `Data.String.Unsafe`, which this development does not use. The
wire therefore carries a TABLE INDEX, exactly as the canonical snapshot
resolves owner-qualified keys against its registry: `index-of-sound` proves
that an index produced by interning reads back as the name that was written,
and a name absent from the table cannot be interned at all (`absent-name`).

The format is now EXECUTABLE END TO END for trees and terms. Scanning is a
FOLD over the character list — one character per step, structural recursion, no
fuel and no termination side condition — into an instruction stream, then the
stack machine decodes that stream. `scan-encode` proves that scanning the
rendering of ANY instruction stream returns it and `decode-encode` composes it
with the machine, so `decode (encode t) ≡ just t` for every tree: a
character-level decoder that provably inverts the encoder, with no postulate.

PAYLOADS travel as the EXISTING proved reflection: `Core.SyntaxEquality.Code`
already has `roundtrip : decode (encode t) ≡ t`, so this layer only has to
carry codes faithfully — tag and both naturals directly, children recursively,
and the NAME as a sound table index with `index-of-sound` supplying the
lookup. The INTERNAL retraction deliberately defaults on malformed codes,
so `wire-to-term` now additionally validates that re-encoding the decoded
candidate is EXACTLY the original code. `checked-term-exact` and
`wire-to-term-exact` expose that successful-acceptance property; unknown tags,
invalid universes/grades, missing/surplus children, incorrect marker nodes and
ignored attributes/names (including nested ones) cannot silently become
another valid term. Canonical holes/absurd remain syntax, not release
eligibility or native typing.
`code-fidelity`, `kids-fidelity`, `term-fidelity` and
`decode-term-fidelity` then give `term-to-wire`/`wire-to-term`/
`decode-term` their round-trips, so no new term-level argument is assumed.

`Proof.WireExamples` now covers both layers: the worked tree down to its exact
characters, an `atom-literals` term through the whole character pipeline
(`characters → tree → term`), and the rejections — garbage characters,
unterminated unary runs, garbage after an atom, an unclosed list, a closed
empty list (which IS a tree), trailing characters after the root, an absent
name that cannot be written, an out-of-range table index, a bare atom that is
not a code, and a truncated code payload.

### Wire format: the producer and the remaining ledger
`lib/cure/core/proof_wire.ex` (`Cure.Core.ProofWire`) is the PRODUCER side: it
reflects a Core term to the `Code` tree of `Core.SyntaxEquality`, interns names
against a caller-supplied table, and renders the resulting nodes to the
characters `Core.Wire` decodes. `test/cure/core/proof_wire_test.exs` pins
thirteen producer vectors (twelve pass on the first run; one expectation was
wrong and was corrected). The two sides share one hand-checked
CROSS-LANGUAGE VECTOR: for `tm-atom_lit "a"` under the table `["" , "a"]` both
emit `(1111111111111111111;1;;)`, asserted by `cross-characters` in
`Proof.WireExamples` and by the Elixir test. That vector is an artifact, not a
proof about the producer.

The producer is UNVERIFIED Elixir. Scope of the runs performed: one focused
file (`mix test test/cure/core/proof_wire_test.exs`), 13 tests, 0 failures,
after the session's `PATH` was pointed at the standalone Elixir/Erlang installs
(the inherited `PATH` resolved `mix` to an unrelated release boot file). The
default suite, documentation checks and the stdlib/example gate were NOT run;
the maintainer policy above still waives them, so their omission is not an
outstanding proof task and is not reported as a pass.

REMAINING LEDGER for this item — none of these is claimed:

- **Universal producer correspondence and automatic recipe production.**
  All current recipe/container layers have Agda codecs and an Elixir data
  producer, with a generated complete artifact described below. Recipes are
  still supplied explicitly; no kernel-acceptance instrumentation/search or
  theorem about arbitrary Elixir producer executions is established.
- **Representation fidelity of snapshots.** That an executable registry
  (`Env`) corresponds to a formal `Snapshot`/`Signature` — name identity,
  declaration order, first-match lookup, owner-qualified keys, context
  correspondence — is NOT proved. `Cure.Core.ProofSnapshot` is an executable
  audit with rejections, not a theorem about Elixir.
- **Kernel acceptance → checked evidence.** Recipe replay proves that a
  REPRESENTED input has a native derivation. It does not prove the converse
  direction (every `Kernel.check` acceptance yields a replayable certificate);
  that is the Stage 3 correspondence and remains open.
- **Float representation gap.** The formal `float_lit` has no payload.
  The Elixir producer now explicitly rejects actual Float payloads as
  unsupported, rather than erasing them, and rejects the malformed
  `{:float_lit}` placeholder. `hole`/`absurd` travel as canonical development
  syntax and remain outside release eligibility/replayed native inference.

### Validated wire boundaries and conversion recipes
Review of the existing codec found a distinction between round-trip fidelity
and safe decoder ACCEPTANCE: using the internal defaulting `Syntax.decode`
directly accepted malformed reflected codes. Canonical re-encoding validation
now closes that boundary while retaining all valid encoder/decoder fidelity.
Formal rejection controls include malformed nested terms and branch codes.
The opt-in producer additionally validates universe bounds, grades, names
and complete UTF-8 name tables, and returns structured errors for malformed
spines/codes. Supported atom/string interning and existing character vectors
are preserved. Additional ExUnit regressions were written but not run under
the maintainer policy; producer source compilation is a separate static check.
There is still no universal proof about the Elixir implementation.

Review also found that recipe coverage unnecessarily checked unrelated
families. It is now family-local, reconstructing the existing `CaseCoverage`
obligations from actual membership, owner-name and arity evidence. A
multi-family control accepts the selected family's complete branches while
rejecting genuinely missing branches for either family. Native typing and
reduction rules are unchanged; nonempty-ambient case reconstruction remains
outside the current protocol.

`Core.WireConversion` encodes/decodes EVERY current `ConvRecipe` constructor
with exact tags and payload arities. Transitivity terms use the canonical
term codec; delta names use sound table interning; recipe vectors preserve
their order and grouping. `fidelity`, `each-fidelity`, `character-fidelity`
and public `roundtrip` prove conditional encoder/decoder fidelity for
arbitrary recipes, without new axioms or check overrides. Unknown tags,
malformed children, invalid term payloads and absent/out-of-range names fail.

`WireConversion.Replay.checked` composes character decoding with the actual
conversion replayer and returns a checked conversion proof or failure.
`Proof.WireConversionExamples` exercises a character-encoded zeta/beta chain
and visible delta unfolding on the exported snapshot; it rejects hidden
delta bodies, a mismatched table and a well-formed but false conversion claim.
Parsing a recipe is not evidence that its conversion succeeds.

The ordinary Recipe, Packet and declaration codecs and their Elixir data
producer are now complete below. Snapshot/context representation fidelity,
kernel-acceptance correspondence, NbE/eta, semantic certification and compiler/runtime
refinement remain unproved; a concrete cross-language vector is not a
substitute for those theorems.
### Complete recipe and certificate character codecs
`Core.WireRecipe` covers every ordinary recipe, with exact tags/child counts,
strict universe atoms 0/1/2, canonical term payloads through `Core.Wire`,
conversions through `Core.WireConversion`, and ordered recipe/term vectors.
Nested cases carry seven fields and each branch is exactly a pair of a
field-kind vector and a body recipe. Mutually structural traversal proves
`fidelity`, `each-fidelity`, `branches-fidelity` and character `roundtrip`,
conditional only on successful encoding with the SAME supplied name table.
There is no defaulting level decoder, fuel, new axiom or checking override.

The ordinary tags are 0 leaf, 1 Pi, 2 lambda, 3 application, 4 let, 5 data,
6 constructor, 7 claim, 8 cumulativity, 9 conversion and 10 case. Tags in
conversion or term payloads are interpreted by their own codecs, not by the
ordinary recipe decoder. `Core.WireCertificate` adds 11 packet, 12 constructor
declaration, 13 family declaration and 14 whole-certificate envelope. Lists
remain ordered node lists; an absent packet body is an empty list and a
present body is a singleton list. Other optional-body shapes fail. Declaration
records carry only their existing recipe vectors; the envelope contains family
recipes and global packets, never source declarations, native proofs or
validity/lookup callbacks. Container and vector fidelity are proved generically.

`WireCertificate.Replay.checked` composes character decoding with
`NativeRecipe.Globals.certificate` against an actual accepted snapshot and
replayed payloads. Only successful SEMANTIC replay returns native evidence.
`Proof.WireCertificateExamples` serializes the complete exported fixture's
family, both constructors and four global packets, including the converted
dependent case. `certificate-from-characters` proves that the resulting native
certificate is exactly the character pipeline's result. Derived validity,
raw-body admission, eligibility and the fixed-goal safe trace consume that
certificate, not manually substituted declaration/global evidence.
Generic equality/status transport and opaque checked evidence avoid repeatedly
normalizing the full scanner and proof value during downstream type checking;
the decoder and native checker themselves are unchanged.

`Proof.WireRecipeExamples` pins every recipe shape (including nested cases,
nonempty parameter witnesses and all levels), an exact leaf character vector
and arbitrary-vector fidelity. Controls reject malformed tags/arity, levels,
term/conversion payloads, branch pairs, missing names and trailing characters.
Certificate controls separate parser rejection from well-formed data rejected
by actual replay: missing/surplus tables, swapped global/constructor/branch
order, missing branches and omitted hidden-body recipes. A changed name table
can still parse a canonical term, but a forged family claim fails actual
source-bound typing. Interning is not name-table authentication.

This completes the current Agda recipe/certificate CHARACTER layers, not a
universal snapshot/context representation theorem,
kernel-acceptance correspondence, eta/NbE refinement, semantic
positivity/totality or BEAM correspondence. The generated snapshot and native
typing/reduction rules are unchanged.
Validation for this continuation: all 135 registered Agda modules, the exact
`funext`/legacy `tree-decides` postulate inventory, ten Python hygiene
regressions, all-directory hygiene and shell syntax checks pass. No new holes
or check bypasses were introduced. Strict Credo reports no issues.
Maintainer-waived Mix/ExUnit, documentation and stdlib/example verification
were not run and are not reported as passing.

### Elixir recipe production and a generated complete artifact
`Cure.Core.ProofRecipe` produces all current conversion/ordinary recipe,
packet, constructor/family declaration and whole-certificate wire layers.
Its public `encode_conversion`, `encode_recipe`, `encode_packet`,
`encode_constructor`, `encode_family` and `encode_certificate` functions take
explicit data and a supplied name table. Exact atom/tuple constructors mirror
the Agda grammar; case branches are pairs, universe levels are integers
0/1/2, ordered vectors must be proper lists, and optional packet bodies use
`nil` or a present recipe. The whole UTF-8 atom/string name table is validated
before traversal; canonical term reflection/interning is reused from
`ProofWire`. Invalid payloads, callbacks, malformed/improper vectors, absent
names and unsupported Float payloads return structured errors, never proof
objects or default recipes. No atoms are minted.

`Cure.Test.ProofRecipeFixture` contains explicit annotations for the existing
dependent exported fixture. Asserted conversion terms are built from its
actual motive and constructor result indices; this is ONE annotated fixture,
not a certificate search algorithm or a hook into kernel checking.
`proof/scripts/generate-wire-certificate.exs` compiles the producer/fixture
sources and writes `Fixtures.ExecutableCertificate`: a name table and LITERAL
wire characters, rather than a call to the Agda encoder. It also audits that
the paired `Fixtures.ExecutableSnapshot` still matches its existing producer
byte-for-byte; it never rewrites that snapshot.

Regenerate with
`elixir -pa _build/test/lib/cure/ebin proof/scripts/generate-wire-certificate.exs`;
add `--check` for a read-only byte comparison. This uses an existing test-build
Core beam path, not Mix startup or ExUnit; it does not run kernel admission,
documentation checks or stdlib/example verification.
`Proof.ProducedCertificateExamples` independently checks exact character
equality with the complete Agda recipe certificate, its decoded data and the
equation that native replay returns the same checked evidence. Derived native
validity/admission, eligibility and fixed-goal safety therefore also hold for
the literal produced artifact.

`test/cure/core/proof_recipe_test.exs` records all constructor/container vectors,
malformed inputs, table/name errors, payload exclusions and artifact
reproduction controls. These ExUnit regressions are written but NOT executed
under the maintainer waiver; artifact generation/check and source compilation
are separate checks, not disguised test-suite passes.

The concrete generated-artifact bridge is now established. Universal
term/recipe producer and snapshot/context representation fidelity, automatic
kernel-acceptance-to-recipe production, native/executable conversion and motive
refinement, semantic certification, typed erasure and BEAM correspondence are
still open. Neither explicit annotations nor a replayed artifact proves those
directions, semantic termination or soundness of all executable acceptances.
Validation for the producer continuation: all 137 Agda modules, exact
postulate/hygiene guards, ten hygiene regressions, shell syntax and strict
Credo pass. Producer/fixture source compilation and the standalone byte
reproduction check pass, with no changes to the existing snapshot. No waived
executable/documentation/stdlib suites were run.
### Source-bound checked admission pipeline
`Core.CheckedAdmission.verify` takes only a represented
`ExecutableSnapshot.Input`, a name table and certificate characters. It
decodes the envelope, decides metadata/layout restrictions and unique keys,
checks complete projected payloads AND every raw hidden body, derives visible
body closedness, instantiates the existing reduction-compatible conversion
model and runs native certificate replay. No accepted-metadata proof, payload
proof, conversion model, reduction witness, validity proof or safety callback
is a caller input.

Success returns `Checked source table characters`. Its `decoded` and
`replayed` equations bind the envelope and native evidence to those exact
inputs; `character-result` proves the original character replayer returns that
evidence. Metadata/payload proof identities remain explicit, with no
proof-irrelevance axiom. Generic result/status transport avoids large
concrete proof-value rewriting without skipping any validation stage.
`Checked.valid` derives signature validity. `Checked.specification` also
derives data-component inversion, reduction compatibility, body finality and
the no-builtin shapes from existing constructive models, yielding native
finite-trace, fuel and guarded-tree safety.

`Bodies.admit` selects a raw definition by exact name using finite first-match
lookup, carrying actual source membership and name equations. It returns
native admission/eligibility at the original declared goal plus trace safety,
fuel results, a guarded outcome tree and fuel/tree agreement. Absent names
and absent bodies fail; a hidden raw body can be admitted without becoming
visible to delta reduction. Contexts here are CLOSED/empty native contexts,
not a semantic-environment or arbitrary-caller-context correspondence theorem.

`Proof.CheckedAdmissionExamples` sends the literal generated certificate
through the combined verifier and selects `Boundary#unpack` by name, deriving
its original Atom goal and safe dependent-case trace without manual lookup or
typing witnesses. It checks metadata/duplicate/layout failures, malformed
characters, missing evidence, unsupported hidden syntax and absent body/name
selection. Separate controls pin representation success for an ill-kinded
sort and an ill-typed body before native replay rejects them.
A certified recursive definition passes the bounded protocol and has a safe
self-loop: body finality and certification FLAGS still do not prove semantic
termination.

This composes all current represented-input checks into native admission and
specification safety for arbitrary successful inputs, not only the fixture.
It does NOT prove universal Elixir producer/extraction fidelity, kernel
acceptance implies recipe production, executable NbE/motive/context
refinement, semantic positivity/totality or compiler/runtime correspondence.
`Nothing` still means this protocol failed, not that native typing is
impossible. Native semantics and generated artifacts are unchanged.
Validation for this continuation: all 139 registered Agda modules pass;
the exact two-name postulate inventory, ten hygiene regressions and
all-directory hygiene remain unchanged. Artifact reproduction, shell syntax,
strict Credo covering all 1,414 source files, formatting and whitespace checks
pass. No maintainer-waived executable/documentation/stdlib suites were run.
### Complete source snapshot wire fidelity and character-only admission
`Core.WireCombinators` proves fidelity for exact products, vectors,
empty/singleton optionals, tag wrappers and record retractions.
`Core.WireSnapshot` uses them to encode/decode the ENTIRE formal
`ExecutableSnapshot.Input`: constructor names, telescope binder names/types,
result parameters/indices and layouts; family parameters/indices/level,
constructor order and opacity; global names/types, raw optional bodies,
optional quantity/explicitness vectors and BOTH certification flags; and
builtin name pairs. Record tags 15/16/17/18 carry right-nested two-child
products. Booleans, grades and levels use exact finite scalar decoders;
names use table indices and terms use canonical `Core.Wire` decoding.

Arbitrary successful snapshot encodings round-trip through nodes and
characters under the SAME supplied table. This is whole-record equality,
preserving every field, list order and absent-versus-present-empty option.
Parsing preserves semantically unsupported metadata, rather than filtering
it or turning flags into proofs; the existing admission checks still reject
unsupported layouts, opacity and builtins.

`Core.WireAdmission.verify` takes only a table, SOURCE characters and
CERTIFICATE characters. Its result stores the decoded source, the exact
source-decoding equation and the existing checked-admission result/equation.
Named raw-body admission and native trace/fuel/tree safety consume that
decoded source. `Pin` identifies a known source solely from equality of
actual decoder results, not a callback or proof-irrelevance assumption.
This removes the constructed-source argument from the character admission
boundary; it does not authenticate the caller's table or original registry.

`Cure.Core.ProofSnapshotWire` encodes the existing `ProofSnapshot.capture`
audit's bounded output, reusing term production and preserving all captured
metadata/raw bodies. It exposes no raw-map input and retains capture's
ASCII/canonical-identity, builtin, opacity, primitive and layout exclusions.
Those producer exclusions are narrower than the lossless FORMAL input codec.
`generate-wire-certificate.exs` now also generates/checks
`Fixtures.ExecutableBundle`, containing an extended table and literal source
and certificate character streams. The old source and certificate artifacts
remain byte-for-byte unchanged.

`Proof.WireSnapshotExamples` proves exact equality between the produced
source characters and the independently encoded complete formal input;
decoding recovers that whole input, with family/global projections and
metadata preserved. Both produced streams then pass character-only
admission, yielding original-goal named-body safety and retaining hidden raw
bodies without exposing them to delta. Additional controls preserve all
grades, optional layouts and builtin/opacity/certification metadata through
the codec, while rejecting them where required during admission. Malformed
scalars/products/optionals/tags/names/trailing characters, duplicate sources
and a changed source paired with the old certificate have rejection controls.
Producer regressions are recorded in `proof_snapshot_wire_test.exs` but
remain unrun under the maintainer waiver.

This discharges GENERAL FORMAL snapshot codec fidelity and establishes a
concrete complete source/certificate artifact bridge. It does not prove
universal Elixir map extraction/producer correspondence, semantic
context/environment fidelity, kernel acceptance implies recipe production,
NbE/motive refinement, semantic totality, typed erasure or BEAM correspondence.
Native rules, admission restrictions and the postulate inventory are unchanged.
Validation for this continuation: all 144 Agda modules pass, with the exact
`funext`/legacy `tree-decides` inventory, ten hygiene regressions and no new
holes or checking bypasses. Standalone producer compilation/artifact
reproduction, strict Credo over all 1,417 source files, formatting, shell
syntax and whitespace pass. The older two artifacts are unchanged; waived
Mix/ExUnit, documentation and stdlib/example suites were not run.
### Checked dependent caller frames and closing substitutions
`Core.CallerAdmission` adds data-only requests: a forward caller telescope,
per-entry kind recipes, closed actual argument TERMS and their recipes, an
open subject/expected goal and subject/goal-kind recipes. Against an already
verified source it reconstructs the native context and well-formedness,
checks representation/scope, exact dependent argument spines, goal kind and
subject typing. There is no caller-supplied lookup, well-formedness,
substitution, typing or safety callback.

The existing constructive frame theorem derives a coherent substitution:
the last declared argument is index zero. General native substitution
transports BOTH subject and expected goal into the empty context. The result
derives closed scoping, goal kind, native admission and finality, then trace,
fuel and guarded-tree safety plus fuel/tree agreement at that same
INSTANTIATED goal. It does not claim the original open goal is closed or
forget dependent substitutions in result indices.

`Core.WireCaller` gives the entire eight-field request an exact tag-19
right-nested-product codec, with node/character fidelity. Character replay
returns actual decode and native replay equations; equality-based pinning
relates its native evidence to a known request without manual proof
substitution. `ProofRecipe.encode_caller` renders the corresponding explicit
tuple grammar, validating tables, proper vectors, binder pairs and term
payloads. Production is data-only; semantic vector alignment and typing
remain replay obligations. The standalone generator also produces the new
literal `Fixtures.ExecutableCaller`, preserving all older artifacts.

`Proof.CallerAdmissionExamples` derives admission/safety for `(A : Type0,
x : A)` instantiated by Atom and a payload, a dependent constructor whose
result index becomes Atom, and an open let whose closed form has a safe
zeta step. The literal caller's native evidence is tied to its character
result against the previously verified literal source/certificate. Controls
reject missing/surplus kind/argument recipes, missing/surplus/reversed or
wrongly typed arguments, unsupported/escaped terms and ill-kinded/wrong goals,
including rejection after character decoding.

This is a CHECKED SYNTACTIC caller-frame bridge with closed actual terms,
not full correspondence for executable `Context` semantic types/environments.
`Context.extend` introduces fresh neutral levels; `extend_def` stores actual
values. Neither arbitrary semantic-value readback, let-environment refinement,
level/index conversion nor evaluation/quote/eta correctness is assumed or
proved by these requests. Nonempty-ambient case recipe reconstruction is
still unsupported and has a retained rejection control; an empty-caller
dependent case still succeeds. Native typing/reduction rules and existing
case protocol restrictions are unchanged. Producer ExUnit regressions are
recorded but remain unrun under the maintainer waiver.
Validation for this caller continuation: all 148 registered Agda modules pass;
the exact `funext`/legacy `tree-decides` inventory, ten hygiene regressions
and empty checking-bypass inventory are unchanged. Standalone producer
compilation/artifact reproduction, strict Credo covering all 1,419 source
files, formatting, shell syntax and whitespace checks pass. All older
artifacts are unchanged; maintainer-waived executable/docs/stdlib suites
were not run.
### Bounded semantic context/readback bridge
`Core.FlatContext` introduces a deliberately CLOSURE-FREE semantic model:
sorts, Atom type/literals and neutral variable levels. Partial readback
rejects out-of-scope levels; successful readback is scoped. General proofs
establish fresh-level readback and weakening, so unchanged semantic values
read back to globally weakened syntax as depth increases.
Length-indexed stores retain parallel types/grades/environments under a
fixed source signature. Opaque extension introduces a new neutral level;
defined extension stores its actual value and unrestricted grade.

The constructive build relation derives native context type readback and
pointwise lookup agreement. Materialized environments are proved to weaken
correctly: an opaque head reads back to variable zero, but a defined head
retains its actual term. Opaque-only environments are identity substitutions;
that theorem explicitly does NOT apply to lets.
`Core.FlatContextTyping` checks each added type's native kind and each defined
value's native type, derives context well-formedness, then checks every image
of the materialized environment as a native coherent substitution. No
context-typing or substitution callback is trusted. Its checked result ties
the native evidence to actual operation replay and supports general native
typing transport.

`Cure.Core.ProofContext` is a bounded observation audit of actual `Context`
and `Quote` calls, not native typing or semantic validity. It validates all
parallel lengths/grades, the full name table, the existing source-signature
audit and supported value shapes before readback. Escaped levels and
unsupported closures/applications/cases/data/effects/other primitives fail;
negative indices are not silently identified with natural zero. Readback
terms are rendered using the canonical term producer.

The new `Fixtures.ExecutableContext` is generated from actual opaque/defined
extensions, `Context.lookup`/`grade`/`env`/`length` and current `Quote.reify`
observations. It contains a dependent variable, dependent let alias,
Atom-valued let and later opaque binders, with all four grades retained.
`Proof.FlatContextExamples` proves exact model/observation agreement,
decodes actual readback characters, derives every native type lookup and
checks native coherence. Let aliases/literals transport at their expected
types; composing the SAME context with checked caller closing yields a safe
closed payload at the instantiated Atom goal.

A negative control distinguishes scope from semantic-frame coherence:
inventing a fresh neutral for an already defined slot passes construction
and kind checks but fails the native substitution image checker. Other
controls reject escaped levels, ill-kinded binders and ill-typed definitions.
Producer regressions are written but remain unrun under the maintainer
waiver. Older generated artifacts and native/Elixir kernel semantics are
unchanged.

This establishes GENERAL flat-model readback/frame laws and a concrete
actual Context/Quote artifact bridge. It does not prove universal Elixir
context extraction or even all executions of those four readback clauses,
closure evaluation/readback, eta, normalization, arbitrary semantic context
validity, quantitative usage/erasure or BEAM refinement. Preserving grades
is not a QTT usage theorem; scoped readback is not typing or evaluation.
Validation for this continuation: all 152 Agda modules pass, with the exact
`funext`/legacy `tree-decides` inventory, ten hygiene regressions and no new
holes or checking bypasses. Actual Context/Quote/capture source compilation,
artifact reproduction, strict Credo over all 1,422 source files, formatting,
shell syntax and whitespace checks pass. Older artifacts are unchanged;
maintainer-waived Mix/ExUnit, documentation and stdlib/example suites were
not run.
### Positive closure evaluation refinement
`Core.ClosureEval` adds finite closure/environment and neutral-spine data for
the actively evaluated Pi/lambda/variable/Atom/let/application/global slice.
Big-step evaluation/application evidence is constructed by the executor,
not supplied as an evaluation or normalization oracle. Every recursive
eval/apply call consumes HEIGHT fuel, including closure body application;
each sibling gets the same smaller height bound. This is not total-step,
native safety-policy or certified-delta fuel, and proves no unbounded
evaluator totality.

Outcomes distinguish exhausted, unsupported, unbound and non-function
failures. Raw Elixir's out-of-environment free-variable fallback is
deliberately outside the positive modeled slice. Let annotations are skipped,
domains/operands evaluated eagerly, and globals remain neutral as in
signature-free Eval. Captured bodies are syntax, not recursively evaluated
until forced; returning a closure is not validation of all its latent syntax.

`Proof.ClosureEvaluation` defines value/environment denotation with scoped
neutral levels; arbitrary captured syntax is preserved, not thereby scoped.
A closure denotes its captured syntax under a binder, NOT its fully
normalized quoted body. The proved beta/environment extension equation
handles capture avoidance; mutual evaluation/application simulation then
produces an actual finite native reduction trace for EVERY positive model
derivation under a represented environment and any signature. Flat-context
readback embeds into that environment relation. No preservation,
normalization, reduct or termination callback is a premise.
`Proof.ClosureEvaluationSafety` consumes checked caller admission and
positive model execution and derives a denoted result's native safe state
at the SAME closed expected goal. Its fuelled `run-safe` preserves model
failure/exhaustion instead of relabelling them as divergence or actual
Elixir exceptions.

The new literal `Fixtures.ExecutableClosure` records reviewed, terminating
calls to CURRENT Eval/Quote: beta, eager arguments/domains, captured and
higher-order closures, lets, Pi, neutral application and globals. Syntax and
captured bodies travel through canonical term characters/decoding.
The generator exposes no arbitrary submitted-program execution API and
preserves all earlier artifacts. `Proof.ClosureEvaluationExamples`
independently replays the observed values and captured environments, uses
the general trace theorem, and derives original-goal native safety for the
typed closed cases. A returned closure retains a beta redex in its denotation;
an additional explicit checked native step under its binder reaches the
observed quoted term. This is NOT a universal full-Quote theorem.

Controls reject wrong captures, missing variables, non-functions and
unsupported active forms. Finite-budget omega and unused-argument examples
pin eager evaluation without invoking unbounded Elixir on omega; another
specification path can reach a value despite model exhaustion. Exhaustion
is not divergence or a no-reachable-value theorem. An ignored hole annotation
has a raw evaluation trace but fails native admission, retaining the
evaluation-versus-typing distinction. ExUnit regression sources are recorded
but not executed under the maintainer waiver.

This proves GENERAL positive closure evaluation refinement for the explicit
MODEL and concrete implementation artifact agreement, not universal Elixir
execution/producer correspondence, full Quote/NbE/eta, certified delta,
data/case/builtin arithmetic, semantic totality, erasure or BEAM refinement.
Legacy `Core.Value` documentation has been corrected: its environment index
does not constrain arbitrary captured body syntax and never proved evaluator
termination. No legacy datatype, native rule or Elixir kernel semantics changed.
Validation for this continuation: all 157 Agda modules pass, with the exact
`funext`/legacy `tree-decides` inventory, ten hygiene regressions and no new
holes or checking bypasses. Current Eval/Quote and fixture source compilation,
artifact reproduction, strict Credo over all 1,424 source files, formatting,
shell syntax and whitespace checks pass. Older artifacts are unchanged;
maintainer-waived executable/docs/stdlib suites were not run.
### Scoped closure quotation and safe normalization
`Core.ClosureScope` adds recursive scope for semantic values, captured
environments and neutrals, INCLUDING each captured body's scope at
`length(env)+1`. Positive model evaluation/application preserves that scope;
semantic values remain unchanged when the ambient depth grows.
`Proof.ClosureWeakening` proves denotation weakening and the fresh-binder
opening/prefix equation using scoped substitution agreement. The body-scope
premise is essential: raw denotation alone preserves arbitrary syntax and
does not justify weakening unbound captured variables.

`Core.ClosureQuote` now has intrinsically certified, height-fuelled readback
for the existing closure slice. Like actual Quote, Pi/lambda readback first
evaluates the captured body under a fresh neutral, then quotes domain/body
at successive depths. Neutrals quote recursively, arguments included, and
escaped levels fail explicitly. Evaluation outcomes are otherwise preserved.
The combined model normalizer carries actual evaluation AND quotation
evidence; its budgets are height bounds, not unbounded termination proofs or
the executable Normalise engine's delta meter.

Every positive quotation produces scoped beta/zeta-normal syntax.
`Proof.ClosureQuotation` proves that positive quotation of a SCOPED semantic
value reduces from its captured-syntax denotation, using the existing
evaluation theorem under a weakened environment and the proved opening law.
Evaluation and quotation compose into a general positive normalization
trace. Normal-form evidence also proves native irreducibility under a
signature with no delta bodies. It does NOT imply irreducibility under an
arbitrary signature.
`ClosureQuotationSafety` consumes checked caller admission and derives
normalization safety at the SAME closed expected goal, without supplied
normalization, preservation or reduct callbacks. Its safe runner preserves
failure/exhaustion rather than interpreting them as ill-typing or divergence.

All older actual closure observations now replay through the new readback
model. A new literal `Fixtures.ExecutableQuotation` adds nested dependent
binders, normalization inside a Pi-valued domain, a neutral application
with a lambda argument, a global under a binder and an eta expansion.
Agda derives typed closed endpoints and open-environment traces via the
GENERAL quotation theorem, replacing the old captured-closure example's
manual extra step. A beta/zeta-normal result with a residual native delta
step and a retained eta expansion pin the two important non-claims.
Malformed capture, escaped level, small-budget and latent-omega controls
retain the difference between scoped evaluation, positive quotation and
unbounded normalization. Unbounded Elixir is never invoked on omega.

The standalone generator executes only reviewed terminating observations
and preserves all older artifacts. Producer ExUnit regressions are written
but remain unrun under the maintainer waiver. This completes general scoped
positive Quote/normalization refinement for the explicit MODEL plus concrete
implementation agreement, not universal Elixir execution/extraction,
whole-Cure NbE, eta/conversion, certified delta, data/case/builtin readback,
semantic totality, erasure or BEAM refinement. No native or Elixir kernel
semantics changed; the prior model evaluator's behavior is unchanged.
Validation for this continuation: all 164 Agda modules pass, with the exact
`funext`/legacy `tree-decides` inventory, ten hygiene regressions and no new
holes or checking bypasses. Current Eval/Quote/fixture compilation, complete
artifact reproduction, strict Credo over all 1,426 source files, formatting,
shell syntax and whitespace checks pass. Older artifacts are unchanged;
maintainer-waived executable/docs/stdlib suites were not run.
### Bounded normalization comparison and expected-goal admission
`Core.NormalFormComparison` normalizes both operands in the represented
environment and uses constructive syntax equality. Its three outcomes are
EQUAL (both executions to one common form), DISTINCT (two successful forms
with a structural inequality proof), and INCONCLUSIVE (side plus original
model failure). Exhaustion, unsupported forms and unbound inputs never become
a default false equality verdict. DISTINCT does NOT mean non-convertible:
eta, residual delta and broader executable comparison remain separate.

`Proof.NormalFormConversion` proves that equal results under scoped input
and environment relations have a common native reduct. Actual reduction
paths are expanded to derive the EXISTING source-specific native conversion
witness; no conversion/normalization oracle or new record law is added.
`Core.NormalizingAdmission` is an optional CLOSED checking protocol:
replay actual inference, validate representation and BOTH synthesized/target
type kinds, then use exact reflexivity or bounded normalized equality.
The result derives native admission and trace/fuel/tree safety at the
ORIGINAL expected goal, not its normal form. Mathematical conversion
certificates are opaque to avoid expensive source-module proof expansion;
inference, kind guards, normalization, comparison and rejection remain
computational. Sort cumulativity is not equality; explicit existing
cumulative recipes still work.

Exact reflexivity runs before model normalization, but AFTER kind/scope
guards, retaining reflexive data typing at zero normalization budget.
Non-exact data comparison can remain inconclusive. The protocol is not
complete native typing or a replacement release gate.
`Core.WireChecking` proves whole-request fidelity for tag 20's five fields
(subject, subject recipe, synthesized-kind recipe, goal, goal-kind recipe).
Character replay retains decode and native verifier-result equations and
preserves diagnostic rejections. `ProofRecipe.encode_checking` renders
data only; no conversion recipe is an input field.

The literal `Fixtures.ExecutableChecking` admits a payload at a beta-redex
type without an asserted conversion path. Under-binder/dependent Pi
examples derive conversion automatically. Wrong goals/kinds/grades,
escaped/forged syntax, insufficient budgets and unsupported comparisons
have explicit controls. The original expected goal survives safety and
budget/tree agreement.

The reviewed CURRENT Conv/Quote artifact in `ExecutableComparison` covers
beta/zeta, lambda/Pi bodies, names/levels/grades, eta, raw lambda domains,
certified delta and unsupported reflexive data. Actual Conv can accept
eta or raw lambda comparisons whose quoted domains differ; the latter has
no shared expected-type guard and is NOT labelled kernel unsoundness.
A distinct-quote residual-global pair is explicitly native-convertible
under delta, proving why a negative conversion claim would be false.
Unsupported reflexive data is inconclusive for the model comparator while
actual Conv and exact checking can succeed.

This discharges general positive MODEL comparison-to-conversion and
guarded expected-goal admission, not universal Elixir Conv/extraction,
eta/conversion completeness, certified-delta normalization, data/case/builtin
operational refinement or backend soundness. Only reviewed terminating
comparisons are executed for artifact generation; ExUnit regressions remain
unrun under the maintainer waiver. Native/Elixir semantics and older
artifacts are unchanged.
Validation for this comparison/checking continuation: all 172 Agda modules
pass, with the exact `funext`/legacy `tree-decides` inventory, ten hygiene
regressions and no new holes or checking bypasses. Current Conv/Normalise,
Eval/Quote and producer/fixture compilation, artifact reproduction, strict
Credo over all 1,429 source files, formatting, shell syntax and whitespace
checks pass. Older artifacts and kernel semantics are unchanged; waived
Mix/ExUnit, documentation and stdlib/example suites were not run.
### Bounded exact-arity constructor-case execution
`Core.ClosureCase` is a separate height-fuelled adapter for syntactically
constructor-headed cases. It evaluates surface-order fields with the existing
closure model, selects the actual first exact-name branch, checks its arity
against the complete field count, and evaluates its body under
`reverse(fields) ++ caller`. Motives and unused branches are not evaluated.
Exhaustion, unsupported heads, missing branches, arity mismatches and
field/body evaluator failures remain explicit MODEL outcomes. Budgets bound
height, not total work or executable fuel, and exhaustion is not divergence.

`Proof.ClosureCase` proves general positive execution refinement under a
denoting caller environment and an arbitrary native signature. Field
evaluation yields constructor congruence paths; the actual first-match
equation and checked length supply the existing native iota rule.
The multi-binder substitution/frame equation preserves arbitrary caller tails
and nested binders without a scope or typing oracle. Scope preservation is
proved separately from scoped fields, branches and semantic caller values.
Consequently scoped positive quotation reduces from the original case as
well, including closures capturing both field and outer-caller slots.
`ClosureCaseSafety` composes independently checked caller admission with
execution/readback into native safety at the SAME original closed goal.

The new literal `Fixtures.ExecutableCase` captures thirteen reviewed
terminating current Eval/Quote observations. Eleven exact-layout cases
replay independently: the existing genuinely dependent unpack, heterogeneous
first/last fields, outer and nested captures, zero fields, beta/zeta in fields
and body, duplicate first-match lookup, and unused branches/motive.
The other two observations record actual leading-parameter filtering and
missing-erased-slot padding: actual Eval returns a payload but this MODEL
rejects both with arity mismatch. This distinction is intentional.
Formal controls cover malformed first-match arities, absent/foreign names,
unbound and unsupported fields/bodies, non-functions, computed/neutral/compact
scrutinees, recursive case bodies and finite-budget eager omega. Unbounded
Elixir is never invoked on omega. Raw execution success can coexist with
failed native admission; it does not validate declarations, motives, finality
or coverage. ExUnit regression sources are written, not executed.

This is positive exact-case MODEL refinement plus concrete artifact
agreement, not universal Elixir correspondence or arbitrary data/case
normalization. Existing closure evaluation, normalized comparison/admission,
native reduction and executable kernel semantics are unchanged. Constructor
fields and selected bodies retain the original closure slice: recursive data,
arbitrary evaluated scrutinees, neutral eliminators, aliases, compact builtin
constructors/literals, filtered parameters and erased-slot relevance remain
separate obligations. Older generated artifact bytes are unchanged.
Validation for this continuation: all 177 Agda modules pass without warnings,
with the exact `funext`/legacy `tree-decides` inventory, ten hygiene regressions
and no new holes or checking bypasses. Standalone current-source artifact
generation/reproduction, strict Credo over all 1,431 source files, formatting,
shell syntax and whitespace checks pass. Maintainer-waived Mix/ExUnit,
documentation and stdlib/example suites were not run.
### Recursive ordinary constructor evaluation and quotation
The shared `Core.ClosureEval.Value` now includes recursive constructor
spines. Intrinsically certified `EvaluatesSpine`/`run-spine` evaluate fields
eagerly in surface order, with the same explicit model failures and
height-budget interpretation as function evaluation. The generic MODEL
constructs named spines; it does not infer declaration validity, arity,
compact-Bounded identity or executable admission from raw syntax.
The earlier constructor-unsupported control is consequently replaced by an
unsupported DATA-FAMILY control; all older actual artifact bytes stay fixed.

Scope preservation/raising, captured-environment denotation and scoped
weakening now recurse through constructor fields. `Proof.ClosureEvaluation`
derives native field congruence paths and general constructor evaluation
refinement for arbitrary signatures and denoting environments.
`Core.ClosureQuote` adds certified recursive spine quotation, scoped output
and constructor normality. General scoped quotation and normalization
refinement now include those values, and no-delta irreducibility descends
through the native element-indexed constructor rule. Readback normalizes
closure bodies inside fields, not just outer constructor nodes.
Existing checked-caller safety and positive comparison/conversion proofs
compose unchanged with this richer domain, preserving original goals.
Data-family comparison/admission diagnostics remain unchanged because data
nodes themselves are still unsupported by the evaluator.

The exact-case adapter now accepts constructor-valued fields and selected
bodies via the shared evaluator. It still does NOT evaluate arbitrary
scrutinees or recursive case bodies. `Fixtures.ExecutableConstructor`
records ten reviewed terminating actual observations: field beta/zeta,
nested constructors, closures in fields, captured constructor values,
constructors under binders, open neutral fields, residual globals, and
constructor-valued case fields/results. Agda independently replays all ten,
proves native paths, and derives unchanged-goal normalization safety for the
five independently admitted closed constructor/function programs.
Raw nested/case observations are not all claimed well typed.
Controls retain distinct constructor names/fields, missing-field admission
failure despite raw evaluation success, non-function application, eager and
latent omega exhaustion, unbound/unsupported fields and escaped/unscoped
nested captures. Actual unbounded Eval is never invoked on omega.

Two additional actual boundary observations remain separate: a RAW `First`
constructor compacts to a Bounded literal rather than the generic model
constructor, and indexed data readback with and without a signature produces
different parameter/index splits. The raw compaction input is not asserted
well typed and this is not labelled kernel unsoundness. Generic model
success is not an executable correspondence claim for compact constructors.
Data-family readback needs a checked signature/split relation before it can
join this positive refinement. Aliases, compact literal operations, neutral
and recursive cases, filtered/erased frames, eta/delta normalization,
universal Elixir/model correspondence and backend soundness remain open.
Native and executable kernel semantics are unchanged. New ExUnit regression
sources are recorded but remain unrun under the maintainer waiver.
Validation for this continuation: all 179 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, all ten hygiene
regressions pass, and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,433 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Evaluated exact-case scrutinees
`Core.ClosureCase` now also evaluates a case scrutinee in the existing shared
closure/constructor slice before dispatching on its semantic constructor.
Positive `computed` evidence retains the actual scrutinee evaluation,
first exact-name branch equation, complete SEMANTIC field count and selected
body evaluation under `reverse(fields) ++ caller`. Beta/zeta computations and
constructor-valued caller slots no longer require syntactic constructor heads.
The original direct-constructor path retains its prior diagnostics and budget
behavior. A checked direct-to-computed evidence bridge exposes the evaluated
route explicitly; it does not assert proof irrelevance, algorithm equality or
equal fuel behavior. A low-budget control demonstrates the budget distinction.

The general arbitrary-signature native simulation now composes scrutinee
reduction, exact iota and the existing simultaneous field/caller frame law.
Semantic field denotation supplies its actual length; scoped scrutinee
evaluation derives scoped field values rather than assuming them.
Existing scoped quotation and checked-caller safety then apply at the SAME
original expected goal. Failure outcomes now distinguish scrutinee evaluator
failure, neutral scrutinee and non-constructor result from missing branch,
wrong arity and body failure. Scrutinees are evaluated before branch lookup;
motives and unused branches remain unevaluated.

`Fixtures.ExecutableScrutinee` records ten reviewed terminating actual
observations for beta/zeta and eager scrutinees, caller variables/outer slots,
capture, nested fields, zero arity and unused payloads. All replay independently
with native reduction and scoped readback evidence. Three closed dependent
cases independently replay their native recipes and derive original-goal
safety. Their conversion recipe reconstructs its asserted middle term at the
NEW scrutinee syntax; an observed evaluation result is never used as typing.
Raw/open examples are not all asserted natively admitted.
Three additional actual observations retain neutral-case readback and
computed filtered/erased layouts that the exact adapter rejects. Formal
controls retain first-match arity, unbound/unsupported/non-function scrutinees,
body failure, neutral/non-constructor outcomes and separate scrutinee/body
omega exhaustion. Unbounded Elixir is never run on omega.

This extension is isolated in the adapter: `ClosureEval`, its normalizer and
normalized checking still reject case syntax. Case-containing scrutinees,
selected case bodies and cases under ordinary function evaluation remain
unsupported. Data-family splitting, neutral-case values/readback, compact
builtin behavior, aliases, filtered/erased relevance, universal Elixir/model
correspondence and semantic totality remain separate obligations.
Older generated artifact bytes and native/Elixir kernel semantics are
unchanged. New ExUnit regression sources remain unrun under the maintainer
waiver. The next operational integration must deliberately share recursive
case evaluation with closure application/readback rather than claim that this
adapter already evaluates arbitrary nested programs.
Validation for this continuation: all 181 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, all ten hygiene
regressions pass, and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,435 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; maintainer-waived suites were not run.
### Shared recursive exact-case evaluation and readback
`Core.ClosureEval` now recursively evaluates exact constructor cases within
scrutinees, selected bodies, applications, constructor fields and closure
bodies/domains. Positive `e-case` evidence carries scrutinee evaluation,
actual first exact-name branch lookup, semantic field arity and selected-body
evaluation under the reversed field prefix plus caller. Fuelled dispatch
consumes height budget and preserves missing-branch, arity, neutral and
non-constructor diagnostics. Motives and unused branches stay unevaluated.
Exhaustion remains a bounded MODEL outcome, not divergence or an Elixir
exception. Neutral-case values, aliases, compact literal peeling and
filtered/erased frames are not silently added.

`Proof.ClosureFrame` factors the existing simultaneous branch/caller algebra
below evaluation, avoiding a quotation/simulation import cycle.
`Proof.ClosureEvaluation` now proves GENERAL native simulation recursively
through case evidence; semantic field denotation derives the iota arity.
Shared scope preservation derives the selected body's scope from actual
first-match membership and the field/caller frame length.
The compatibility adapter has an explicit `to-shared` evidence bridge and
reuses shared scope, simulation and frame lemmas rather than maintaining
independent recursive proofs. Its direct/evaluated route bookkeeping remains;
equal fuel budgets or proof objects are not asserted.

Existing scoped quotation, normalization, no-delta irreducibility, checked
safety and positive comparison/conversion compose with the richer evaluator.
`Fixtures.ExecutableRecursiveCase` records ten fixed terminating actual
observations, all independently replayed: nested scrutinees/bodies,
applications/fields, cases under lambda readback, Pi-domain computation,
case-computed types, returned captures and an outer caller slot beneath two
field frames. Five independently replayed closed native programs instantiate
unchanged-goal normalization safety. Raw/open observations are not all
claimed natively admitted.

A payload now checks through `NormalizingAdmission` at a case-computed
expected type without an input iota-conversion path. Actual inference and
BOTH kind proofs replay first; bounded execution/readback then derives
conversion. Native safety and fuel/tree agreement retain the ORIGINAL case
goal, not its Atom normal form. Insufficient comparison budget still rejects.
The separate native recipe protocol still excludes nonempty-ambient case
replay; successful model execution under a binder does not remove that guard.

Former unsupported-recursive controls now pin positive execution and shared
normalization. Missing/wrong-first-arity cases, non-constructor/unsupported
inputs, unbound bodies, small budgets and nested omega retain negative
controls. Actual unbounded Eval never sees omega. A latent neutral-case
closure evaluates but MODEL readback stops explicitly; actual Quote preserves
its neutral case. This remains positive exact-case MODEL refinement plus
concrete implementation agreement, not universal Elixir/model correspondence,
whole-kernel admission, totality, data-family split fidelity, neutral-case
readback, certified delta/eta, relevance/erasure or BEAM refinement.
Older artifact bytes and native/Elixir kernel semantics are unchanged.
New ExUnit regression sources remain unrun under the maintainer waiver.
Validation for this recursive integration: all 184 Agda modules pass without
warnings, the exact `funext`/legacy `tree-decides` inventory is unchanged, all
ten hygiene regressions pass and all-directory hygiene finds no new holes or
checking bypasses. Standalone artifact reproduction, shell syntax, strict
Credo over all 1,437 source files, formatting and whitespace checks pass.
Older generated artifact bytes remain unchanged; waived suites were not run.
### Checked ambient contexts in native case replay
`Core.NativeRecipe` now carries optional, genuinely checked context
well-formedness through its mutual inference/kind/checking/spine workers.
Pi/lambda/let extension constructs a new context witness only from a prior
witness, an actual scope decision and the replayed domain kind. Motive and
branch replay retain this evidence; opened fields derive their extended
witnesses entry by entry, and nested branch bodies use that checked context.
Forward declarations retain prior checked entry kinds, including across
family parameter/index and constructor field/result replay boundaries.
No globally shifted raw context is unshifted or certified by its length.

The existing raw-context entry points remain conservative: a directly
supplied nonempty context has no automatically manufactured witness and
cannot replay a case merely because variable lookup works.
Internal checked-context entry points consume actual native proofs, not
new untrusted recipe/wire fields. `CallerAdmission` obtains those proofs
from its replayed declaration and uses them for BOTH subject and expected
goal replay. Caller arguments, support, kinds, ownership, exact branch
arity, typed curried motives and family-local coverage still check
independently. This broadens bounded replay, not the native typing rules
or executable checker semantics.

`Fixtures.ExecutableCaseContext` contains three existing-tag-19 requests:
a genuinely dependent case in `A : Type0, x : A`, a case under a checked
lambda, and cases nested inside checked branch contexts. Explicit producer
annotations are not automatic recipe search. Character fidelity and exact
verifier-result equations pin each request; native evidence is replayed,
not serialized. The SAME derived substitution closes the dependent subject
and its original A-goal, and all three actual terminating readback observations
replay through shared normalization into original-goal native safety and
fuel/tree agreement. Computational examples use direct data-verifier results;
wire-transported proofs are kept separate, without proof irrelevance.

Positive controls cover caller goal kinds and case types in a forward
telescope. Negative controls retain missing context evidence, raw context
inference, bad/escaped domain kinds, forged recipes, wrong goals/actuals,
missing declaration kinds, escaped scrutinees, missing coverage, wrong
field arity and missing/non-kind branch-field recipes. Old blanket
nonempty-ambient exclusions are now positive checked-context examples;
arbitrary raw nonempty contexts remain excluded. No recipe constructor,
wire schema/tag, native/kernel rule or older generated byte changes.
New ExUnit regression sources are written but remain unrun under the
maintainer waiver. Universal Elixir checker/producer correspondence,
neutral readback, data-family splitting, aliases/compact builtins,
filtered/erased relevance, semantic totality and backend soundness remain
separate obligations.
Validation for this continuation: all 186 Agda modules pass without warnings,
with the exact `funext`/legacy `tree-decides` inventory, ten hygiene regressions
and no new holes or checking bypasses. Standalone artifact reproduction,
shell syntax, strict Credo over all 1,439 source files, formatting and
whitespace checks pass. Older generated artifact bytes are unchanged;
maintainer-waived Mix/ExUnit, documentation and stdlib/example suites were
not run.
### Checked signature-aware data-spine readback
`Core.DataSpine` now models actual readback's clamped prefix split for
arbitrary finite lists. Signature-free and unknown-family modes put every
argument in parameters; successful exact family lookup selects its actual
parameter telescope length. All modes preserve concatenation. Canonical
source parameters/indices are recovered under the DECLARED parameter-count
equation, not from flattening alone. The separate fail-closed alignment
checker derives family lookup, complete parameter prefix, exact index count
and flattened-spine equations; fallback or alignment success is not typing.

`Core.DataReadback` checks that layout for a flattened list of existing
closure values, then independently quotes parameter/index fields at the
requested depth. Unknown families, missing parameters, surplus/short indices,
exhaustion and field readback failures remain explicit.
`Proof.DataReadback` proves GENERAL positive native data-head quotation and
field evaluation/readback simulation under denoting scoped environments.
The field relations are tied to the checked canonical split; no arbitrary
raw source split is assumed to survive flattening.
Native data congruence yields the finite path, and scoped field normality
gives data-head irreducibility under a no-delta signature.
Its checked-caller composition derives safety at the SAME original closed
goal from independent admission, exact source shape and positive field
executions, not from a typing or normalization callback.

The independent `Fixtures.ExecutableDataSpine` snapshot/certificate has one
parameter and one genuinely dependent index. Its finite declaration and
native signature validity replay independently. Ten fixed terminating actual
Eval/Quote observations cover canonical data, parameter/index redexes,
closure fields, an open neutral field, short/surplus spines, unknown family,
forged source split and ill-typed index. Five positive checked readbacks
replay; four closed programs independently replay native admission and
derive original-universe-goal safety. Ordinary fallback/clamped observations
also agree with the explicit split model.

Controls retain the critical distinctions: signature-free readback changes
the canonical split; an unknown family falls back but fails checked alignment;
ordinary Quote accepts truncated/surplus spines while checked alignment
rejects them. A forged raw source split flattens to the SAME values as a valid
one and is repaired by actual readback, but fails native source kind replay.
Correct counts and successful field quote can still accompany an ill-typed
index, which independently fails native replay. Scoped open fields work;
escaped levels and insufficient budgets fail without an unbounded call.

This completes finite split/canonical-layout and positive TOP-LEVEL data-head
readback MODEL laws plus concrete artifact agreement, not universal Elixir
execution/extraction or recursively integrated data normalization.
`ClosureEval`, shared quotation/normalization and normalized admission
continue to exclude data-family nodes; no trusted source split is added to
their semantic values. Recursive data-valued closures, neutral-case readback,
aliases/compact builtins, filtered/erased relevance, eta/delta normalization,
semantic totality and backend correspondence remain separate.
Native/Elixir semantics and older artifact bytes are unchanged. New ExUnit
regression sources are written but remain unrun under the maintainer waiver.
Validation for this continuation: all 191 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,441 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Checked recursive data evaluation and quotation
Shared closure values now represent data with canonical parameter/index
spines, related to actual flattened values using one explicit finite registry.
This annotation is NOT a trusted raw source split:
`DataSpine.check-source` verifies actual family lookup and BOTH source counts
before signature-aware evaluation constructs it. Readback re-checks both
semantic spine counts before quoting. Positive spine evaluation/quotation
prove count and canonical-split preservation, rather than assuming it from
the flattened total length.

`ClosureEval` and `ClosureQuote` now expose signature-aware entry points,
threading the SAME registry through all recursive calls, applications,
constructor/case fields, captured closure evaluation and fresh-binder quote.
Source/value unknown families and malformed split annotations fail explicitly.
These guards are intentionally stricter than ordinary actual Quote fallback
on malformed inputs. Existing signature-free entry points and standalone
comparison retain data exclusion; actual signature-free Quote's flat fallback
is not assigned a native reduction path.

General intrinsic evaluation/quotation relations, semantic scope/raising,
denotation and scoped weakening now include data. Arbitrary-signature native
evaluation and quotation simulation reduce parameter/index fields separately,
and normal data spines are irreducible under a no-delta signature. Existing
checked normalization safety composes at unchanged goals; a new safe runner
uses the checked source's registry. The older top-level data readback
compatibility layer reuses shared field proofs.

Normalized admission now compares with its CHECKED snapshot registry after
actual inference and BOTH inferred/expected kind guards. The former
non-exact-data inconclusive case now admits, while signature-free comparison
of the same terms stays inconclusive. Exact zero-budget reflexivity and
explicit cumulativity behavior are unchanged. Distinct successful forms
still do not imply non-conversion.
`Fixtures.ExecutableRecursiveData` records ten reviewed terminating actual
observations, including nested data, data-domain/body closures, captured data,
applications, Pi types, constructor/case results and open fields. All replay
with the signature-aware model; six independently admitted closed programs
derive original-goal normalization safety. Raw nested/Box observations are
explicitly not all asserted typed or registered.

An existing-tag checking request admits a data-domain identity at a
beta-expanded expected Pi type, without a supplied conversion path. Character
fidelity, inference/kinds, positive normalization and original expected-goal
safety/fuel-tree agreement all check. The checker request uses the original
checked registry's table; the observation-only raw Box name is separate.
Forged source AND semantic splits, unknown/changed registries, wrong index
counts, escaped levels and small budgets have negative controls; correct
layout still does not imply native typing.

This is bounded positive recursive data MODEL integration plus concrete
implementation agreement, not universal producer/Elixir refinement or full
NbE. Registry consistency is an explicit contract. Ordinary fallback, aliases,
compact builtins, neutral-case readback, filtered/erased relevance,
eta/certified-delta normalization, semantic totality and backend refinement
remain separate. Native/Elixir semantics and older artifact bytes are
unchanged. New ExUnit regression sources remain unrun under the maintainer
waiver.
Validation for this integration: all 193 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,443 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Scoped fresh branch opening and residual normality audit
`Core.BranchOpening` now models fresh branch frames independently of shared
quotation: declaration-order levels ascend from the caller depth, and the
reversed prefix places the LAST field at zero before the untouched caller
environment. Zero arity adds no slot. A general proof relates the recursive
prefix to ascending enumeration/reversal and `arity + depth` to actual
`depth + arity`. Bounded execution wrappers reuse the existing evaluator,
including explicit signature-aware mode; height fuel is not a total-work
bound on constructing an arbitrary finite frame.

`Proof.BranchOpening` derives arbitrary-arity environment scope and
denotation by iterating scoped semantic weakening and fresh-neutral
readback. The simultaneous substitution/opening equation protects every
field binder and weakens caller images consistently, INCLUDING beneath
nested binders. It requires actual captured-body scope: equality on
arbitrary raw out-of-frame variables would be false. General positive
shared normalization then yields a native branch-body readback path from
the captured substitution under all field binders, for arbitrary signatures.
An explicit arithmetic transport also states the theorem at executable
`depth + arity`. No field typing, arbitrary weakening or normalization
oracle is assumed.

`Fixtures.ExecutableBranchOpening` records eleven reviewed terminating actual
`Eval.open_branch` observations. A fixed identity-lambda probe exposes the
ACTUAL captured frame independently of the tested body result. Frames,
evaluation and signature-aware readback independently replay for zero/one/
multiple fields, nonzero caller depth, first/last/outer variables,
beta/zeta, captured lambdas/data, spines and nested case bodies. Native paths
follow from the general opening theorem, not manually supplied reducts.
Wrong order/arity, empty-frame lookup, out-of-frame substitution,
unscoped caller values, signature-free data and bounded omega retain controls.
Actual unbounded Eval never sees omega.

The residual-case audit records an important prerequisite for full neutral
readback. `Core.Reduction.ξ-case-brs` accepts REFLEXIVE branch paths, hence
EVERY case has a native administrative self-step, even with a no-delta
signature. A residual neutral case is also an existing native `Value`.
Constructive controls therefore refute a proposed strict no-step theorem
for residual cases and reject labelling them with the existing strict normal
grammar. This is not kernel unsoundness, divergence or computational change.
Existing native rules and strict no-delta normality results are unchanged.
A future residual normality contract must distinguish genuine change from
administrative self-steps; it cannot silently extend strict irreducibility.

This supplies scoped multi-binder opening/readback prerequisites, not full
neutral-case semantic values/readback, typed fresh field telescopes, native
admission from raw opening success, universal Elixir correspondence or
relevance/backend soundness. Older artifact bytes and native/Elixir semantics
are unchanged; new ExUnit regression sources remain unrun under the
maintainer waiver.
Validation for this continuation: all 197 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,445 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Residual forms modulo administrative native reduction
`Core.ResidualNormal` adds an INDEPENDENT signature-relative residual-form
grammar and total proof-producing syntax checker for the supported
function/data/constructor/Atom slice. Cases require neutral scrutinees and
normal motives/branch bodies; globals require the ACTUAL native body's
absence. Delta-ready globals reject. Scope, data layout, native typing and
checker completeness are separate: a form can be unscoped, ill-kinded or
ill-typed, and an unsupported irreducible leaf can fail this fragment checker.
This is a form checker, not an evaluator or normalization oracle.

`Proof.ResidualNormal` classifies SUPPORTED administrative congruence by
the actual native step/path/branch-path PROOF, excluding beta/zeta/iota/delta
roots. Administrative endpoints agree. Every native step and finite path
from an accepted residual form is proved administrative, yielding absence
of changing reduction and finite-path invariance. Existing strict quoted
normals embed under a no-delta signature; the old grammar, no-step theorem,
normalizer, comparator and native semantics are not weakened or migrated.

Provenance matters: endpoint equality ALONE also holds for beta omega and
delta self-loops. Omega's beta proof cannot be administrative and no
residual-form proof for omega exists. The syntax checker rejects it without
evaluating it. A delta self-loop likewise fails the sufficient grammar even
though every single global delta endpoint equals its source. These controls
explicitly prevent turning invariance into completeness, totality or a
classification of computational loops as harmless administrative stuttering.
No actual unbounded Eval call is made on omega or the synthetic delta loop.

`Fixtures.ExecutableResidualNormal` records ten fixed terminating current
Eval/Quote observations: opaque residual cases, branch/motive redexes,
nested/binder/constructor/data/open residual contexts, a delta-ready global
and ordinary beta readback. Nine quoted forms pass the checked snapshot's
residual checker; the delta-ready global rejects there but passes under a
no-delta signature, as intended. Five independently replayed native programs
derive original-goal safety. The branch-beta path uses the GENERAL scoped
fresh-opening theorem before native outer congruence; other raw contexts
are not all asserted natively typed.

Normality remains separate from scope and typing in explicit controls.
Real beta/zeta/iota redexes, unnormalized branches/motives and computational
loops reject; actual Quote can leave certified globals that are not residual
forms relative to their unfolding signature.
This establishes the residual normality contract needed by future neutral
readback, not full shared neutral-case evaluation/quotation or universal
Elixir correspondence. Shared evaluation still reports `neutral-scrutinee`.
Native/Elixir rules, strict normality contracts and older artifact bytes
are unchanged. New ExUnit regression sources remain unrun under the
maintainer waiver.
Validation for this continuation: all 201 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,447 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Bounded neutral-case capture and readback
`Core.NeutralCase` adds a separate TOP-LEVEL component for capturing an
existing shared neutral scrutinee and reading a residual case back.
The motive and ALL branch closures share the SAME indexed caller
environment; branch names, arities and order are preserved by the
proof-producing branch relation and its metadata theorem.
Capture does not force the motive/branches. Readback quotes the neutral
head, normalizes the captured motive, then opens/normalizes every branch
using the established fresh-field convention. One optional registry is
threaded through the whole pipeline. Non-neutral heads, capture/head/motive
failure, named branch failure and height exhaustion remain explicit.
Neither capture success nor a raw branch arity certifies typing or coverage.

`Proof.NeutralCase` proves output scope and residual-form evidence under a
NO-DELTA signature. Actual-signature normality remains a separate check:
Quote does not unfold certified globals, and a returned delta-ready head can
still change under its actual signature.
The GENERAL arbitrary-signature native readback path composes scrutinee
evaluation/quotation, captured motive normalization and the proved scoped
branch-opening paths. Its source is the original caller-substituted case,
not an asserted reduct. Checked-caller safety then preserves the ORIGINAL
closed expected goal, including when a coherent closing substitution comes
from a nonempty caller. Source/body scope and denoting caller values remain
real premises; there is no typing, reduct or normalization oracle.

`Fixtures.ExecutableNeutralCase` records fourteen fixed terminating actual
captures/readbacks. Generation checks actual motive/branch environment
equality and branch metadata/order before recording terms. Twelve component
readbacks replay, covering branch/motive redexes, beta-computed scrutinees,
open neutral applications, zero/multiple fields, a defined caller slot,
data and constructor-case bodies. A scrutinee's temporary let/application
frame is not mistaken for the case caller.
Five independently replayed native cases derive original-goal safety;
the defined-caller example also retains native fuel/tree agreement.
Two actual nested residual observations stay outside this bounded shared
content slice and produce explicit capture/branch limits, not fabricated
semantic values.

Negative controls retain non-neutral heads (which need not be ill typed),
escaped heads, unbound motives, zero-arity missing slots, motive/branch omega
exhaustion and signature-sensitive residual normality. Actual unbounded Eval
never sees omega. Explicit program and closing-image indices avoid expensive
inverse elaboration through parsed/substituted terms; this is not a proof
or verifier bypass.
This proves bounded neutral-head capture/readback MODEL refinement plus
concrete implementation agreement. It does NOT add residual cases to the
shared recursive value domain, replace strict quotation/comparison, prove
universal Elixir correspondence or supply general neutral-case readback
inside every nested body/value. Existing shared neutral failures and strict
normality contracts remain unchanged. Native/Elixir semantics and older
artifact bytes are unchanged; new ExUnit regression sources remain unrun
under the maintainer waiver.
Validation for this continuation: all 205 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Standalone artifact reproduction, shell syntax, strict Credo over
all 1,449 source files, formatting and whitespace checks pass. Older generated
artifact bytes remain unchanged; waived suites were not run.
### Opt-in recursive residual-case evaluation and readback
`Core.ClosureEval.Neutral` now includes captured residual cases. Each node
stores its neutral scrutinee, ONE caller environment, its raw motive and
ordered raw branches. Positive evaluation captures this node without forcing
the motive/branches. An explicit residual policy follows every recursive
evaluation/application/spine/exact-case call. Existing entry points remain
residual-disabled; `run-residual`, `run-residual-in` and
`run-residual-with` opt in. Default data exclusion and exact constructor
arity remain unchanged.

`Core.ClosureScope`, `Proof.ClosureEvaluation` and `Proof.ClosureWeakening`
extend to these recursive values. Scope includes captured motive/branch
syntax at the captured environment's length, not merely ambient depth.
Arbitrary-arity captured renaming is derived from bounded substitution
agreement. The counterexample with an unbound captured motive still has a
raw denotation but cannot be scoped or arbitrarily weakened.
`Proof.BranchOpeningFrame` extracts the existing pure opening algebra below
quotation; `Proof.BranchOpening` re-exports the same interface.

`Core.ClosureQuote.QuotedIn` and its neutral/spine/branch relations carry
residual permission independently of the optional signature.
Existing `Quoted`, `Normalizes` and all old runtime entry points remain
STRICT specializations. The new residual-case evidence is impossible in
that specialization, preserving the old grammar and no-step theorem.
`ResidualNormalizes` and `normalise-residual`/`normalise-residual-in`/
`normalise-residual-with` have separate positive contracts. Enabled readback
recursively quotes captured heads, evaluates/quotes motives and opens every
branch under its actual arity. The same signature follows all recursive
content, including data and captured residual values.

`Proof.ClosureQuotation` proves native positive readback for either policy,
including nested residual branches, under ARBITRARY native signatures.
`Proof.ResidualQuotation` derives output residual forms under NO DELTA,
preserves branch names/arities/order, constructively embeds old strict
evidence, and composes checked-caller admission with the general native path
at the ORIGINAL closed goal. Actual-signature normality is still separate:
certified delta heads remain unchanged by Quote and can fail that check.
Neither the policy bit nor evaluation/readback success is a typing or
termination certificate.

`Fixtures.ExecutableResidualQuotation` records 31 reviewed terminating
actual evaluations/readbacks, now including complete recursively captured
values. Generation checks that each actual case's motive and branches
capture the SAME caller. All 31 values, outputs, source scope and residual
forms replay independently. Coverage includes the two former nested limits,
motives, binders, application heads/arguments, constructor/data fields,
eager beta, lets, exact cases and residual-valued callers. Thirteen
independently admitted instances derive original-goal safety, including
genuinely typed nested scrutinees/branches and a residual caller argument
with native fuel/tree agreement. A three-field opening followed by a lambda
explicitly instantiates scoped weakening on that residual caller.
Other observations are RAW operational controls, not all typed programs.

Strict rejection, escaped/unbound captures, zero-field missing slots,
finite motive/branch omega exhaustion, missing signature, wrong layouts,
exact-arity rejection and delta-sensitive normality remain checked controls.
No actual unbounded Eval call sees omega. Earlier artifact bytes and
native/Elixir semantics are unchanged. The older top-level component still
uses strict content APIs and retains its historical limits.
This completes recursive residual MODEL readback for the named slice, not
universal Elixir correspondence, eta/delta completeness or semantic totality.
Existing normalized comparison/checking remains strict; positive residual
comparison integration is a separate next increment. New ExUnit sources
remain unrun under the maintainer waiver.
Validation for this continuation: all 210 Agda modules pass without warnings,
the exact `funext`/legacy `tree-decides` inventory is unchanged, ten hygiene
regressions pass and all-directory hygiene finds no new holes or checking
bypasses. Shell syntax and standalone byte-for-byte artifact reproduction
pass. Strict Credo checks all 1,451 source files and 19,143 modules/functions
without issues. All seven required gates returned exit code 0 after
formatting; whitespace checks pass. Waived suites were not run.
### Positive residual comparison and original-goal checking
`Core.ResidualComparison` is an OPT-IN comparator using recursive residual
normalization. Equal results retain both executions and their common form;
distinct results retain both executions and syntactic difference only.
Failures identify the side and bounded evaluation/readback reason.
One optional registry follows both normalizations. The old strict comparator
and its contracts remain unchanged.

`Proof.ResidualConversion` derives native joining for arbitrary signatures
from the two scoped, environment-relative paths, and derives conversion
for the checked signature.
The common endpoint need not be strictly irreducible or normal relative to
certified delta. Its no-delta residual-form evidence is separate.
Existing strict equality evidence embeds constructively, without a claim
about which strategy or fuel budget succeeds. Closed, open and
residual-valued caller instances exercise the general conversion theorem.

`Core.ResidualAdmission` reuses the SAME data-only checking request and
diagnostics as `Core.NormalizingAdmission`, but has a separate residual
comparison basis and checked result. It independently replays subject
support/inference, inferred-type support/kind and goal support/kind BEFORE
exact reflexivity or bounded comparison. Exact syntax can succeed at zero
comparison fuel; it cannot bypass either kind check. Native admission,
finite-trace/fuel/tree safety and fuel/tree agreement preserve the ORIGINAL
goal. The normalized equality is derived internally, not supplied as an
asserted conversion or normalization callback. This checker remains closed.

`Core.WireResidualChecking` reuses the EXISTING tag-20 codec and its
fidelity/roundtrip results, adding a separate opt-in replay. Parsed requests,
successful admission and exact request pinning stay distinct. There is no
new wire tag or residual permission flag controlled by untrusted input.
The old strict checking/wire APIs and native/Elixir code are unchanged.

`Fixtures.ExecutableResidualComparison` records 41 reviewed terminating
actual Conv/readback pairs. Both model readbacks, source scope and
classifications independently replay; 35 equal-readback pairs also record
actual positive Conv results. They cover the complete prior recursive
residual corpus and four new well-kinded residual-type pairs. Six distinct
controls cover eta, delta, grades, universes, branch names and branch arity.
Actual Conv accepts the eta/delta pairs despite distinct quoted forms;
the delta pair additionally has a native conversion witness. Distinct forms
therefore cannot serve as non-conversion proofs.

Four actual serialized requests derive NONEXACT normalized admission in
both directions, under data indices and through nested residual branches.
Each independently checks its inferred type, normalized basis, wire pinning,
original-goal source/readback safety and native fuel/tree agreement.
The expected goals retain their original residual/beta syntax.
Controls preserve strict nonexact rejection, strict/exact zero-fuel success,
nonexact exhaustion, both kind guards, source scope, inference, universe
ceiling, grades, separate explicit cumulativity and malformed/trailing
wire rejection. Bounded omega tests stay entirely in the model; no actual
unbounded Eval sees omega.

This proves positive residual MODEL comparison/admission for the named
slice, not universal Elixir checker/Conv correspondence, eta/certified-delta
completeness or semantic termination. Normalization and syntax equality do
not certify typing on their own. All older artifact bytes remain unchanged.
New ExUnit regression sources remain unrun under the maintainer waiver.
Validation for this continuation: all 217 Agda modules pass without warnings
and every source is registered exactly once in the runner. The exact
`funext`/legacy `tree-decides` inventory remains unchanged; ten hygiene
regressions and all-directory hygiene pass without holes or checking
bypasses. Shell syntax, standalone byte-for-byte artifact reproduction and
strict Credo over all 1,453 source files pass. Each of the seven required
gates returned exit code 0 after formatting; whitespace checks pass.
Maintainer-waived suites were not run.
### Ambient residual checking and coherent caller closure
`Proof.FreshEnvironment` derives arbitrary-size neutral caller frames from
the existing branch-opening construction. Length, scope and denotation are
proved. Its substitution reconstructs OPEN syntax only within the declared
scope; the out-of-prefix counterexample forbids upgrading this bounded
agreement to a false global identity equation.

`Core.AmbientResidualAdmission` is a separate, proof-consuming extension of
residual expected-goal checking to a native well-formed context. It replays
size-relative subject support/inference, inferred-type support/kind and
goal support/kind with `infer-wf`/`kind-wf`, then chooses exact reflexivity
or residual comparison under FRESH neutral slots. The fresh identity
theorem turns the general substituted native conversion back into
conversion of the original open types. Context-relative native typing and
admission are derived, not trusted as input. The raw nonempty-context
interfaces and all existing closed/strict APIs remain unchanged.

`Core.ResidualCallerAdmission` pairs an existing caller request with one
additional ordinary inferred-kind recipe. It checks forward declarations,
declaration/argument support and closed dependent argument typing, then
runs ambient checking. It constructs the EXISTING `CallerAdmission.Checked`
closure evidence and reuses coherent substitution, closing BOTH subject
and original expected goal, native finite-trace/fuel/tree safety and
fuel/tree agreement. There is no new transport or normalization oracle.
Caller slots remain abstract during open checking: actual arguments are
used for closure, not as a shortcut to open equality.

`Core.WireResidualCaller` reuses TWO existing character packets: the caller
codec and ordinary-recipe codec. Each checks its own EOF. Their combined
roundtrip and exact request pinning cover all caller fields plus the
inferred-kind recipe. There is no new tag, old packet shape change or
production Elixir API change.

`Fixtures.ExecutableResidualCaller` records seven reviewed terminating
actual open Conv/readback and closing observations. Six paired proposals
independently replay nonexact native admission, actual inferred types,
context sizes, fresh frames, both open forms, packet encoding and original
closed subject/goal equations. They cover a dependent variable, conversion
under a binder, genuinely open residual case types with opaque versus
constructor arguments, nested residual branches and the empty-context
specialization. Source and normalized readback safety retain the original
closed goal, and every accepted caller retains native fuel/tree agreement.

The seventh proposal validates a frame where two distinct OPEN types
become the same type under one supplied closing assignment. Fresh checking
and paired wire replay still reject that open comparison. A nearby exact
request validates all declarations/actuals/kinds, and the particular closed
instance is proved safe. Rejection is therefore not a closed-unsafety or
non-conversion theorem. It prevents one instance's coincidence from being
misused as a general open conversion proof.
Missing/surplus/reversed frames/recipes, bad dependent arguments, escaped
slots, unsupported payloads, universe overflow, both kind guards before
zero-fuel exact checking, nonexact exhaustion and malformed/trailing
packets retain controls. A syntactically valid kind packet can still fail
semantic replay.

This covers checked SYNTACTIC callers and explicit closed actual terms,
not extraction of arbitrary semantic contexts or automatic normalization
of defined local slots. Universal producer/Elixir correspondence,
eta/certified-delta completeness, broader argument/layout inference,
semantic totality and backend soundness remain separate.
Native/Elixir semantics, all older artifact bytes and strict/closed APIs
are unchanged. New ExUnit regression sources remain unrun under the
maintainer waiver.
Validation for this continuation: all 223 Agda modules pass without warnings,
and every source is registered exactly once. The exact `funext`/legacy
`tree-decides` inventory is unchanged. Ten hygiene regressions and the
all-directory scanner pass without holes or checking bypasses. Shell syntax,
standalone byte-for-byte artifact reproduction and strict Credo over all
1,455 source files pass. All seven required gates returned exit code 0
after formatting; whitespace checks pass. Waived suites were not run.
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
