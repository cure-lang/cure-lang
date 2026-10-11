# Mechanised soundness proof for the Cure Core kernel

This directory holds **deliverable B**: a mechanised proof, in
[Agda](https://wiki.portal.chalmers.se/agda/), of the soundness of the Cure
Core kernel. It is the machine-checked counterpart of the written argument in
[`../docs/SOUNDNESS.md`](../docs/SOUNDNESS.md), whose §7 scopes exactly this
development.

> **Status: in progress.** The formalisation of the Core calculus and the
> typing judgment is complete and compiles clean. The canonical-form lemmas
> are **proved**, as are the renaming and substitution lemmas **except for
> their application case** — the one documented obstruction. The
> Progress/Preservation/Soundness theorems are stated, with their remaining
> obligations isolated as `postulate`s, each carrying a named proof
> strategy. See [Status](#status) for the lemma-by-lemma breakdown.

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
| Builtin ctor names | `BuiltinCtors` | `@builtin_ctor_aliases` |

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
| `Proof.Preservation` | `weaken`, `subst⇒`, `subst⇐`, `preservation` | ⚠️ renaming/substitution + `ξ-*` congruence cases **proved**; β/ζ/ι/δ inference-preservation open |
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

### In progress (statements given, proofs open)

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
5. **`preservation`** (`Proof/Preservation.agda`) — **the `ξ-*` congruence
   cases and the β/ζ CHECKING cases are proved** (generalised to an arbitrary
   context `Γ`). The remaining obligations are the inference-preservation
   gaps: β/ζ/ι/δ do not preserve INFERABILITY (the reduct's continuation is
   only checked), and the `ξ-app₂` / `ξ-case` result types name their subterm
   syntactically. See [The `preservation` findings](#the-preservation-findings).
6. **`soundness`** (`Proof/Soundness.agda`) — the type-safety induction
   combining Progress and Preservation.
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

- **β / ζ / ι / δ do not preserve INFERABILITY.** The β reduct
  `substTopT a b` has its continuation only *checked* (`b` checks the
  codomain, it does not infer it), so it cannot be shown to infer `T`. The
  CHECKING-mode `preserve-β` / `preserve-ζ` are what the soundness argument
  needs; the inferring-mode statements are recorded as obligations.
- **The `ξ-app₂` / `ξ-let` / `ξ-case` result types name their subterm
  SYNTACTICALLY** (`⇒-app` returns `substTopT a c`, `⇒-case` returns
  `tm-app m s`), so the reduced subterm's type differs unless the two are
  convertible. Resolved by the `ReduceConv` hypothesis (`⇝ ⊆ ≈`): the
  kernel's `conv?` normalises both sides, so a reduct is definitionally
  equal to its redex. `≈-subst-cong` (substitution congruence) then relates
  `substTopT a c` to `substTopT a′ c`.
- **The `ξ-lam-body` / `ξ-pi-cod` congruences reduce UNDER A BINDER**, so
  `preservation` is generalised from `⟨⟩` to an arbitrary context `Γ`; the
  `ξ-lam-dom` / `ξ-pi-dom` cases (which change the binder's domain) are
  transported by the CONTEXT CONVERSION lemma (`conv⇒` / `conv⇐`).

Two further `preservation` obligations need a **framework extension**, not
just proof work:

- **The ι (branch substitution) case.** The `⊢*brs` rule types a branch's
  field binders with `tm-hole "field"` (`extendⁿ`), but the ι reduction
  substitutes the constructor's REAL arguments (typed by `ctor-args ct`).
  The substitution lemma therefore cannot relate the hole-typed field
  variables to the actual args. Proving ι needs `brs∷` to type the field
  binders with the constructor's argument telescope (a change to the typing
  judgment, rippling through the renaming/substitution lemmas).
- **The δ (certified unfolding) case.** `Certified` (Proof.Progress) gives
  only that a global's body is FINAL; δ preservation needs it to INFER the
  global's declared type. This is the well-typedness half of the kernel's
  `Env.certified?` and needs a strengthened signature hypothesis (plus a
  weakening-from-`⟨⟩` lemma, since a body types in `⟨⟩` but must type in
  `Γ`).

### The `soundness` finding

`soundness` as stated ("reaches a value, OR raises, OR diverges") is a
**classical** disjunction: the `diverges` outcome is a negative statement
(no value is reachable), and deciding which disjunct holds requires
coinduction (or a well-founded measure), neither of which the development
sets up. A constructive **fuel-indexed** version — `soundness-fuel n`
returns either a reached value or "fuel exhausted" — is provable by
induction on `n` (consuming `progress`, `preservation`, and
`Final`-preservation), and is the natural next step.

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

The β and ζ cases of Preservation are now **proved**. The remaining
obligations are the ι (branch substitution) and δ (certified unfolding)
cases and the congruence cases, plus the signature closedness axioms.

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
