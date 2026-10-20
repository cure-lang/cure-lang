# Soundness of the Cure Core Kernel

**A written soundness argument for the trusted dependent-type kernel.**

Status: written argument with executable evidence; formal interfaces under repair.
Scope: the trusted kernel (`lib/cure/core/`, the TCB), not the elaborator, the
emitter, or the surface language.
Companion documents: [KERNEL.md](KERNEL.md) (what each mechanism is and why it
exists), [PROOFS.md](PROOFS.md) (the proof surface), `MATCH.md` §6.17 and
Appendix J (the `match`-specific sketch this document generalises),
[PROOF_CARRYING.md](PROOF_CARRYING.md) (offline re-validation).

This document exists because the kernel is small enough to audit and important
enough to deserve a written argument. It states the soundness theorem, walks the
Progress and Preservation proofs by term former, enumerates the assumptions the
argument rests on, and maps each lemma to the executable evidence that tests it
today. It is deliberately honest about what is *proved*, what is *assumed*, and
what is *tested but not proved*.

**Formal applicability warning.** The four refuted historical interfaces
are now frozen only in `proof/Proof/InterfaceAudit.agda`. Conversion uses
separation of two exposed rigid type heads, not raw syntax-head reflection;
universe cumulativity belongs to declarative typing, not symmetric equality.
`Proof.ReductionConversion` now inhabits the full conversion record AND
`ReduceConv` by common reducts after compact-literal expansion.
`Proof.SoundnessModel` jointly instantiates the current soundness hypotheses
on a nonempty closed-entry fragment, including a finite typed global table.
This closes the formal-model inhabitation gap, NOT executable NbE/η refinement.
The old `ClosedSig` oracle is frozen only in
the audit; active preservation/soundness now use inhabited `ClosedFragmentSig`,
explicitly restricted to individually closed telescope entries/results.
This does **not** establish dependent telescope support. The former global `Covers` oracle
is now frozen only as a negative regression: admitted cases carry local
`CaseCoverage` evidence. `LiteralArity` was also removed from active confluence:
literal reduction steps carry local arity witnesses. Successful
compilation of the existing parameterised Progress/Preservation/soundness
modules does **not** establish an applicable kernel soundness theorem.
Their conditional derivations are not completed executable certification.
No termination-check overrides remain. `Proof.Confluence` now uses a
strong one-step parallel diamond and checked strip/closure recursion.
This establishes specification confluence, not executable soundness. See §8.

---

## 1. What is being claimed

### 1.1 The object language

The object language is the **Core** calculus of `Cure.Core.Term` — a
bidirectional, intensional Martin-Löf type theory with:

- **a fixed predicative universe hierarchy** `Type 0 : Type 1 : Type 2`
  (`Cure.Core.Universe`, ceiling `2`; `Type 3` is not a well-formed term);
- **graded dependent functions** `{:pi, g, dom, cod}`, `{:lam, g, dom, body}`,
  `{:app, f, a}` where the grade `g` ranges over the four-element QTT carrier
  `{:erased, :linear, :affine, :unrestricted}` (`Cure.Core.Grade`);
- **graded `let`** `{:let, g, ty, val, body}`, ζ-transparent;
- **indexed inductive families** `{:data, name, params, indices}` with
  constructors `{:ctor, name, args}`;
- **a dependent eliminator** `{:case, scrut, motive, branches}`;
- **global references** `{:global, name}`;
- **primitive numeric/atom/binary base types and their literals**
  (`{:int_type}`/`{:int_lit, n}`, `{:nat_lit, n}`, `{:bounded_lit, n}`,
  `{:float_type}`/`{:float_lit, f}`, `{:binary_type}`, `{:atom_type}`/
  `{:atom_lit, a}`);
- **inert effect terms** `{:effect_type, t}`, `{:effect_pure, a}`,
  `{:effect_bind, e, k}` — with *zero* reduction rules;
- **two development-only leaves**: `{:hole, name}` and `{:absurd}`.

`Bool` and `Nat` are genuine inductive families, not primitives
(`Cure.Core.Builtins.seed`). Propositional equality is the ordinary indexed
family `Equivalent` with constructor `reflexive` (`@builtin(:eq)`), not a
primitive node.

### 1.2 The judgement

Typing is bidirectional, exactly as `Cure.Core.Kernel` implements it:

- `infer(Γ, e) = {:ok, T}` — synthesise the type *value* `T`;
- `check(Γ, e, T) = :ok` — verify `e` against the expected type *value* `T`,
  falling back to `infer` plus a cumulative conversion test (`check_via_infer`).

We write `Γ ⊢ e : T` for "the kernel accepts `e` at type `T` in context `Γ`",
meaning `check(Γ, e, T)` succeeds (or `infer` returns a `T'` with `T' ≡ T`).
Types are compared as **values** — `Cure.Core.Value` — via NbE definitional
equality (`Cure.Core.Conv`), with cumulativity applied at the sort level.

### 1.3 The dynamic semantics

Evaluation is **normalization by evaluation** (`Cure.Core.Eval`), read back to
syntax by `Cure.Core.Quote`, with the policy between them owned by
`Cure.Core.Normalise`. The reduction relation `⇝` comprises:

- **β**: `(λx. b) a ⇝ b[x := a]` — `Eval.apply/2` on `{:vlam, …}`;
- **ζ**: `let x = v in b ⇝ b[x := v]` — `Eval.eval({:let, …})` pushes `v` into
  the environment, so no `let` survives evaluation;
- **ι**: `case (ctor c args) of … ⇝ b_c[args]` — the `{:vcase}`/`{:vctor}` arm
  of `Eval.eval({:case, …})`;
- **δ**: `global f ⇝ body(f)`, **gated**: `Eval.eval({:global, name})` leaves a
  global *neutral* (`{:nglobal, name}`) and only `Normalise.unfold_certified_head`
  unfolds it, and only when `Env.certified?(sig, name)` holds — i.e. the global
  carries a valid totality certificate (§3.2).

We write `e ⇝* e'` for the reflexive-transitive closure.

### 1.4 The theorem

> **Theorem (Soundness).** Let `e` be a **closed, hole-free, final-Core** term
> with `· ⊢ e : T` for a closed type `T`. Then evaluation of `e` either:
> 1. reaches a value `v` with `· ⊢ v : T`; or
> 2. raises an exception (`case_clause` / the ι coverage guard, or a partial-op
>    guard); or
> 3. diverges.
>
> In particular, evaluation never reaches a **stuck** state — a well-typed
> closed term is never a neutral eliminator whose scrutinee is a value.

The three-way conclusion mirrors `MATCH.md` §6.17: totality of *closed*
programs is not promised (a closed term may legitimately diverge — the language
is not total), but *stuckness* is unreachable. "Stuck" is the failure mode that
would be a soundness bug: a term that is neither a value, nor able to step, nor
raising.

### 1.5 What the theorem does *not* claim

- **It does not claim the language is total.** `loop : A` that diverges is
  typeable if it is not certified total; divergence is conclusion (3), not a
  contradiction.
- **It does not claim the elaborator is correct.** The elaborator may reject
  good programs or (in principle) accept one whose Core it then fails to
  produce; the kernel re-checks whatever Core it is *given*. Soundness of the
  kernel is what makes a kernel-accepted Core term trustworthy.
- **It does not claim the emitter is correct.** BEAM emission is out of scope;
  §5 states the (small) interface the argument assumes of it.
- **It is not an end-to-end mechanised implementation theorem.** Parts of the
  syntax and algebra are machine-checked; historical soundness interfaces
  were refuted and repaired for a restricted fragment. A joint formal
  full-reduction instance now exists and exact-arity closed-entry branches
  bind the last field at zero; dependent signatures, filtered/erased frames,
  η and implementation refinement remain open.
  See §§7–8.

---

## 2. Progress

> **Lemma (Progress).** If `· ⊢ e : T` and `e` is not a value, then either
> `e ⇝ e'` for some `e'`, or `e` raises.

We proceed by cases on the head of `e`. "Value" means a canonical form:
`{:lam, …}`, `{:ctor, …}`, `{:pi, …}`, `{:type, l}`, `{:data, …}`, a literal, or
an inert effect former (`{:effect_type,_}`, `{:effect_pure,_}`,
`{:effect_bind,_,_}`) — exactly `MetaCheck.canonical_head?/1`.

- **`{:var, k}`.** Closed, so no free variable; the case is vacuous.
- **`{:type, l}` / literals / `{:data, …}`.** Values.
- **`{:pi, …}`, `{:lam, …}`.** Values.
- **`{:app, f, a}`.** By IH, `f` steps or is a value. If `f` is a value it is a
  `{:lam, …}` (a well-typed application's function position has function type);
  then β applies. If `f` is neutral, `Eval.apply/2` accumulates the argument on
  the spine — the term is *neutral*, not stuck, because a neutral function is a
  legitimate value of function type whose eventual reduction depends on the
  neutral's own head.
- **`{:let, g, ty, val, body}`.** ζ applies unconditionally: `Eval.eval` pushes
  `val` into the environment. (Note `let` is *not* a value former here, so it is
  never a stuck state.)
- **`{:case, scrut, motive, branches}`.** By IH, `scrut` steps or is a value.
  If `scrut` is a value, it is a `{:vctor, …}` (a well-typed `case`'s scrutinee
  has data type) or a neutral. If a constructor, ι fires; the branch is found
  because `check_coverage` (§3.3) required a branch for every possible
  constructor, and `Eval.eval({:case, …})` raises a *named* coverage error only
  if a constructor is missing — which coverage forbids. If a neutral, the term
  is neutral (`{:ncase, …}`), not stuck.
- **`{:global, name}`.** A global is a value position; if certified total it may
  δ-unfold; if not, it is an opaque neutral. Either way it is not stuck.
- **`{:hole, _}` / `{:absurd}`.** Excluded by hypothesis (hole-free final Core;
  `{:absurd}` is rejected in reachable position by `infer`, §3.4).

The only way Progress could fail is a well-typed application whose function
position reaches a value that is not a lambda, or a well-typed `case` whose
scrutinee reaches a non-data value. Preservation (§4) rules both out by keeping
types invariant across steps.

---

## 3. The three side conditions

Progress and Preservation are *conditional*. The kernel is sound **provided**
the following three properties hold. Each is a genuine theorem about a
sub-component, each is enforced in code, and each is the load-bearing assumption
that a broken implementation would falsify.

### 3.1 Strict positivity

**Claim.** Every inductive family declared in the signature is strictly
positive: the family name never occurs to the left of an arrow in any of its
own constructors' field types.

**Why it is needed.** A negative occurrence
(`MkBad : (Bad -> Nat) -> Bad`) yields a well-typed non-terminating term *with
no recursion written anywhere* — a perpetual-motion machine — which inhabits any
type and would prove `False`. Progress's "`case` scrutinee is data" and
Preservation's conversion argument both assume the inductive types are
well-founded trees.

**How it is enforced.** `Inductive.positive?/2` (`lib/cure/core/inductive.ex`),
run at `Inductive.declare/3`. The walk is **nested**: when a field mentions
another family, the checker descends into that family's constructors too
(cycle-guarded by a seen-set), mirroring Agda's `Positivity.hs` — so smuggling a
negative occurrence through a wrapper datatype is also rejected.

**Tested by.** `Antigen.Assays.Positivity` (known-label generation: emits
positive families and negative witnesses, asserts accept-iff-positive);
`test/oracle/` Idris parity rows.

### 3.2 Totality gates δ-reduction

**Claim.** Whenever `Normalise` unfolds a `{:global, name}` during type
checking, that global carries a valid **size-change totality certificate**
(Lee–Jones–Ben-Amram).

**Why it is needed.** Type checking *runs* programs (δ-reduction during
conversion). Unfolding a looping definition makes the *type checker* loop — the
checker would not terminate, and worse, a non-terminating definition can claim
any type it likes, because it is never caught holding the wrong value. So
δ-reduction must be gated behind a proof that the definition terminates.

**How it is enforced.** `Eval.eval({:global, name})` returns an opaque neutral
`{:nglobal, name}` *always*; the only δ-unfold site is
`Normalise.unfold_certified_head/3`, guarded by `Env.certified?(sig, name)`. The
certificate (`lib/cure/core/certificate.ex`) is a size-change call summary
extracted from checked Core; the *global* SCC/closure computation lives outside
the TCB in `Cure.Elab.TotalityGraph` / `Cure.Elab.TotalityCertificate`, and the
kernel only *verifies* their finite certificates. Mutual recursion is handled by
the cross-function generalisation (`addFunctions`).

**Tested by.** `Antigen.Assays.Totality` and `Antigen.Assays.TotalityClosure`
(known-label generation of terminating and non-terminating definitions);
`Antigen.Assays.DeltaReduce`; the `conversion_termination` assay (reflexivity
`conv(t,t)` within budget ⟺ deep normalization — the sharpest independent probe,
per the Antigen research synthesis §3.5).

**Known conservative boundary.** Descent must be *structural*. Semantic
termination arguments (a shrinking measure, well-founded recursion on a custom
order) fall outside the certificate — such functions stay opaque during type
checking, which is sound but incomplete.

### 3.3 Coverage and branch unification

**Claim.** For every `{:case, scrut, motive, branches}` the kernel admits,
`check_coverage` requires a branch for every constructor of the scrutinee's
family that the index unifier does not prove impossible, and every required
branch body checks against the motive instantiated at that constructor's
indices.

**Why it is needed.** ι-reduction assumes the branch exists. If a possible
constructor had no branch, evaluation would reach the coverage guard and raise —
which is *conclusion (2)* of the theorem, not a soundness violation, but it
would make the "statically exhaustive `match` cannot raise `case_clause`"
corollary false. Coverage is what makes that corollary true.

**How it is enforced.** `check_coverage` + `check_case_branches` +
`Kernel.branch_unify/5`. The unifier is first-order and structural with the full
Solution / Injectivity / Deletion / Clash / Cycle rule set; `Clash` and `Cycle`
discharge impossible branches, `Solution` refines a branch's argument types
(branch refinement). Anything undecidable is `:undecided`, and the kernel
conservatively **requires** the branch.

**Tested by.** `Antigen.Assays.BranchUnify`, `Antigen.Assays.Indexed`,
`Antigen.Assays.DotForcing`; the `E118` diagnostic suite; Idris oracle rows for
impossible-clause discharge and `Fin`-absurd elimination.

### 3.4 Hole and absurd discipline

**Claim.** A term admitted at the *release* boundary contains no `{:hole, _}`
and no reachable `{:absurd}`.

**Why it is needed.** `check(Γ, {:hole, _}, T) = :ok` — a hole typechecks at any
type (so development can proceed around it). `infer` rejects `{:absurd}` in
reachable position, but `check` admits it once the context is inconsistent. Both
are development conveniences that would be unsound if they escaped into a
released artifact.

**How it is enforced.** `Cure.Core.Validator.release_config/0` sets
`no_hole: :reject` and `no_absurd_node: :reject`. The single enforcement point
is `Emit.reject_holes/2` (called from both codegen entry points,
`emit.ex:50` and `emit.ex:109`), which validates the **pre-erase** Core body —
so a hole hidden in an erased position (a rewrite proof/motive, an `eq`/`refl`
argument) is caught before `Erase.erase` drops it. `check_def` also runs the
validator over both the declared type and the body.

**Status (verified against the tree).** This is the audit's §4.2 finding. The
audit reproduced a *running* hole; the soundness-sweep log
(`docs/superpowers/CORE-SOUNDNESS-SWEEP-COMPLETE.md`, item K3) claims the
firewall landed. **The firewall is implemented, wired, and tested in the current
tree:**

- `Validator.release_config/0` sets `no_hole: :reject`;
- `Emit.reject_holes/2` is the enforcement point, called from both codegen
  entry points (`emit.ex:50`, `emit.ex:109`);
- `test/cure/compiler/dependent_codegen_test.exs:51` pins the behaviour:
  a dependent module containing `?todo` is refused with
  `{:codegen_error, {:unfilled_hole, details}}`.

The ordinary and lifted codegen paths were subsequently audited and tested
(§8.1). `cure check` deliberately permits development holes; compilation must
reject them. Maintaining release-entry-point coverage is an ongoing regression
obligation, not evidence that the firewall is missing.

---

## 4. Preservation

> **Lemma (Preservation).** If `· ⊢ e : T` and `e ⇝ e'`, then `· ⊢ e' : T`.

By cases on the reduction rule.

- **β.** `(λx. b) a ⇝ b[x := a]`. `infer({:app, f, a})` requires `f : Π(x:A).B`
  and `a : A`, giving type `B[x := a]`; the body `b` was checked under
  `Γ, x:A` against `B`, so substituting `a` for `x` (capture-avoiding, via
  `Term.subst/3`) preserves the type. The kernel's substitution and the
  elaborator's `Subst.shift` are pinned equal by `Antigen.Assays.Elab` and the
  `beta_subst` generator.
- **ζ.** `let x = v in b ⇝ b[x := v]`. `infer({:let, …})` checks `v` against
  `ty` and infers `b` under `Context.extend_def` (the variable is
  definitionally `v`). Substituting `v` is exactly the definitional equality the
  context already recorded, so the type is unchanged.
- **ι.** `case (ctor c args) of … ⇝ b_c[args]`. `check_case_branches` checked
  `b_c` against the motive instantiated at `c`'s result indices; the scrutinee's
  actual indices are those same indices (the branch was admitted only because
  `branch_unify` solved the index equation), so the result type — the motive at
  the scrutinee's indices and value (`apply_motive`) — is preserved.
- **δ.** `global f ⇝ body(f)`. This is the delicate case, and it is *why*
  totality gates δ. `Env.certified?(sig, f)` guarantees `body(f)` terminates and
  was checked against `f`'s declared type at `check_def`. Since δ only fires on
  certified globals, the step is type-preserving by `check_def`'s conclusion.
  An *uncertified* global never unfolds, so there is no step to preserve.

The `MetaCheck` module is the executable form of this lemma:
`type_preserved?/2` infers a term's type, normalizes, re-infers, and asserts the
two types are convertible.

---

## 5. The trusted base and its assumptions

The argument above rests on the following. Each is stated so a reader can attack
it directly.

### 5.1 The TCB

`lib/cure/core/` (~9,200 LOC): `term.ex`, `value.ex`, `eval.ex`, `quote.ex`,
`conv.ex`, `normalise.ex`, `kernel.ex`, `context.ex`, `inductive.ex`,
`universe.ex`, `grade.ex`, `certificate.ex`, `size_change.ex`, `builtins.ex`,
`serialize.ex`, `validator.ex`, `runtime_refs.ex`, `totality_certificate.ex`,
`scc_certificate.ex`, `meta_check.ex`, `printer.ex`.

### 5.2 Explicit trust roots

Enumerated by `cure audit trust <Module>`:

- **`postulate`** — an assumed proposition. An opaque family is
  *non-eliminable* (`Inductive.opaque_family?`, `:opaque_not_eliminable`), so a
  postulate cannot be case-split into a proof of anything.
- **bodyless `@extern`** — an external boundary; typed, never unfolded.
- **`believe_me`** — the explicit escape hatch.
- **builtin ops** — bodyless by design, checked for a valid *type* only, treated
  as total by fiat (Lean/Idris do the same for primitive ops).

### 5.3 Assumptions the argument makes of *outside* the kernel

1. **The signature is well-formed.** `Inductive.declare/3` enforced the universe
   check and strict positivity (§3.1) when each family was registered.
2. **The verified size-change criterion implies semantic termination.**
   The kernel independently verifies SCC partitions, base edges, composed
   matrices, and saturation; an untrusted proposer's output is not accepted
   merely because its matrices have valid dimensions. What remains unproved
   is the full chain from trusted Core call extraction to semantic size
   descent and from the size-change criterion to termination (§8.2).
3. **The emitter maps Core faithfully.** BEAM emission is assumed to preserve
   the operational semantics of §1.3. Out of scope here.
4. **The host runtime is trusted.** Elixir/OTP integer and float semantics, the
   atom table, and `:crypto` (for certificate hashing) are trusted.

### 5.4 Deliberate exclusions from the TCB

- **The SMT solver is never trusted.** Z3 runs only as an *untrusted lint* over
  refinement obligations; its verdicts can warn but never certify a kernel
  judgement.
- **The elaborator is never trusted.** The kernel re-derives every type; it
  never consumes an elaborator-supplied type as an axiom.

---

## 6. Corollaries

- **Exhaustive `match` cannot raise `case_clause`.** A statically exhaustive
  `match` has a branch for every possible constructor (§3.3), so ι never reaches
  the coverage guard. (The `case_clause` in conclusion (2) is only for
  *non*-exhaustive blocks, which `E118` rejects at compile time — so in practice
  a well-typed program does not raise it either.)
- **Pattern purity.** Pattern matching contributes no observable effects; all
  effects in a `match` come from the scrutinee, guards, or selected branch.
- **Proof irrelevance by erasure.** A value graded `:erased` leaves no runtime
  footprint (`Grade.erased?`), so proof-only values are erased before emission.
  This is what lets `Equivalent` proofs be computationally irrelevant.
- **Conversion is decidable on certified terms.** With δ gated (§3.2) and β/ι
  terminating on the certified fragment, definitional equality is decidable by
  NbE + structural comparison (`Conv.conv_values?/4`), with a fuel counter as a
  belt-and-braces bound.

---

## 7. Toward mechanisation

The implementation theorem is not machine-checked end to end. The interface
audit in §8 refuted four historical contracts, now frozen only as negative
regressions. Their replacements now have checked consumers and a joint
full-reduction instance for the closed-entry specification. Executable
correspondence and dependent-signature support are not established.
Remaining obligations include:

1. **NbE conversion.** A mechanised proof must model `Eval`/`Quote`/`Conv` and
   prove conversion sound (positive *and* negative). Per Lennon-Bertrand's
   *What does it take to certify a conversion checker?* (FSCD'25), conversion
   soundness needs only injectivity of type constructors — provable in a
   meta-theory *weaker* than the object theory — while normalization is needed
   only for *termination*. This is encouraging: the hard part (termination) is
   exactly what the totality certificate abstracts.
2. **The totality certificate.** A mechanised proof must either (a) prove the
   size-change principle itself (Lee–Jones–Ben-Amram is a substantial
   development), or (b) take the certificate as an assumption and prove that
   *verifying* it implies termination — the "translation validation" discipline
   of QuickChick's POPL'18 certified generators.
3. **The universe hierarchy and cumulativity.** Standard but fiddly.
4. **Grades.** The QTT carrier is finite, so its laws are exhaustively checkable
   (`Cure.Core.GradeTest`) — a mechanised proof would discharge them by case
   analysis.

A realistic target is a **Rocq/Coq or Agda development of the Core calculus with
the totality certificate as a stated hypothesis**, proving Progress and
Preservation, and a separate (smaller) proof that the certificate verifier is
sound. That splits the research risk: the certificate's *verification* is small
and kernel-adjacent; the certificate's *generation* (SCC closure) is the part
that stays outside the TCB and outside the mechanised proof.

### 7.1 The Agda development (`proof/`)

A partial mechanisation now exists in [`proof/`](../proof/README.md): the Core
calculus, the typing judgment, the canonical-form and head-inversion lemmas,
the renaming/substitution lemmas, **Progress**, **`Final`-preservation**,
**`preservation` (every case, including ι and δ)**, and — with the side
conditions carried as hypotheses — **derivations of both constructive forms
of the soundness theorem**. The following statements belong to conditional
parameterised modules, now jointly instantiated by `Proof.SoundnessModel`
for the closed-entry specification. There is no implementation refinement
making them an executable kernel certificate:

```agda
-- the bounded unfolding, by induction on the fuel
soundness-fuel : ∀ (n : ℕ) {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → FuelResult t T

-- the coinductive completion, by guarded corecursion
soundness-tree : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → EvalTree t T
```

`soundness-fuel` runs the type-safety induction for `n` steps and returns
either a reached value (with its type, value witness, and multi-step
reduction) or "fuel exhausted", consuming Progress, Preservation, and
`Final`-preservation. `soundness-tree` is the full outcome as a coinductive
tree: a `Reached` leaf is a terminating evaluation, a `Stepped` node continues
at the reduct. Divergence is given POSITIVELY by the greatest fixed point
`Diverges` (a term that can always step), inter-derivable with the tree's
never-reaching spine; and the fuel-indexed run is exactly the depth-`n`
truncation of the tree.

Two findings from the mechanisation are worth recording here. First, the
β/ζ "inference-preservation" gaps (§4) are **dissolved** by `check-infer`: a
hole-free term that CHECKS against a type has a corresponding **declarative**
inference derivation, because the only checking rule without a matching
inference rule is `⇐-hole`. This judgment includes explicit `⇒-conv` and
`⇒-cumul` closure: it does not assert executable synthesis returns the same
type syntax or a larger cumulative sort. So the
checking-mode β/ζ reducts infer their type once the redex is final. Second,
δ preservation is discharged by a `CertifiedTyped` hypothesis — the
well-typedness half of `Env.certified?` — plus `weaken-closed` (a closed term
that types in `⟨⟩` types in any context).

The **ι (branch substitution) case** — the one remaining Preservation
obligation — is now **proved**. The `⊢*brs` rule was changed to type a
branch's field binders with the constructor's argument telescope
(`extendTele Γ (ctor-args ct)`) rather than with `tm-hole "field"`, so the ι
substitution lemma relates the field variables to the constructor's real
arguments. The four literal-peel variants additionally use a compact-literal
identification on the `Conversion` record (`tm-ctor "Z" [] ≈ tm-nat_lit 0`,
etc.), mirroring the kernel's `Eval.nat_to_ctor`/`bounded_to_ctor`.

The constructive soundness theorems are **proved**: the fuel-indexed
`soundness-fuel` and the coinductive `soundness-tree`
(`proof/Proof/Soundness.agda`). The classical statement is `soundness-nf`
(`proof/Proof/SoundnessConfluence.agda`), the dichotomy
`Reached ⊎ DivergesNF` over NORMAL FORMS, resting on ONE classical input:
`tree-decides` (the outcome tree is finite or infinite — LPO on the path,
since `progress` is deterministic).

**Correction (confluence slice).** An earlier revision derived a classical
three-way `soundness` from a SECOND input, `never-reached→no-value` (a
never-reaching tree has no reachable value). Confluence of `_⇝_` is now
MECHANISED (`proof/Proof/Confluence.agda`: `confluence : _⇝_`), but it does
NOT discharge that input — the input is **false as stated** for the
mechanised `_⇝_`, which reduces UNDER BINDERS (`ξ-lam-body`). Let
`Ω = (λx. x x) (λx. x x)`; then `Ω ⇝ Ω`, so `tm-lam g d Ω` is a canonical
`Value` that steps to itself, hence `NeverReached` — yet
`tm-lam g d Ω ⇝* tm-lam g d Ω` with `Value (tm-lam g d Ω)`. The statement
would hold only if "value" meant a stuck-free NORMAL FORM (a term that has
finished evaluating), which is strictly stronger than `Value`
(canonical/neutral). See docs/CONFLUENCE.md for the full finding.

**Repair (same slice).** `proof/Proof/SoundnessConfluence.agda` states and
proves the TRUE form of the input over normal forms, with **zero new
postulates**: `never-reached-not-nf` (a never-reaching tree is not a normal
form), `DivergesNF` + `never-reached→divergesNF` (positive divergence), and
`soundness-nf` — the dichotomy `Reached ⊎ DivergesNF`, which leaves
`tree-decides` (LPO) as the only classical input. The false
`never-reached→no-value` and the `soundness` built on it have been
**REMOVED** from `Proof/Soundness.agda`; the development now rests on exactly
two named postulates, `funext` and `tree-decides`. This count does not include
module parameters or conversion record fields. No termination-check
override remains in confluence or elsewhere. The former `LiteralArity` oracle was refuted
and removed from active confluence; its old shape is kept as a negative
regression in `Proof.InterfaceAudit`. Note also that the tempting
strengthening "reaches a NORMAL-FORM value, or diverges" is *not* provable
from `soundness-tree` (a `Reached` leaf supplies only `Value v`, and
`progress⇐` at `v` returns `Value v` again), which is why the first disjunct
stays `Reached`.

---

## 8. Verification status and open obligations

The enforcement and specification results below have different strengths.
Neither passing tests nor counting `postulate` declarations establishes
that an uninhabitable theorem interface is useful.

### Foundational blockers and the migration gate
`proof/Proof/InterfaceAudit.agda` machine-checks these negative results:
- **Coverage — migrated:** the old `Covers` quantified over every branch
  list, including `[]`, and was incompatible with `BuiltinCtors`. It is
  now frozen only in the audit. `Core.Coverage.CaseCoverage` constrains one
  family and branch list; `⇒-case` requires this evidence alongside branch
  typing. Progress and both soundness modules no longer take a global
  coverage parameter. Renaming, substitution, context conversion, and
  branch/scrutinee/motive reduction preservation propagate the local evidence.
- **Conversion — rigid-head migration implemented:** `ReduceConv` makes a
  let reducing to a Π convertible to that Π. The historical raw Π-reflection
  property, now frozen as `RawPiReflection`, would require the raw let to
  have literal Π syntax. Active `Conversion` instead separates two exposed
  type heads (`Core.TypeHeads`) and retains component injectivity for two
  exposed Πs. Head tags preserve exact universe levels and family names.
  Inversion and constructor/literal metadata extraction now recurse over
  arbitrary intermediate types while accumulating conversion witnesses.
  Cumulativity is separate: `⇒-cumul` explicitly closes declarative typing;
  the old `≈-type` field is removed. Progress, preservation, renaming,
  substitution, context conversion and checking inversion are migrated.
  Full formal reduction compatibility is now constructed in
  `Proof.ReductionConversion`, including compact-literal equations.
  **Executable NbE/η correspondence remains open.**
- **Signature oracle — repaired for the closed-entry fragment:** the old
  `ClosedSig` required arbitrary fabricated records to be closed and is now
  frozen only in the audit. `Core.ClosedFragment.ClosedFragmentSig` constrains
  only actual family and constructor members. Preservation's renaming,
  substitution and branch helpers obtain those memberships from lookups;
  the preservation and soundness module parameters are migrated.
  **This is not the full dependent-signature repair:** individual entries
  and constructor results are still required to be closed because the
  current spine/context proofs rely on their renaming/substitution identity.
  The explicit fragment name replaces the previous misleading generality.
- **Literal arities — repaired:** the former `LiteralArity` required every
  raw `Z` branch to have arity zero; a fabricated arity-one branch refutes it.
  Arity constraints
  now belong to the four literal reduction-rule premises in both small-step
  and parallel reduction. Progress derives the witnesses from checked
  branches and builtin telescopes. `Conf` no longer takes this impossible
  parameter. `Proof.LiteralCases` checks valid steps, rejects malformed
  arities in both relations, and instantiates a real confluence peak with a
  concrete closed-body signature. Confluence now has a checked strong
  diamond/closure proof with no termination override; it remains a theorem
  about the formal specification, not executable refinement.

Further correspondence repairs are required: dependent spine tails and
constructor result indices must be instantiated, with parameter filtering
and erased-slot frame handling. Exact-arity closed-entry branches now bind
the last field at zero as the evaluator does. `Certified` currently means only
that unfoldable bodies are `Final` (hole/absurd-free), **not** that they terminate.

**Forward-dependent spine foundation (not broad migration).**
`Core.LocalFrame` now proves that declaration-order pushes implement a
last-field-first simultaneous frame for arbitrary bodies, with parameter
seeding and unchanged outer slots. The candidate `Core.Verification`
operators use this frame and include result parameter/index instantiation.
`Proof.LocalFrame` proves scoped local instantiation stable under ambient
renaming/substitution. `Proof.DependentSpine.Spines.Checked` threads preceding
values and requires entry scope, actual kinding and argument checking.
Its scoping/arity and transport properties are checked; for closed entries
it supplies the existing flat spine rule and a registered constructor example.

Positive dependent/parameterized witnesses and negative type/scope/arity/
kind controls live in `Proof.DependentSpineExamples`. A Type2 counterexample
separates argument checking from declaration kinding: the old flat spine
rule alone does not establish entry validity. Sixteen independent executable
tests kernel-check genuine dependent declarations and positive programs
before evaluation, checking indices, field/ambient order, lambda capture
and parameter seeding. These tests use primitive Atom rather than requiring
the Int facade's builtin bootstrap.

**Active field-order migration — exact-arity closed entries.**
`Core.Reduction.substArgs` now reverses surface fields before simultaneous
substitution. `argsSub` remains an already-de-Bruijn-ordered prefix helper:
local declaration environments must not be reversed again.
`Core.LocalFrame.fields-agree` connects declaration-order pushes directly to
active `substArgs` for arbitrary bodies.

`Core.Typing.branch-context` extends by the reversed telescope, while
`surface-field-vars` reconstructs constructor arguments in declaration order.
Branch arity uses the reversed length definitionally, equal to ordinary
arity by `length-reverse`. Renaming, substitution, context conversion,
finality and all five ordinary/literal ι preservation cases are migrated.
`Proof.FieldOrder` supplies reversal facts; preservation's generic
`contract-fields` reverses checked arguments and closed telescope entries
together, substitutes the body, then restores the surface-order constructor.
Strict-parallel substitution/confluence, literal-expansion simulation and the
inhabited full-conversion/soundness model remain checked.

`Proof.FieldOrderExamples` exercises heterogeneous `Next(Nat, Bounded)`
fields: slot zero has type Bounded, slot one has type Nat, and the latter
cannot check at Bounded even through conversion/cumulativity. Both ordinary
constructor and compact-literal cases preserve typing when returning
`Bounded 7`; a nested lambda retains that field without capture, and the
case transports under weakening. Raw confluence examples distinguish two
Nat values and now select the last field at zero.

This migration retains individually closed entries/results; it does not
admit the genuine dependent constructor through the active rules.
Parameters must be checked separately. The evaluator's parameter-spine
filtering, missing erased-slot frame and full executable refinement remain
outside the proved exact-arity fields-only contract.

**Typed declaration-to-frame bridge — constructed, not admission migration.**
`Proof.DependentInstantiation` adds forward local `Declared` telescopes:
each entry has preceding-binder scope and an actual kind derivation in its
declaration context. `Arguments` checks the actual spine at prefix-instantiated
types without asking again for those kinds. `instantiate` derives both the
existing kind-checked dependent-spine judgment and a coherent substitution
from the final declaration context into the caller.

`coherent-push` realizes a fresh declaration binder by an actual term without
adding a caller binder. Arguments must be final, because checking-only holes
need not infer their types; neither a value nor termination premise is added.
`result-frame` composes checked parameter and field frames, and
`instantiate-result⇒` / `instantiate-result⇐` prove that locally typed terms
AND their types remain typed after parameter-plus-field instantiation.
The proof reuses the current conditional substitution theorem, not an
assumed dependent-preservation law.

The examples include `(A : Type0, x : A)`, two distinct Atom/Float parameters,
computed-index typing/conversion, reducible actual parameters, and closed/open
lambda capture avoidance.
Bad parameter order, kind, scope and arity are rejected; an explicit
checking-only hole demonstrates why finality cannot be inferred from
argument checking. Six additional executable regressions kernel-check
distinct parameter/field frames, dependent/computed result indices, result
parameter uniformity and result-index typing.

This establishes typed LOCAL instantiation over the existing inhabited
closed-signature baseline. The typed-frame theorem alone does not validate
complete result declarations; the next checkpoint adds that local evidence.
It still does not admit dependent global declarations or replace the active
constructor/data/branch rules.

**Local dependent result declarations — evidence and transport constructed.**
`Proof.DependentResult` packages kind-checked parameter/index/field
telescopes, scoped result vectors, field-universe bounds, syntactically uniform
result parameters and kind-checked result spines in `LocalDeclaration`.
`LevelsBelow` refers to actual field-kind derivations, not a raw signature's
`universe-ok`/`positive` booleans. This is local declaration evidence rather
than a verified implementation of the global admission checker.

`ResultSpines` checks parameter vectors before dependent index vectors and
derives exact arities. `subst-result-spines` transports both vectors and
their dependencies through coherent substitution. `uniform-instantiates`
proves that result parameter slots instantiate EXACTLY to supplied
parameters. `instantiate-results` combines those results with the checked
parameter/field frame, producing a whole checked computed-index spine under
the same actual parameters. It reuses existing, inhabited conditional
substitution laws; no dependent-preservation oracle is added.

The examples include `D(A : Type0; x : A, B : Type0, y : B)`, distinct
Atom/Float actual types, computed indices and open caller variables.
Wrong index/parameter types, missing/surplus indices, an undersized field
budget and typed-but-nonuniform parameters have negative controls.
The adapter `active-result-kind` supplies current data formation ONLY when
the family's parameter/index entries are individually closed and a real
lookup succeeds. A registered Bounded example exercises it; the genuinely
dependent local family's closedness requirement is explicitly refuted.

Sixteen independently kernel-checked executable result tests cover
whole dependent/computed result vectors, prior-index dependencies,
well-typed mismatch, arity, uniformity, field universes and scope.
The result theorems still rely on the current closed-signature substitution
infrastructure. The next checkpoint links local certificates to bounded
registered admission without claiming full dependent soundness.

**Base-checked registered admission — a separate bounded layer.**
`Proof.DependentRegistry.Layer base sig conv registry` separates the
closed-entry base used for declaration/argument checking from a fresh
registry containing genuine dependent records. `Registry` requires family
and constructor certificates only for actual lookups, visible constructor
ownership, and identities fresh relative to the base. No universal oracle
over arbitrary fabricated records is introduced.

Its `Application` and `Formation` records are bounded admission judgments,
NOT the active `Core.Typing` relation. They include the checked registry,
actual lookup evidence and argument/result checks. `result-formation`
proves that an admitted constructor application has a checked registered
result; `subst-formation` preserves formation under a coherent BASE caller
substitution. The proof does not require closed dependent registry entries
or assume a new dependent-preservation theorem.

The registry examples instantiate all certificates with registered
ordinary/computed constructors, closed/open callers and caller substitution.
They reject unknown names, missing fields, bad result indices, base-name
shadowing and inconsistent visible ownership. They explicitly REFUTE the
registry's old `ClosedFragmentSig` premise and base typing of its new data
type. This is therefore not a disguised claim of extending the old full
soundness model.

Three executable controls add to the result suite:
lookup/visible-owner agreement, missing registration rejection and rejection
of a same-shaped foreign result family. The layer's freshness policy is
formal evidence, not a proved correspondence with all executable namespace
guards. No kernel/runtime source changes.

Unified dependent global typing, recursive extension/signature validity and
positivity, dependent elimination, broad preservation and implementation
refinement remain open. The new records are also not release certificates:
final actual arguments alone do not imply every declaration/result term is
final. Parameter filtering, erased slots, η, typed erasure simulation and
semantic totality remain separate obligations.

**Registered constructor congruence — fixed-goal preservation constructed.**
`Proof.DependentPreservation` preserves dependent argument checking under a
selected final field's reduction. The changed local prefix converts the
expected types of later fields; this is not an unproved raw-type identity.
Finality is retained, and pointwise frame/substitution congruence proves
the newly computed result type convertible to the original result type.

`CheckedApplication` fixes a checking goal in the bounded registry layer.
`preserve-at` / `preserve-step` keep that exact goal for a selected field
step or any small step from a constructor term. `preserve-star` handles
arbitrary finite constructor paths by structural recursion on the input
path. The proof does not replace the old goal by the newly inferred type,
add a dependent-preservation oracle or assert termination.

Concrete witnesses reduce a type-valued `B` field in
`(x : A, B : Type0, y : B)`. Ordinary/computed constructors, open callers
and a two-step type/value reduction retain their original goals. Raw result
types are explicitly unequal while conversion is proved; unrelated field
replacement and wrong-result-family controls fail.
Five executable regressions check source/intermediate/reduced terms against
ONE original kernel-checked goal and evaluate their values independently.
The result and frame suites each contain sixteen tests.

The new result is operational preservation for this bounded registered
constructor fragment, not dependent case elimination or unified
`Core.Typing` preservation. Recursive extension checking, positivity,
elimination, release certification, evaluator/readback/η refinement,
filtered/erased frames, typed erasure simulation and semantic totality
remain open. No runtime/kernel library source changed.

**Parameter-specialised selected-branch contraction — constructed.**
`Core.LocalFrame.specializeParameters` replaces local parameter slots while
protecting field binders. `Proof.LocalFrame.staged-contraction` proves exact
agreement of parameter specialisation followed by active fields-only
substitution with full parameter-plus-field instantiation, for arbitrary
bodies and open callers. Existing binder-aware composition provides capture
avoidance; the pure push/weakening helper is shared with typed instantiation.

`Proof.DependentBranch.Contract` uses an actual checked registry application
and its local constructor declaration. A body checked in that local
parameter/field context contracts to a term checked at the instantiated
local goal. Final local bodies yield final reducts and corresponding
inference. A separate `selected-step` theorem exhibits ordinary ι with the
constructor's FIELD arity and the parameter-specialised runtime body.
Its motive and other branches are raw syntax, not certified case typing.

Examples cover field projection, parameters replaced rather than captured,
lambda domains/captured fields/own binders, and an open parameter shifted
past fields then restored to its caller slot. Negative controls reject
unspecialised/unprotected slot interpretations and treating parameters as
branch fields.
Ten independent executable tests kernel-check whole positive cases and
compare declaration-frame and fields-only case evaluation, including open
parameters and lambda capture. No kernel/runtime implementation changes.

This is **typed selected-branch substitution and a raw ι witness**, not a
whole-source-case preservation theorem. The next checkpoint constructs the
fresh caller-context bridge; motive/index agreement, coverage and unified
dependent typing remain open, as does proving that elaboration emits the
specified specialisation.
The typed body here lives in the local declaration context, not an arbitrary
fresh caller branch context. Parameter-prefix filtering, missing erased
slots and the remaining erasure/totality/η/refinement obligations are not
established by this result.

**Fresh caller branch contexts — typed opening and closing constructed.**
`Proof.DependentOpening.build` opens fields forwards in the ambient caller,
specialising field types with actual parameters and preceding fresh fields.
It derives exact caller-plus-FIELD context size, not a parameter-plus-field
branch arity. `open-coherent` and `open-kinded` derive the embedding and
field kinds from the actual registered local declaration; `local-to-branch`
types the parameter-specialised local body in the resulting fresh context.

`close-coherent` handles a general ambient substitution and checked actual
field values. Its registered instance `branch-coherent` yields a coherent
fields-only contraction from the fresh context to the caller.
`contract-branch` / `contract-branch⇒` preserve checking/inference for any
body typed THERE, including direct ambient references not expressible in
the local parameter/field-only context. Both the reduct and its dependent
type are substituted; no kinding or dependent-preservation oracle is added.

Concrete witnesses separate caller and field values, protect caller capture
and lambda-local variables, and embed/close open parameter-dependent bodies.
Fresh dependent field types stay symbolic until actual-field contraction.
Two additional executable whole-case tests exercise unrelated ambient
value access/capture; the branch suite now has ten tests.
The frame/result suites retain sixteen each. No kernel/runtime source changes.

This strengthens the selected-branch bridge but does not establish whole
dependent case preservation. Motive/index agreement, coverage, unified
typing and recursive signature validity/positivity remain open, alongside
elaboration/evaluator/readback refinement and the other §8 obligations.

`Core.Coverage` is now connected to the active typing and proof consumers.
`Proof.CoverageExamples` gives concrete Nat coverage in an environment also
containing Bool and Void, without requiring unrelated Bool branches. It
rejects missing Nat/ordinary constructors, wrong arities and wrong-arity
first duplicates, admits empty-family coverage, and exercises coverage after
renaming, substitution and real branch reduction. A typing-level refutation
rejects an empty Nat case even through `⇒-conv` wrappers.

This first coverage interface is deliberately conservative: it requires all
constructors of the scrutinee family, not index-unification-based omission
of impossible branches. The local witnesses are not a verified implementation
of the kernel's indexed coverage checker.

`Core.Verification` and `Proof.VerificationExamples` still contain candidate
scoped dependent telescopes, membership-indexed signature scoping,
reduction-based head exposure and parameter-aware frame operators.
**Dependent admission and exposure remain candidates, not a complete
replacement conversion relation.** The exact-arity field frame is connected
to active substitution as described above. The
coverage examples alone do not instantiate soundness. The separate
`Proof.SoundnessModel` now inhabits the closed-entry theorem parameters,
while dependent signature typing and executable correspondence remain open.
The typing-level missing-case refutation is parameterised by abstract
`Conversion`, without assuming `ReduceConv`.

`Proof.ClosedFragmentExamples` provides an inhabited `ClosedFragmentSig`
with registered Nat/Bool/Void families and a registered global type.
Unregistered open family/constructor records do not obstruct the witness;
registered open parameters, fields and results are rejected. A final
boundary regression shows that a genuinely scoped dependent telescope
inhabits the candidate `ScopedFamily` interface but **cannot** inhabit
this individually-closed-entry fragment. These are signature-invariant
examples, not a full executable soundness-model instance.

`Proof.ConversionModel` supplies an actual inhabitant of **every conversion
record field**, using a structurally terminating ζ-only interpretation.
It proves commutation with renaming/substitution, head separation and Π
component injectivity, using existing function extensionality and no new
postulates or bypasses. Applications are uninterpreted; all constructors
and literals deliberately map to one opaque leaf. This is a non-vacuity
witness, **not faithful value conversion or NbE**.
`Proof.ConversionExamples` exercises inference/checking inversion through
let-wrapped types, constructor/literal family metadata, a registered global
with a let-wrapped type, exact-universe rejection, and upward cumulative
typing without universe equality. It also **refutes full `ReduceConv` for
this witness using a well-typed β redex**. Thus record inhabitation does not
silently become a full preservation/soundness-model claim.

**Full formal reduction conversion — constructed.** `Core.LiteralExpansion`
expands compact Nat/Bounded literals into distinct constructor towers while
preserving all other term structure, values, grades, variables and binders.
It commutes with renaming/substitution and preserves scoping and closed
global bodies. `Proof.ExpansionSimulation` maps EVERY original reduction rule
to a finite path in the expanded signature: β/ζ, ordinary and all literal
ι rules, δ, and all congruences, including arbitrary branch-body paths.
This is representation expansion, not erasure or an NbE algorithm.

`Proof.ReductionConversion` defines equality by a common reduct of expanded
terms. Checked confluence proves transitivity; rigid-head preservation and
Π-path decomposition prove separation and component injectivity. All
conversion fields and full `ReduceConv` for the ORIGINAL signature are
supplied, using closed global bodies and existing function extensionality,
with no new postulates or bypasses. Pointwise substitution congruence uses
structural term induction, not a uniform bound on infinitely many entries.

`Proof.SoundnessModel` jointly inhabits the EXISTING soundness hypotheses:
registered Nat/Bounded families, positivity, local coverage, `BuiltinCtors`,
`ClosedFragmentSig`, body finality, `CertifiedTyped`, the constructed
conversion and full `ReduceConv`. Its finite global table contains a typed
body at a let-wrapped declared type, whose kind is checked. It invokes
actual β/ζ/ι/δ preservation and the constructive fuel theorem.
The formal closed-entry baseline is therefore non-vacuous.
Its BuiltinCtors-compatible Bounded family is explicitly **unindexed**;
it is not the full executable dependent builtin signature.

`Proof.ReductionConversionExamples` rejects unequal Nat/Bounded/Int values,
universe/grade/family confusion and distinct holes. It also explicitly
**refutes η between well-typed open functions in this model**. Thus neither η-aware
executable conversion nor full dependent Cure soundness follows from this
inhabited specification. Filtered/erased-frame correspondence, indexed coverage,
typed erasure simulation, semantic totality and evaluator/readback
refinement remain open.

The postulate guard is supplemented by `proof/scripts/check-hygiene.py`,
which rejects new holes, unreviewed options/postulate blocks, and changes to
the reviewed check-bypass inventory. `Core.Parallel` now contains **no**
termination overrides: generic `⇉*-at-spine` / `⇝*-at-spine` lifters carry
source-alignment equations separately and recurse on the unchanged tail
derivation. All six constructor/data spine wrappers and the complete
parallel-to-small-step simulation are termination-checked. `Proof.SpineLifting`
exercises two real reduction steps at a non-head position, unchanged neighbour
fields/opposite data spines, zero-step paths, symbolic alignment, and simulation.
The guard now forbids any check bypass anywhere in the proof tree.
`Proof.Confluence`'s final override has been eliminated by redesign, not
by assuming termination or another diamond. `Core.StrictParallel` uses only
one-step premises, including branch bodies. `Proof.StrictConfluence` proves
one-step substitution and a strong diamond; `Core.Relation` separately
checks strip/closure recursion on the input paths. Both simulations recover
confluence of the unchanged small-step relation with the original
`ClosedBody` hypothesis. `ξ-case-brs` still admits arbitrary finite body
paths, translated to strict-parallel closure rather than one strict step.
`Proof.ConfluenceExamples` includes β/ζ overlaps, duplication, a newly
exposed branch redex that cannot be compressed to one strict step, distinct
fields/non-head updates, all literal peels and malformed arities, recursive
δ, and normal-form uniqueness. No typing/conversion/termination oracle is
used by this confluence theorem. Full formal conversion compatibility is
constructed above; filtered/erased frames, η and the other implementation
soundness/refinement obligations remain open.

### Item-by-item evidence

1. **Release firewall — implemented and regression-tested.** The ordinary
   and lifted paths route through `Emit.reject_holes/2` (§3.4). Maintain
   coverage when adding compilation/publication entry points.
   *Audited (this slice) — the firewall holds, and the audit's "running hole"
   could not be reproduced.* Findings:
   - Both `Emit` entry points guard: `compile_and_load/2` and
     `compile_forms/3,5` each run `validate_emission_closure` then
     `reject_holes` before any forms are built. `LiftModule.emit/1` routes
     through `Emit.compile_forms/3`, so the lifted (macro-generated) path is
     guarded too.
   - A hole in an ordinary definition is refused: `pub fn probe(x: Int) ->
     Int = ?probe` fails with **E014 / unfilled_hole**
     (`{:codegen_error, {:unfilled_hole, …}}`).
   - A hole in an `actor` handler body is refused **by the same firewall**,
     reached through the lifted path: `LiftModule.emit/1` →
     `Emit.compile_forms/3` → `reject_holes`, surfacing as
     `{:lift_module_error, %{cause: {:unfilled_hole, details}}}` with the
     exact source span of the hole. (An earlier revision of this note said
     actor-body holes were caught only by macro expansion; that was wrong —
     it came from a malformed probe whose body failed for an unrelated
     reason.)
   - **Regression tests added** (`test/cure/elab/emit_hole_firewall_test.exs`,
     3 new tests, 7 total green): the ordinary-definition refusal end-to-end
     through the real compiler; the actor-body refusal asserting the
     `:lift_module_error` → `:unfilled_hole` chain and the hole's source
     span; and a CONTROL asserting a hole-free actor still compiles and
     emits callable functions (`handle_cast/2` returns `{:noreply, 7}`), so
     the refusal cannot be an artifact of broken emission.
   - **A retracted claim, recorded so it is not re-derived:** an earlier
     revision of this note asserted that `actor`/`sup` modules emit NO
     functions at all, based on finding a `.beam` in
     `_build/…/.cure_generations/` that exported only `module_info/0,1`.
     **That was wrong.** `Compiler.compile_and_load/2` deliberately does NOT
     persist bytecode — it only loads into the VM
     (`compile_and_load_units/2` calls `:code.load_binary`). The `.beam` files
     on disk are unrelated artifacts, so inspecting them says nothing about
     what was emitted. Actor emission works:
     `test/cure/compiler/actor_family_raw_test.exs` calls the emitted
     `handle_cast/2`, `init/1`, `start_link/1` and drives a real
     `:gen_server` (5 tests, green).
2. **Certificate verification and semantic termination.** The proposer is
   outside the TCB; the finite SCC and closure verifiers are inside it.
   *Audited (this slice) — the design does NOT trust the proposer, and the
   verifier is tested against forged partitions.* Findings:
   - `TotalityGraph.propose_partition/2` is explicitly untrusted: it only
     *proposes* an SCC partition plus witnesses. `Kernel.validate_scc_certificates/4`
     first calls `SCCCertificate.verify_partition/2`, which **re-derives the
     edge set from the environment** (`Env.direct_call_summary`) rather than
     trusting `certificate.edges` — so a proposer cannot hide a call edge
     (`:direct_edges_mismatch`).
   - The verifier independently enforces: universe/domain agreement, no
     duplicate or missing members, canonical component ids, a strict
     topological rank (`:rank_not_decreasing`), and spanning forward+reverse
     trees inside each component (`:tree_edge_count`, `:tree_not_spanning`).
     A shrunken universe is caught with the omitted callee and a verified
     path (`:totality_scc_incomplete`, e.g. `verified_path: [:a, :b]`).
   - **The SCC-splitting attack is closed by the rank check.** Splitting a
     genuine cycle `a -> b -> a` into singleton components would make each
     look trivially terminating. Ranks must be a permutation of `0..n-1`
     (`:rank_not_total`), and every inter-component edge must be strictly
     rank-decreasing — which no distinct rank assignment can satisfy for a
     2-cycle, in either orientation. So the verifier re-derives mutual
     reachability from the edges alone. Verified for both `%{a: 0, b: 1}`
     and `%{a: 1, b: 0}`.
   - New tests: `test/cure/core/scc_certificate_tamper_test.exs` (6 tests)
     forge partitions directly, bypassing `TotalityGraph`, and assert each is
     rejected **for the intended reason** (not merely "some error"), so the
     tests cannot pass vacuously. The existing
     `totality_certificate_property_test.exs` covered only the honest path.
   - **The size-change matrices ARE verified — an earlier revision of this
     note wrongly said they were assumed.** `Cure.Core.TotalityCertificate.verify/3`
     is a trusted verifier that: derives the expected base matrices from
     `Env.direct_call_summary` (independent of the candidate, so a proposer
     cannot submit a wrong base edge — `:invalid_base_derivation`); replays
     every `{:compose, left, right}` derivation by recomputing
     `SizeChange.compose_edges` and requiring `same_edge?`
     (`:composition_mismatch`); rejects cyclic derivations
     (`:cyclic_derivation`); and checks saturation — every composable pair of
     edges must have its composite present (`:closure_not_saturated`). It then
     rejects **any idempotent self-edge without a smaller diagonal**
     (`{:not_total, …}`); finding just one decreasing loop is not sufficient.
   - **The real residual is the TERMINATION THEOREM, not the matrices.** The
     verifier establishes "this closure is saturated and every idempotent
     self-edge has a smaller diagonal". That this implies termination is the size-change
     principle itself, together with sound semantic descent extraction.
     Contrary to an earlier claim, Agda's `Certified` supplies only body
     finality, not termination. So §8.2 is narrowed to: SCC discovery is verifier-checked
     and tamper-tested, matrix composition and saturation are verifier-checked,
     and the size-change *principle* remains an assumed theorem.
3. **`Erase.erase` preserves the operational semantics.** Erasure is assumed to
   drop only `:erased`-graded binders, which the relevance check enforces — but
   the argument here does not prove erasure commutes with reduction.
   *Partial executable evidence (β, ζ, ι).* `test/cure/elab/erase_test.exs`
   contains independent β substitution comparisons, let-collapse regressions,
   and shape checks. The ζ/ι tests now evaluate erased original redexes
   independently; the selected congruence tests reduce the erased subterm
   rather than rebuilding it from the source reduct. These bounded raw-term
   examples are not an operational preservation proof:

   `test/cure/elab/erasure_simulation_test.exs` additionally kernel-checks
   source definitions and compares their original Core evaluation with
   independently emitted/executed BEAM. It covers direct/nested lets,
   distinguishable first/last case fields, local global calls, and an erased
   function parameter whose runtime arity shrinks. The source oracle does
   not call erasure. These examples do not prove a universal simulation or
   preservation of divergence.

   - **β** (`describe "erasure commutes with β-reduction"`, 3 tests): an
     erased argument, a present argument through an identity body, and a
     nested redex;
   - **ζ** (`describe "erasure commutes with ζ-reduction"`, 2 tests): the
     administrative identity `let x = v in x`, which erasure collapses to
     `erase(v)`, and a non-identity `let` whose binder erasure KEEPS (the
     value must still be evaluated once);
   - **ι** (`describe "erasure commutes with ι-reduction"`, 2 tests): a case
     on a nullary constructor, plus a test pinning that `erase` does NOT
     perform ι — it keeps a `:runtime` case and erases only inside it (a
     COLLAPSIBLE case, whose sole constructor's fields are all erased, is the
     one that is dropped).

   Running them pinned three facts worth recording: `erase` **recurses into
   an application's argument**; `erase` does **not** perform β or ι (it
   preserves `{:app, {:lam, …}}` and `:runtime` cases); and the erased-field
   dropping depends on `ctor_quantities` being available, so the tests build a
   real env rather than using `Env.empty()`.

   - **δ — a NEGATIVE result, and the most substantive finding here.** δ does
     NOT commute with erasure, and must not be expected to. Erasure drops an
     argument when the *callee's signature* marks that position erased; after
     δ the callee is gone (the head is the body), so those positions can no
     longer be identified. Concretely: `certified_prim` takes two `:erased`
     parameters, so erasing the CALL `certified_prim(cs)(es)` drops both and
     yields `{:global, :certified_prim}`; but its body `prim` is NULLARY, so
     erasing the UNFOLDED form treats the two arguments as over-application
     and keeps them. Two tests pin this (`describe "erasure and
     δ-reduction"`).
     *Scope correction:* this fixture inserts an unchecked declaration with
     a non-function body at a function type. It refutes a raw-syntax equality,
     not a well-typed source/runtime simulation. The emitter calls
     `Erase.erase(env, body)` directly in `real_function_form/3`; neither
     complete prior unfolding nor a single erasure pass may be assumed.
     The required theorem relates checked source execution to an erased
     program/signature with its runtime arities and branch environment.

   - **Congruence cases** (`describe "erasure is a homomorphism over the term
     formers"`, 4 tests): the ξ-rules reduce a SUBTERM, and erasure recurses
     structurally into exactly those positions. The tests assert the
     homomorphism property directly — reducing a subterm then erasing equals
     erasing the whole term then reducing the corresponding erased subterm —
     for `app` (argument position), `lam` (body), `data` (spine element), and
     `effect_bind` (effect position). These are selected structural checks,
     not coverage of every ξ-rule or an independently executed simulation.

   **MECHANISED (new): `proof/Proof/Erase.agda`.** The Agda tree previously
   had no `Erase` module; it now has one, and it is in `check.sh`:

   - `eraseTerm` formalises structural recursion **with administrative let
     collapse**: a let whose **erased body** is variable zero becomes its
     erased value; surviving lets receive the unrestricted runtime grade.
     These are the executable eraser's let rules.
   - `erase-idem` — this structural erasure with let collapse is idempotent
     (`eraseTerm ∘ eraseTerm ≡ eraseTerm`), PROVED with **no new postulates,
     holes, or termination overrides**. `letStep-fixed` proves directly that
     the Boolean-dispatched let constructor preserves fixed points, then the
     term induction applies it to already-erased components.
   - Definitional (`refl`) regressions cover identity collapse, nested collapse
     exposed only after erasing the body, and surviving nonzero-variable
     bodies with grade normalisation.

   **Corrections to the earlier proof diagnosis.** A missing `Data.Nat.zero`
   import previously made `tm-var zero` bind a fresh variable rather than
   match index zero. That was not a failure of mutual recursion. A later
   proposed bridge, `isVar0 b ≡ false → isVar0 (eraseTerm b) ≡ false`, is
   **false**: `let y = var 0 in y` is not a variable, but erases to variable
   zero. The correct test is on the erased body, and the fixed-point proof
   aligns its second pass using body idempotence rather than transporting
   that invalid bridge.

   **What the mechanisation still omits.**
   - Signature-dependent constructor/global argument filtering and its arity
     guards. `eraseSpine` filters a supplied quantity vector (keeping excess
     arguments), but is **not called by `eraseTerm`**. Constructor arguments
     are recursively erased without filtering in `eraseTerm`. Consequently,
     `erase-idem` does **not** prove idempotence of the full executable
     `Erase.erase/2`, nor of applying `eraseSpine` twice with the same vector.
   - the kernel's heuristic refinements (collapsible-family case elimination,
     convoy discharge, the `cure_erased` placeholder) — optimisations whose
     correctness is a separate obligation.

   **Still not mechanised:** operational preservation. The target must account
   for erased signatures, binders and runtime representations. The tests
   provide bounded evidence; the unchecked δ fixture does not refute a
   properly formulated typed simulation theorem.

4. **The effect fragment is inert.** `{:effect_type,_}` / `{:effect_pure,_}` /
   `{:effect_bind,_,_}` have zero reduction rules by design (§1.1), so they
   cannot break Preservation — but a future monad law would have to be
   re-argued. **Closed for the present Core specification:**
   `Proof.EffectInert` proves single-step inversion and arbitrary finite-step
   preservation of all three effect heads, with child reductions tracked.
   These proofs use none of the refuted typing/conversion/coverage hypotheses.
   `test/antigen/assays/effect_inert_test.exs` independently pins executable
   skeleton preservation, payload normalisation, and rejection of monad laws.
   This does not verify runtime execution of effectful BEAM code.
5. **η and proof irrelevance.** Cure's NbE conversion DOES perform η:
   `Conv.conv_struct?/4` (`lib/cure/core/conv.ex`) compares a `vlam` against a
   non-`vlam` by applying both to a fresh neutral (`eta_eq?/4`), and compares
   `vlam` against `vlam` by grade equality plus the same η test.
   *Open implementation correspondence.* The repaired `Conversion` record
   (`proof/Core/Typing.agda`) has **no** η field — no `≈-lam` congruence and
   no "λ x. f x ≈ f" rule. The new common-reduct model supports FULL
   formal reduction and compact literals, but explicitly rejects a neutral
   function η equation. It is not an executable conversion refinement. Merely
   adding more equalities does not automatically preserve type safety.
   Closing this item requires a coherent declarative conversion relation,
   η-aware head/injectivity and substitution proofs, and refinement of
   `Eval`/`Quote`/`Normalise`/`Conv`. Checker soundness, completeness, and
   termination are distinct obligations. Definitional proof irrelevance is
   not established by proof erasure; no blanket such rule was found in the
   inspected executable conversion.

---

## 9. Executable evidence

The full implementation theorem is not mechanised, but it is not untested. Each lemma has a
property-based assay that generates known-label cases and asserts the kernel
agrees. The mapping:

| Lemma / side condition | Executable evidence |
|---|---|
| Progress (§2) | `MetaCheck.progresses?/2`; `Antigen.Assays.KernelLaw` |
| Preservation (§4) | `MetaCheck.type_preserved?/2`; `Antigen.Assays.Conv` |
| β agrees with substitution | `Antigen.Assays.Elab`; `beta_subst` generator |
| Strict positivity (§3.1) | `Antigen.Assays.Positivity` |
| Totality gates δ (§3.2) | `Antigen.Assays.Totality`, `TotalityClosure`, `DeltaReduce` |
| Conversion reflexivity ⟺ normalization | `reflexivity` assay (the sharpest δ probe) |
| Coverage / branch unification (§3.3) | `Antigen.Assays.BranchUnify`, `Indexed`, `DotForcing` |
| Hole firewall (§3.4) | `test/cure/compiler/dependent_codegen_test.exs:51`; `Validator` release-config tests; `E014` suite |
| Serialization round-trip | `Antigen.Assays.Serialization` |
| Idris parity | `test/oracle/` differential harness (~30 rows) |

Antigen is a *fuzzer*, not a proof: it can find counterexamples but cannot
establish the theorem. Its value here is that it turns each lemma into a
runnable, falsifiable claim, and its shape-coverage manifest (~98.6% reachable
kernel lines) bounds how much of the kernel the evidence actually exercises.

---

## 10. Summary

The kernel is a bidirectional checker for a three-universe dependent type theory
with graded Π, indexed inductive families, a dependent eliminator, and inert
effects, where type equality is decided by NbE conversion, case elimination is
driven by first-order index unification, and δ-reduction is gated behind a
size-change totality certificate. This document argues that it is sound —
Progress and Preservation for the Core calculus — **conditional on** three side
conditions (strict positivity, totality-gated δ, coverage), each enforced in
code and each tested by an Antigen assay. Some syntactic/algebraic results are
mechanised. Four historical interfaces are refuted and frozen; their active
replacements now admit a joint formal closed-entry soundness instance with
full reduction conversion, not a joint EXECUTABLE soundness model.
§8 records the remaining dependent-signature and refinement obligations.

The honest headline: **the inspected executable paths have passing regression
evidence; formal results include checked confluence, structural erasure
idempotence, effect inertness and an inhabited closed-entry soundness model.
Full executable kernel soundness is not yet certified by this Agda tree.**
