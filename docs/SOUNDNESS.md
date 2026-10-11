# Soundness of the Cure Core Kernel

**A written soundness argument for the trusted dependent-type kernel.**

Status: draft for review.
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
- **It is not mechanised.** See §7.

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

The residual questions are (a) whether *every* codegen path routes through
`reject_holes/2`, and (b) whether the audit's repro exercised `cure check`
(which, by design, *passes* a file containing holes — only `cure compile`
reports `E014`; see `PROOFS.md` §3.7) rather than `cure compile`. §8 records
these as open verification items, not closed ones.

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
2. **Certificates are genuinely valid.** The kernel verifies the *finite*
   size-change certificates (`SizeChange.valid?`), but the SCC discovery and
   transitive closure that *produce* them live outside the TCB
   (`Cure.Elab.TotalityGraph`). A bug there could hand the kernel a certificate
   that verifies as a matrix yet does not correspond to the real call graph.
   This is the single largest assumption in the argument (§8).
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

This argument is written, not machine-checked. The obstacles, in rough order of
difficulty:

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
the renaming/substitution lemmas, **Progress**, and — with the three side
conditions carried as hypotheses — **the constructive, fuel-indexed soundness
theorem** `soundness-fuel`:

```agda
soundness-fuel : ∀ (n : ℕ) {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → FuelResult t T
```

It runs the type-safety induction for `n` steps and returns either a reached
value (with its type, value witness, and multi-step reduction) or "fuel
exhausted", consuming Progress, Preservation, and `Final`-preservation. The
classical three-way statement §1.4 remains a `postulate`: its `diverges`
disjunct is a negative statement, so deciding it needs coinduction (or a
well-founded measure) — the fuel-indexed theorem is its constructive content,
with the `reached` outcome inhabiting the classical first disjunct.

---

## 8. Open verification items

These are honestly *not* settled by this document. They are the places a
determined adversary should look first.

1. **Every codegen path routes through `reject_holes/2`.** The firewall is
   implemented (§3.4), but the audit reproduced a running hole. Confirm by
   inspection that no emission path bypasses `Emit.reject_holes/2`, and add a
   regression test asserting `cure compile` fails on a reachable `?goal` (the
   audit's §5.2 recommendation).
2. **Certificate generation is sound.** §5.3(2): the SCC closure in
   `Cure.Elab.TotalityGraph` is outside the TCB. A bug there is invisible to the
   kernel. This is the highest-value item to audit or move into the TCB.
3. **`Erase.erase` preserves the operational semantics.** Erasure is assumed to
   drop only `:erased`-graded binders, which the relevance check enforces — but
   the argument here does not prove erasure commutes with reduction.
4. **The effect fragment is inert.** `{:effect_type,_}` / `{:effect_pure,_}` /
   `{:effect_bind,_,_}` have zero reduction rules by design (§1.1), so they
   cannot break Preservation — but a future monad law would have to be
   re-argued.
5. **η and proof irrelevance.** If Cure's NbE has η-laws or definitional proof
   irrelevance, they are not covered by this argument and need an η-aware
   treatment (Antigen research synthesis §3.2, #8/#9 gap).

---

## 9. Executable evidence

The argument is not mechanised, but it is not untested. Each lemma has a
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
code and each tested by an Antigen assay. The argument is written, not
mechanised; §7 scopes the mechanisation, and §8 lists the items a mechanised or
adversarial audit should attack first.

The honest headline: **the kernel is sound in the cases that have been tested,
and the argument for why it is sound in general is now written down where it can
be attacked.**
