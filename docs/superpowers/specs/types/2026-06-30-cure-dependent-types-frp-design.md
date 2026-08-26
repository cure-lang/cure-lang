# Cure Dependent Types for Safe FRP — Design (Slice 1)

**Status:** Draft for review
**Date:** 2026-06-30
**Repo of implementation:** `cure-lang/` (the Cure compiler, Elixir)
**Companion audit:** [`docs/CURE_DEPENDENT_TYPES_AUDIT.md`](../../CURE_DEPENDENT_TYPES_AUDIT.md) — establishes that today's Sigma/Pi/`Eq`/proof/holes/totality features are faked (dead modules, no checker integration); only refinement types + Z3 and `assert_type` are real.

---

## 1. Why

The audit found that Cure's advertised dependent-typing layer is an "island": well-written, unit-tested Elixir modules (`sigma.ex`, `pi.ex`, `equality.ex`, `dependent.ex`, `holes.ex`, `reduce.ex`) that the real type checker never calls, with surface syntax that often does not parse and indices erased to `Any`. We want to replace that façade with a **genuinely sound** dependent type system.

The goal is not "dependent types in the abstract." It is a **concrete, falsifiable target**: implement enough of a dependent type theory to host Sculthorpe & Nilsson, *Safe Functional Reactive Programming through Dependent Types* (ICFP'09) — the FRP type system they embedded in Agda — in Cure. That dovetails with the signal/Reactor/FSM work already underway in this repo: the payoff is FRP networks whose well-formedness (no ill-formed feedback loops, proper initialisation, productivity) is **statically guaranteed**.

## 2. Target and acceptance criterion

The paper's safety result is stated plainly: *"as it passes the Agda type, coverage and termination checks, we know the operational semantics is total, which means our type system is safe."* Safety comes from **typechecking + coverage + termination**, not from hand-written equality proofs.

**Program-level acceptance criterion:** port the paper's Agda development to Cure and have Cure accept it under the same type/coverage/termination checks. The ported FRP library then ships as a Cure stdlib module.

### What the paper actually requires (and does not)

Requires:
- **Indexed inductive families (GADTs)** whose constructors compute their indices. The core is `data SF : SVDesc → SVDesc → Dec → Set`, with e.g. `_∗∗_ : … → SF (as ++ bs) (cs ++ ds) (d₁ ∧ d₂)`.
- **Type-level total functions + definitional equality** (`_∧_`, `_∨_` on `Dec`; `_++_`, `map` on lists). The checker must *evaluate* these and decide equality by reduction.
- **Dependent function types** with **implicit, inferred, erased** arguments (`∀ {as bs cs} → …`).
- **Dependent pattern matching** (the operational-semantics step function matches on `SF` constructors, refining indices).
- **Two universe levels** (`SigDesc` stores a `Set`, so `SigDesc : Set₁`; footnote 2 of the paper).
- **Totality (coverage + termination)** as the safety mechanism.

Does **not** require:
- Propositional `Id`/`refl`/`rewrite`/`J` as a core feature (safety is from coverage+termination, not proofs). We add only a *minimal* `Eq` escape hatch (§4).
- **Sigma dependent pairs** are *not* needed by the paper (every product in it is non-dependent) — but they are **included in Slice 1 anyway** (§4.7, §6) so that retiring `sigma.ex` forfeits no capability. (The audit's focus on Sigma was the wrong axis for the *target*; indexed families are the real need.)
- **Holes** (`?`/`??`) are likewise not a paper requirement, but are **included in Slice 1** so retiring `holes.ex` forfeits no capability.
- Universe polymorphism, cubical machinery, or SMT-for-indices (indices are inductive, decided by reduction, not Z3).

## 3. Locked design decisions

| Area | Decision |
|---|---|
| Paradigm | Bounded Agda-subset of **intensional MLTT** (not F\*/SMT; not a general prover) |
| Core features | Indexed inductive families w/ computed indices; dependent `Pi` + implicit (inferred, erased) args; **dependent pairs (`Σ`)**; dependent pattern matching with index unification; **holes** (`?`/`??` goal reporting) |
| Equality | **Definitional** (conversion) first; **minimal sound propositional `Eq` + `rewrite`/`subst`** escape hatch (`refl` accepted only when both sides reduce-equal) |
| Type-level computation | Real evaluator (**NbE**), runs total user functions like `++`/`map` |
| Universes | **Small fixed predicative hierarchy** `Type₀ : Type₁ : Type₂` with **cumulativity**; levels inferred (you write `Type`). Sound (consistent + strongly normalizing). No universe polymorphism yet. |
| Erasure | **Checked `{0,ω}` erasure** (the non-linear fragment of QTT): type-level data, implicits, and `Eq` proofs are `0` (erased) and *checked* never to be used in a computationally-relevant position; everything else is `ω` and ships. The linear `1` multiplicity and usage-counting are **not** adopted (no compelling BEAM user story — see §3.1). |
| Totality | **Targeted**: required (hard error) for functions used at the type level or marked `@total`; runtime code may stay partial. Certificates gate δ-reduction so conversion always terminates. |
| Architecture | **Trusted Core kernel** (`Cure.Core`) + **untrusted elaborator** (`Cure.Elab`). Surface elaborates to explicit Core; the kernel re-checks. |
| Conversion | NbE with **β, ι, δ (certified defs only), η** (for `Pi`). |
| Refinement+Z3 | Unchanged and **orthogonal** — value-level numeric constraints; not used for index equality. |
| Staging | **Paper-driven vertical slice.** Build each mechanism only as far as the next paper fragment needs, end-to-end, then widen. |

### Why `Type : Type` was rejected

`Type : Type` is Girard-inconsistent: (a) it makes the embedded logic prove `False`, poisoning the `Eq` escape hatch; and (b) more practically it loses strong normalization, so NbE conversion can loop and **type checking becomes undecidable**. Targeted totality would *mostly* plug the hole, but that makes soundness contingent on the totality checker being exactly right — too fragile for the stated bar. The paper itself used Agda's `--type-in-type` only "for clarity" and notes it ports to a predicative hierarchy. A small fixed cumulative hierarchy restores consistency + normalization and gives the `Set`/`Set₁` separation the port needs, without the cost of full universe polymorphism.

### 3.1 Why no linearity (the `{0,ω}` choice)

We adopt erasure (`0`/`ω`) but not the linear `1` multiplicity, because BEAM specifically blunts linearity's usual payoffs:
- **Performance / in-place mutation** — linearity's classic win — is largely moot: BEAM is immutable, copies terms across processes, and GCs per process; there is no user-level destructive update to make safe.
- **Aliasing control** is moot: no cross-process aliasing (messages are copied), and within-process immutability makes aliasing harmless.
- **Resource handles** (sockets, ETS, and — relevant here — ESP32 GPIO/UART/I2C) are a *real* but modest story, and it is partly subsumed by process lifetime + supervision, and largely coverable by an `fsm` that *owns* the peripheral.
- **Session-typed actor protocols** are the one genuinely compelling BEAM story — but (a) Cure's `fsm`/`actor` containers already encode protocol state in their types non-linearly, (b) full session types are a separate research program *layered on* linearity (the `1` multiplicity is only the substrate), and (c) none of it is needed by the FRP target.

So `1` buys nothing for the target and little for Cure that FSMs don't already approximate. The Core/elaborator keep multiplicities as an explicit, if currently 2-point (`{0,ω}`), lattice so `1` can be slotted in later if Cure ever commits to first-class session types.

## 4. The Core calculus (implementation-independent spec)

This section is **commitment #1** of the kernel-trust strategy (§9): the source of truth that any reimplementation (the Cure self-host; a future proof-assistant formalization) must conform to. The Elixir kernel conforms to *this*, not vice versa.

### 4.1 Syntax (Core terms, fully explicit)

```
ℓ  ::= 0 | 1 | 2                          -- universe levels (fixed, small)
t,A,B ::=
   | Type ℓ                                -- universe
   | x                                     -- variable (de Bruijn in impl)
   | Π (x : A). B   | λ (x : A). t | t u   -- dependent functions
   | Σ (x : A). B   | (t , u) | t.1 | t.2   -- dependent pairs (§4.7)
   | D ā ī                                 -- family D applied to params ā, indices ī
   | c t̄                                    -- data constructor
   | case t of { c x̄ → uᵢ } : M            -- dependent eliminator with motive M
   | f                                      -- reference to a global def
   | Eq A a b | refl a | rewrite e at (x.M) in t  -- minimal propositional equality (§4.5)
```

Implicits, erasure annotations, and **holes** exist only in the **surface/elaborator**; Core is fully explicit, fully relevant, and hole-free (a checked program contains no holes). Erasure (§8) happens *after* kernel checking.

### 4.2 Contexts and judgments

```
Γ ⊢ t : A          -- t has type A in Γ
Γ ⊢ A : Type ℓ     -- A is a well-formed type at level ℓ
Γ ⊢ t ≡ u : A      -- t and u are definitionally equal at A
```

### 4.3 Universes and cumulativity

```
─────────────────────         Γ ⊢ A : Type ℓ
Γ ⊢ Type ℓ : Type (ℓ+1)       ───────────────── (cumulativity)
                              Γ ⊢ A : Type (ℓ+1)

Γ ⊢ A : Type ℓ₁   Γ, x:A ⊢ B : Type ℓ₂
─────────────────────────────────────── (Π lives at the max level)
Γ ⊢ Π(x:A).B : Type (max ℓ₁ ℓ₂)
```

`max` over the fixed set `{0,1,2}`. Level 2 is the ceiling; a program needing `Type₃` is a (rare) error for this slice.

### 4.4 Indexed families

A family declaration introduces
```
data D (p̄ : P̄) : (ī : Ī) → Type ℓ where
  cⱼ : (ā : Āⱼ) → D p̄ s̄ⱼ          -- s̄ⱼ are index *expressions* over p̄, ā
```
Parameters `p̄` are fixed across all constructors; indices `ī` may vary and may be **computed** in each constructor's result (`s̄ⱼ`). Typing of a constructor application checks `ā` against `Āⱼ` and yields `D p̄ s̄ⱼ` with `s̄ⱼ` evaluated by NbE. (Strict positivity is required; checked structurally.)

The **dependent eliminator** (`case … : M`, the construct §12 keeps in Core for the kernel to check) is typed against a motive `M` that abstracts over the indices and the scrutinee. With `D` declared as above:
```
Γ ⊢ t : D p̄ ī
Γ, (ȷ̄ : Ī), (x : D p̄ ȷ̄) ⊢ M : Type ℓ
for each constructor  cⱼ : (āⱼ : Āⱼ) → D p̄ s̄ⱼ :
    Γ, (āⱼ : Āⱼ) ⊢ uⱼ : M[s̄ⱼ/ȷ̄, (cⱼ āⱼ)/x]
─────────────────────────────────────────────────── (dependent case)
Γ ⊢ case t of { cⱼ x̄ⱼ → uⱼ } : M  :  M[ī/ȷ̄, t/x]
```
(`p̄` = the family's parameters, `āⱼ` = constructor `cⱼ`'s arguments, matching the declaration convention above.)
Each branch is checked under its constructor's telescope with the index variables `ȷ̄` instantiated to that constructor's computed indices `s̄ⱼ` (this is the index refinement the elaborator's pattern compiler discharges via unification, §5); the eliminator's result type is `M` at the scrutinee's actual indices `ī` and `t`. Branches whose `s̄ⱼ` fail to unify with a reachable index are *impossible* and omitted (coverage, §7).

### 4.5 Definitional equality (conversion)

Conversion is decided by **normalization by evaluation**: evaluate to weak-head/whole normal forms over a value domain with neutral terms, then compare by read-back. Reduction rules:
- **β**: `(λx.t) u ⇝ t[u/x]`
- **ι**: `case (cⱼ ā) of {…cⱼ x̄ → uⱼ…} ⇝ uⱼ[ā/x̄]`
- **δ**: `f ⇝ body(f)` **only if `f` carries a totality certificate** (§7). Uncertified globals are opaque (neutral).
- **η**: `t ≡ λx. t x` at `Π` types.

Because δ is gated on certified-total definitions and β/ι terminate on well-typed terms in a normalizing hierarchy, conversion checking terminates.

### 4.6 Minimal propositional equality

```
Γ ⊢ A : Type ℓ   Γ ⊢ a : A   Γ ⊢ b : A
───────────────────────────────────────  (Eq formation — homogeneous, at A's level)
Γ ⊢ Eq A a b : Type ℓ

Γ ⊢ a : A    Γ ⊢ a ≡ b : A
────────────────────────────         refl is well-typed at Eq A a b
Γ ⊢ refl a : Eq A a b                ONLY when a ≡ b definitionally (NbE).

Γ ⊢ e : Eq A a b    Γ, x:A ⊢ M : Type ℓ    Γ ⊢ t : M[a/x]
──────────────────────────────────────────────────────────  (transport / subst)
Γ ⊢ rewrite e at (x.M) in t : M[b/x]
```

The motive `(x.M)` is carried **explicitly** in the Core term (like `case … : M`), keeping Core fully explicit: the kernel does not reconstruct which occurrences to abstract — that ambiguous higher-order choice is the elaborator's job (§5), and the kernel merely re-checks the supplied motive.

This is the escape hatch for index equations reduction can't settle (e.g. `++` associativity). It is genuinely sound (`refl` is *not* the "any atom inhabits any Eq" rule the audit found). `Eq`, `refl`, and `rewrite` are erased at runtime.

### 4.7 Dependent pairs (Sigma)

Not required by the FRP target, but in Slice 1 for capability parity with the retired `sigma.ex` — and free to add given `Π` (it is its dual).

```
Γ ⊢ A : Type ℓ₁    Γ, x:A ⊢ B : Type ℓ₂
─────────────────────────────────────── (Σ formation)
Γ ⊢ Σ(x:A).B : Type (max ℓ₁ ℓ₂)

Γ ⊢ a : A    Γ ⊢ b : B[a/x]              Γ ⊢ p : Σ(x:A).B    Γ ⊢ p : Σ(x:A).B
───────────────────────────── (intro)   ──────────────── ──────────────────── (projections)
Γ ⊢ (a , b) : Σ(x:A).B                   Γ ⊢ p.1 : A         Γ ⊢ p.2 : B[p.1/x]
```

Conversion adds the ι-rules `(a,b).1 ⇝ a`, `(a,b).2 ⇝ b` (η optional). A **non-dependent** pair is the special case where `B` ignores `x` (recovering the plain products the paper uses). At runtime a pair lowers to a 2-tuple; purely type-level `Σ`s erase. Dependent pattern matching (§5) binds both components, with `B`'s dependency on the first.

## 5. Architecture

```
 surface .cure
   │  lex / parse  (existing front-end, extended)
   ▼
 Cure.Elab  (UNTRUSTED)
   │  · bidirectional check/infer
   │  · implicit inference via metavariables + Miller-pattern unification
   │  · dependent-pattern compilation → Core case trees (+ coverage); Σ pairs/projections
   │  · totality closure: mark type-level fns, require & certify totality
   │  · holes: parse ?/?? → report goal type + local context (:hole_goal)
   ▼
 Cure.Core terms  (explicit, typed, serializable)   ← commitment #2
   │
   ▼
 Cure.Core kernel  (TRUSTED, small)
   │  · check / infer   · NbE conversion   · certificate checking
   ▼
 erase  →  existing Cure codegen  →  BEAM
```

The **trusted surface** is exactly: `kernel.ex` (`check`/`infer`), `conv.ex` (NbE conversion), and certificate validation. Everything clever and fallible (inference, unification, pattern compilation) lives in the untrusted elaborator and is re-checked by the kernel (de Bruijn criterion).

### 5.1 Module layout

New, trusted — `lib/cure/core/`:
- `term.ex` — Core syntax (de Bruijn).
- `value.ex` — NbE values + neutrals.
- `eval.ex` — evaluator (β/ι/δ).
- `conv.ex` — conversion + read-back + cumulativity/η.
- `universe.ex` — levels, `max`, cumulativity.
- `context.ex` — typing contexts.
- `kernel.ex` — `check`/`infer`, family/constructor checking, `Σ`/pair rules, certificate validation.

New, untrusted — `lib/cure/elab/`:
- `elaborator.ex` — bidirectional surface → Core.
- `unify.ex` — metavariables, Miller-pattern unification.
- `patterns.ex` — dependent pattern compilation + coverage (extends `pattern_checker.ex`); `Σ` pair patterns.
- `implicits.ex` — implicit insertion + erasure marking.
- `holes.ex` — recognise surface `?`/`??`; emit `:hole_goal` (goal type + local context). Replaces the retired `types/holes.ex`.

Reused: `lib/cure/types/totality.ex` and `lib/cure/types/pattern_checker.ex` (wired in at last — their termination/coverage *decision procedures* are invoked by the kernel during certificate validation and so count as **trusted** when used that way, see §7; the elaborator's only role is the untrusted closure walk that decides *which* functions to submit), `lib/cure/compiler/codegen.ex`, the refinement+Z3 layer (untouched).

Retired (replaced by Core/Elab; their intent reborn soundly): `types/sigma.ex`, `types/pi.ex`, `types/equality.ex`, `types/dependent.ex`, `types/holes.ex`, and `types/reduce.ex` (superseded by `core/eval.ex`).

### 5.2 Reference implementations

We build each kernel/elaborator part against three battle-tested implementations rather than inventing from scratch. **The workflow is continuous**: when implementing a part, first read the corresponding reference file(s), then write Cure's version. Curated snapshots (pinned to upstream commits) live in [`reference/`](../../../reference/MANIFEST.md); the full part-by-part file mapping is in that manifest.

Division of labor, by concern:
- **Idris 2** (`~/Develop/Idris2`, BSD-3) — closest *holistically*: untrusted elaborator → explicit `TT` core → checker → erase → runtime backend; pragmatic `total`/`partial` totality; erasure. Our primary reference for architecture (J), totality (G), pattern/case trees (E), unification (F), holes (I), and the `Eq`/`rewrite` elaboration (K).
- **Lean 4** (`~/Develop/lean4`, Apache-2.0) — the **trusted-kernel** exemplar: a small, independently re-checkable kernel. Primary reference for the kernel's term/defeq core (A, B) and for **universes/levels/cumulativity** (C), where Idris is weak. Its independent re-checkers are the model for our Phase 2 oracle.
- **Agda** (`~/Develop/agda`, BSD-3) — the literal host of the target paper. Primary reference for **dependent pattern matching + index unification + coverage** (E) — its LHS unifier (`Rules/LHS/Unify.hs`) and `Coverage.hs` are the closest match to what the FRP port needs.

Two standing caveats (also in the manifest): **don't import Idris's QTT multiplicities** (we deferred quantitative typing — read its core as ω-except-erased), and **don't copy Idris's permissive universe handling** (follow Lean's `level.*` for our fixed cumulative hierarchy).

## 6. Slice 1 scope

The smallest fragment of the paper that forces every foundational mechanism into existence: **construct a sequential composition and run one evaluation step.**

**Must typecheck (and, for the `compose`/`step` core, run one evaluation step):** the `compose` construction plus `step` must construct and execute one step end-to-end; `forget_dec`/`recover` (Σ) and `sketch` (hole) need only *typecheck* — `sketch` in particular carries a hole and, per the negatives below and §10, blocks codegen and does not run.

```cure
type Dec = Dcoupled | Causal
fn and(d1: Dec, d2: Dec) -> Dec         # used in a type ⇒ totality REQUIRED
  | (Causal, Causal) -> Causal
  | _ -> Dcoupled

type Sig = C(Type) | E(Type)
type SVDesc = List(Sig)

indexed type SF(as: SVDesc, bs: SVDesc, d: Dec) where
  prim : (...) -> SF(as, bs, Causal)
  seq  : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, and(d1, d2))

fn compose({as}, {bs}, {cs}, {d1}, {d2},
           l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, and(d1, d2)) =
  seq(l, r)

# one-step operational semantics — dependent match on SF constructors
fn step(dt, sf, input) -> ... = match sf
  prim(...)   -> ...
  seq(l, r)   -> ...   # SEQ rule; indices refined per branch

# dependent pair (Σ): existentially package the decoupledness index, then project.
# `d` is EXPLICIT (present), not an erased implicit `{d}`: it is materialised into
# the runtime-relevant first component of the Σ, which the {0,ω} relevance check
# (§8, criterion §2 — no computationally-relevant use of an erased binder) forbids
# for an erased binder. Making it present is the honest signature: `forget_dec`
# exists precisely so `recover`/`step` can inspect `d` at runtime, so `d` cannot
# have zero runtime footprint here.
fn forget_dec({as}, {bs}, d: Dec, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) =
  (d, sf)
fn recover({as}, {bs}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2

# hole: reports its goal type + local context; does not codegen until filled
fn sketch(l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, and(d1, d2)) = ?body
```

**Mechanisms exercised:** TT1 (type-level terms, `Pi`, implicit inference+erasure, NbE conversion, universes), TT2 (one indexed family + one type-level inductive + computed index `and(d1,d2)`), TT3 (dependent pattern matching with index unification in `step`), TT4 (totality required for `and`), plus **`Σ` types** (formation/intro/projection + pair pattern + erasure) and **holes** (goal-type + local-context reporting).

**Negatives that must be rejected:**
- `seq(l, r)` where the middle indices disagree (`bs ≠ bs'`) → index-unification error.
- A composition whose declared index contradicts `and`'s computation → conversion error (both normal forms shown).
- Making `and` non-total while it is used in a type → totality-required error.
- A pair `(a, b)` whose second component's type doesn't match `B[a/x]` → `Σ` type error.
- An unfilled hole → the program reports the hole's goal type + context and **does not** emit BEAM.

**Deferred to later slices:** `_++_`/`map` (needed by `**`/`loop`); the `**`/`switch`/`dswitch`/`loop` constructors; `Init`/uninitialised-signal descriptors; broad use of the `Eq`/`rewrite` escape hatch. And the kernel self-host (phase 2) and verified metatheory (phase 3) per §9.

## 7. Totality integration (targeted)

The elaborator computes the **type-level closure**: every function reachable from a type (transitively) or marked `@total`. Each must pass **termination** (`totality.ex`: structural descent + `tarjan_scc` mutual recursion) and **coverage** (`pattern_checker.ex`). On success the function gets a **totality certificate** in the Core global environment; the kernel only δ-unfolds certified functions during conversion (guaranteeing termination). A type-level function that fails → hard error. Runtime-only functions stay partial; their classification is merely reported.

**Trust boundary for certificates (important — conversion termination depends on it).** Conversion termination is a *kernel* guarantee, so the kernel must not simply trust an elaborator-asserted certificate. The termination + coverage **decision procedure** is therefore part of the trusted base: `kernel.ex`'s certificate validation **re-runs** that check on the Core definition itself before accepting the certificate (it does not take the elaborator's word for it). What the *untrusted* elaborator contributes is only the **closure computation** — *which* functions to submit for checking — and that choice is safe to leave untrusted because a missed function simply stays uncertified (opaque to δ, never a soundness hole). The check's *logic* (the `totality.ex`/`pattern_checker.ex` algorithms) is invoked by the kernel and thus trusted; only its *driver* (the closure walk in the elaborator) is untrusted. This is why the §3 "Why `Type : Type` was rejected" tension does not bite: with the predicative hierarchy, **logical consistency** no longer depends on the totality checker at all (it is secured by the universes); only conversion **termination** does, and that obligation is a small, local, kernel-re-validated property — unlike `Type : Type`, where the universe itself is non-normalizing regardless of how correct the totality checker is.

## 8. Erasure → codegen

After `kernel.check` succeeds, Core is erased to the existing runtime AST: implicit args, type-level data, universe levels, and `Eq` proofs are dropped; indexed-family constructors become ordinary tagged tuples (identical to today's ADT lowering); `case` trees become ordinary BEAM `case`. Purely type-level functions vanish; functions used at both levels are kept. Erasure is *licensed* by the `{0,ω}` check (§3, `lib/cure/elab/relevance.ex`, M8.3): a `0`-marked binder is verified during elaboration never to be used in a **computationally-relevant position** at runtime — returned as the value, passed in a `present` argument position, scrutinised as a `case` discriminant, or applied as a function head (type/index positions, erased argument positions, and `Eq`/proof positions are exempt) — so dropping it is sound rather than a positional guess. (The criterion is §2's "computationally-relevant position"; the earlier shorthand "scrutinised" understated it — returning or passing an erased binder is equally unsound, which is why the §6 `forget_dec` takes its decoupledness `d` as an explicit *present* parameter.) Net effect: the **descriptors** (`SVDesc`, `Sig`, and the `as/bs/cs/d` *index arguments* of `SF`) have **zero runtime footprint** — matching the paper's "descriptors exist only at the type level." `SF` itself is *not* fully erased: its value-relevant structure (constructor tags plus the embedded transition functions/continuations) survives as tagged tuples so that `step` can pattern-match on it at runtime (§6); only its erased type indices are dropped. `codegen.ex` is reused essentially unchanged.

## 9. Kernel-trust strategy (three phases)

A *verified* dependent type checker cannot be written in a language without dependent types — so some unverified bootstrap is unavoidable. This is the normal state of the art (Coq/Agda/Lean kernels are unverified OCaml/Haskell/C++, trusted via smallness + independent re-checking). We adopt the standard arc, with the self-host scheduled rather than vague:

1. **Phase 1 — Elixir bootstrap (this spec).** Build the kernel + elaborator in Elixir; reach the FRP slice; lock the design. Ship the three commitments from day one:
   - **(C1)** the implementation-independent Core spec (§4);
   - **(C2)** **serializable Core proof terms** + a minimal, pure kernel boundary, so an independent checker can re-validate the same artifacts;
   - **(C3)** a **conformance corpus** of positive/negative Core terms every kernel implementation must agree on.
2. **Phase 2 — Cure self-host (committed milestone).** Re-implement the kernel in Cure once the type theory is rich enough, validated **differentially against the Elixir kernel as a reference oracle** (run both on C3 + random Core terms; they must agree). In-language trusted base; still unverified, but independently cross-checked.
3. **Phase 3 — Verified metatheory (long horizon).** Prove soundness + decidable conversion (in an established assistant such as Coq/Lean and/or self-verified in Cure, à la MetaCoq). Not gated on host language; gated on Cure's metatheoretic maturity.

Rationale for Elixir-first: proofs are equally far away in either host, so the near-term question is only which host makes the hardest, most novel code (NbE, pattern unification) fastest to stabilize — clearly the mature one — and the Elixir kernel + C1 + C3 become the oracle that de-risks the Phase 2 rewrite.

## 10. Diagnostics

New error codes, routed through the existing Socratic type-error assistant: **conversion failure** (print both normal forms), **index-unification failure** (the `seq` middle-index mismatch), **uninferable implicit** (unsolved metavariable + local context), **totality-required** (function used in a type isn't total), **coverage failure**, **universe ceiling exceeded**, and **hole goal reports** (`:hole_goal` carrying goal type + local context). An unfilled hole blocks codegen rather than erroring hard.

## 11. Testing & acceptance

Red-green discipline per `~/agent_docs/testing.md`. Layers:
- **Kernel unit tests** — conversion (β/ι/δ/η) + cumulativity; the `Σ` projection ι-rules (`(a,b).1 ⇝ a`, `.2 ⇝ b`) and the pair-intro `B[a/x]` check (§4.7); hand-written positive/negative `check`s on Core terms. These seed the **conformance corpus (C3)**.
- **Elaborator tests** — implicit inference; dependent-pattern coverage; the index-unification reject; `Σ` pair-pattern compilation; hole recognition + `:hole_goal` reporting (goal type + local context).
- **Slice 1 acceptance** — the program in §6 constructs, typechecks, **and runs one step** on generic-unix; each §6 negative is rejected with the right code.

## 12. Risks & open questions

- **Dependent pattern compilation** is the hardest single piece (index unification, impossible-branch detection, coverage under indices). Mitigation: keep case trees in Core (kernel checks them) rather than synthesizing eliminators; start with the two-constructor `SF` in Slice 1.
- **Implicit inference** beyond Miller patterns is undecidable; we deliberately restrict to the decidable fragment and error out (with context) otherwise.
- **Cumulativity + NbE η** interaction needs care in read-back; covered by kernel tests.
- **`++` associativity** may or may not be needed by the full port; if it is and is non-definitional, the §4.6 `Eq`/`rewrite` hatch handles it. We confirm against the real port, not hypothetically.
- **Integration seam** with the existing `checker.ex` (non-dependent surface, refinements) must be clean: the elaborator handles the dependent fragment; refinements remain orthogonal. Exact hand-off boundary is an implementation detail to nail in the plan.

## 13. Out of scope (this spec)

Later slices widen the family (`**`, `loop`, `switch`, `dswitch`), add `++`/`map` and `Init` descriptors, and broaden the `Eq` hatch. Phases 2–3 (Cure self-host; verified metatheory) are roadmap, not this slice. Universe polymorphism, the linear `1` multiplicity / usage-counting (we do the erasure-only `{0,ω}` fragment, §3.1, §8), and SMT-for-indices are explicitly excluded unless a concrete need appears. (Sigma and holes were moved *into* Slice 1 — see §4.7, §6 — so retiring the faked modules forfeits no capability.)
