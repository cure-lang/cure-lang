# Verified LIA Reflection — design

**Branch:** `smt-solver` (off `feature/idris-parity`)
**Date:** 2026-07-18
**Status:** approved design, rebased 2026-07-20 onto canonical inductive `Int`

> **2026-07-20 authoritative amendment.** The original design predated the
> inductive-`Int` and ordered-ring work. `Std.Int.Int = FromNat(Nat) |
> NegativeSuccessor(Nat)` and `Std.Proof.IntOrder` are now the sole integer
> substrate. Do not create the formerly-planned parallel `Std.Integer.Zed`
> family. The checker proof also requires the algebra, vector-semantics, shape,
> and Boolean-inversion layers specified in §3.5–§3.9; scalar order
> monotonicity alone is not enough to justify Farkas combination.

> **2026-07-21 proof-authoring dependency.** The remaining semantic
> homomorphism and fold-preservation proofs are the acceptance workload for
> `2026-07-21-proof-language-ergonomics-design.md`. Keep the current work parked
> until that proof surface is implemented, then restore it without changing the
> checker mathematics or trust boundary.

> **2026-07-22 OTP-first execution amendment.** The follow-on execution spec
> `2026-07-22-certificate-generator-integration-design.md` establishes the
> implementation order. Before completing this document's general Farkas/cut
> path, Cure vertically slices B3 mailbox-pattern inclusion using checked
> affine embeddings between semilinear components. Full commutative-regex
> inclusion is quantified Presburger arithmetic; it is not covered merely by
> adding quantifier-free cut/split nodes. This changes priority and adds a
> domain certificate, but does not change the trust boundary described here.

## 0. Motivation

The Int-refinement prelude (`IsTrue`/`Confirmed`, `Std.Proof.IntMath`) discharges
*closed* Int obligations by computation and a *curated* open Nat fragment by lemma
search / v2 positivity. It does **not** replace what Z3-driven refinements gave us:
a uniform decision procedure for open linear integer arithmetic. That breadth gap —
`fn f({n:Int|n>0}) -> {m:Int|m>0}` where the obligation is symbolic — is the "real
need" the mailbox-subtyping thread deferred to its Phase 4 extension point.

This branch closes that gap the sound way named in the locked
`smt-trust-boundary-decision`: **a verified linear/Presburger decision procedure via
computational reflection — no solver in the TCB.** It is the SMTCoq / Rocq-Micromega
architecture, specialized to one theory (LIA) and one target proposition
(`IsTrue(<Bool comparison>)`).

Z3 stays out of the TCB permanently. Any external solver may only ever act as an
**untrusted producer**; the kernel re-checks every certificate.

### Non-goals (explicitly out of scope for this branch)

- **Native-proof replay (design "B")** — consuming veriT/cvc5 Alethe proofs directly.
  The seam is left open for it (§2) but no Alethe checker is built here.
- **The `IsTrue ↔ inductive-family` bridge (#4)** — connecting `IsTrue(a<b)` with
  `Std.Proof.Math`'s `IsPositive`/`IsLessThan`. Owned by a separate agent/branch.
  This branch only *produces* `IsTrue(...)` evidence and composes with #4 downstream.
- **Path narrowing** — bringing `IsTrue(n>0)` into scope from a runtime `if n>0`
  guard. Follow-on, related to #4.
- **Nonlinear arithmetic** (SOS/Positivstellensatz degree > 1, CSDP) — Micromega's
  `nlia`/`nlinear`. Out.
- **ℤ-completeness via cutting planes** — see §3.4. P1 ships the Farkas core
  (sound for ℤ, complete over ℚ); cuts/splits are a documented follow-on.
- **`Equal`-relation goals** — see §3.1. A single Farkas combination can't certify a
  negated equality (a disjunction); P1 restricts `check_lia`'s `goal` to
  `LessEqual`/`Less`. Splitting an `Equal` goal into two sub-certificates is a
  documented follow-on. `Equal`-relation *hypotheses* are unaffected.

## 1. Prior-art models (all local, in-family + canonical)

| Design piece | Model | Path |
| --- | --- | --- |
| Full A architecture, both halves | **Rocq Micromega** | `~/Develop/rocq/plugins/micromega/` |
| — untrusted producer (simplex Farkas search) | `certificate.ml`, `simplex.ml`, `linsolve.ml`, `polynomial.ml`, `vect.ml` | idem |
| — verified checker (extracted) | `micromega.mli`: `zChecker`, `zTautoChecker`, `zArithProof` | idem |
| — certificate result type | `certificate.mli`: `res = Prf of 'prf | Model of 'model | Unknown` | idem |
| Reflexive-checker seam, modern & in-family | Lean 4 **`bv_decide`** (external SAT → LRAT → verified checker) | `~/Develop/lean4/tests/.../bv_decide*` |
| LIA goal normalization | Lean 4 **`omega`** | `~/Develop/lean4/src/Init/Omega` |
| Farkas certificate *content* | mathlib **`linarith`** | `~/Develop/mathlib4/Mathlib/Tactic/Linarith` |
| Reflective checker idiom in a DT setting | agda-stdlib **`RingSolver`** (`NonReflective`, `Core`) | `~/Develop/agda-stdlib/src/Tactic/RingSolver` |
| In-repo precedent for verified-checker + reflection | shipped mailbox `Incl`/`incl_sound`, Brzozowski `matches_word_sound` | `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/mailbox_pattern.cure` |
| Sibling verified-checker design, same architecture | mailbox-subtyping certificate checker plan (`check_incl`/`check_incl_sound`, Brzozowski completeness `matches_word_complete`) — **not yet merged into this branch's history** (commit `8b237eef`, branch `elaborator-gaps`); read for the pattern, don't assume its lemmas are in scope here | `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/2026-07-18-mailbox-subtyping-certificate-checker-plan.md` on `elaborator-gaps` |

The algorithm is modeled on Micromega; `bv_decide`/`omega`/`linarith`/`RingSolver`
are cross-checks. Idris remains the **differential oracle** (`rel=same`), not the
algorithmic model.

## 2. Architecture — the seam

A single E-layer dispatch point, additive over the existing syntactic discharge
paths:

```
obligation the syntactic paths cannot close
        │
        ▼
recognize domain  ──► registered (recognizer, producer, checker) entry
        │
        ▼
producer (UNTRUSTED, Elixir)  ──►  certificate c   |   Model m (counterexample)  |  Unknown
        │ Prf c
        ▼
build Core term  check_lia(hyps, goal, c)
        │
        ▼
kernel discharges goal by COMPUTING check_lia(hyps, goal, c)  ⇓  True()
```

- The registry holds **one** entry today: LIA. Adding design B later = registering
  another `(recognizer, producer, checker)` triple; the seam does not change.
- On `Model`/`Unknown`, fall back to the existing syntactic paths / honest error.
  Never weakens soundness — the kernel re-runs the verified checker regardless of
  what the producer claims.
- **No new kernel rule.** Discharge uses existing whnf/δ computation on a normal
  Cure function. This is the elaborator-hard-stop guarantee: if the checker ever
  *seems* to need a kernel change, STOP and report.

## 3. The verified checker (kernel-checked metatheory; TCB does not grow)

"Trusted" here means: trusted *because the existing kernel checks its soundness
proof*. Nothing new is assumed.

### 3.1 Types (Cure, `Std.Proof.LinearArithmetic` — descriptive naming)

- `LinearAtom` — a linear comparison over integer variables: a coefficient vector
  `List Int`, a constant `Int`, and a relation (`LessEqual`/`Less`/`Equal`). `Int`
  here is the canonical inductive `Std.Int.Int`, never a second `Zed` family. Models
  Micromega's `nFormula` / `op1`. `GreaterEqual`/`Greater` are not separate
  constructors: `a ≥ b` / `a > b` are built by negating the coefficient vector and
  constant and using `LessEqual`/`Less` (`a ≥ b ≡ -a ≤ -b`) — every `≥`/`>` example
  in this document (§0, §6) is this normal form, informally written with `≥`/`>` for
  readability. **Goal scope for P1:** `check_lia`'s "negate the
  goal" step (§3.2) only yields a single `LinearAtom` when `goal.relation` is
  `LessEqual` or `Less` — negating `Equal` is a disequality (`a<b ∨ a>b`), a
  disjunction no single Farkas combination certifies. Micromega itself needs a
  dedicated `NonEqual` op1 constructor plus a case-splitting `zTautoChecker` layer
  above the raw certificate checker for this case (`micromega.mli`). P1 therefore
  restricts `check_lia`/`check_lia_sound`'s `goal` to `LessEqual`/`Less` relations;
  `Equal`-relation goals (split into two `LessEqual` sub-certificates) are a
  documented follow-on, not silently assumed to work. `Equal`-relation *hypotheses*
  are unaffected — they combine fine with a nonnegative multiplier in one direction;
  supplying the reverse direction as a second hypothesis covers the other.
- `Hypotheses = List LinearAtom` — the in-scope facts (from refinement binders and
  local hypotheses).
- `FarkasWitness = List Nat` — nonnegative multipliers, one per atom in
  `hyps ++ [negate(goal)]` (i.e. length `|hyps| + 1`: one per hypothesis plus one
  for the negated goal, matching the combination §3.2 forms). Dense positional list,
  index-aligned with the atom list it multiplies — decided now so `check_lia`'s
  indexing is unambiguous; a sparse `List (Nat, Int)` encoding is a possible later
  optimization, not part of this design. Models Micromega `zWitness` / `RatProof`'s
  witness.
- `Valuation = List Int` — an assignment of integer values to the variables a
  `LinearAtom`'s coefficient vector indexes into (one value per coefficient
  position), positional like `LinearAtom` itself.
- `evalAtom(atom: LinearAtom, env: Valuation) -> Bool` — evaluates the dot product
  of `atom`'s coefficients against `env`, compares against `atom`'s constant using
  `atom`'s relation, and returns the `Bool` result. The semantic counterpart to
  `check_lia`'s purely syntactic combination.
- `AllHold(hyps: Hypotheses, env: Valuation) -> Type` — every atom in `hyps`
  evaluates to `True()` under `env` (via `evalAtom`); the semantic reading of a
  hypothesis list, dual to `Hypotheses` itself being the syntactic reading.

All atoms in one problem have the same coefficient-vector length as the
valuation, and the witness has exactly `length(hyps) + 1` entries. P1 carries
explicit checked shape evidence. `List.zip_with` truncation is not an admissible
meaning for malformed certificates.

### 3.2 `check_lia`

```
fn check_lia(hyps: Hypotheses, goal: LinearAtom, witness: FarkasWitness) -> Bool
```

Total, structural. Negate the goal, add it to `hyps`, form the nonnegative linear
combination `Σ witnessᵢ · atomᵢ`, and check the combination reduces to a manifest
contradiction (`0 ≤ -1` / `0 < 0`). Returns `True()` iff the witness certifies
unsatisfiability of `hyps ∧ ¬goal`. Mirrors `zChecker` restricted to `RatProof`.

The Boolean facade is not by itself the proof object consumed by soundness. P1
defines `ValidFarkasCertificate(hyps, goal, witness)`, carrying checked shape,
normalized-combination, zero-coefficient, and negative-bound evidence. A
decision procedure constructs or refutes this evidence; `check_lia` is its
computable Boolean projection. A Boolean-only implementation is acceptable only
if it proves equivalent inversion lemmas for every carried fact before proving
soundness.

### 3.3 `check_lia_sound` (the metatheory payoff)

```
fn check_lia_sound(
  hyps: Hypotheses, goal: LinearAtom, witness: FarkasWitness,
  valid: ValidFarkasCertificate(hyps, goal, witness),
  env: Valuation,
  holds: AllHold(hyps, env)
) -> IsTrue(evalAtom(goal, env))
```

Proven in Cure, Idris-mirrored `rel=same`. Structure mirrors Micromega's
`ZTautoChecker_sound`: a valid nonnegative combination that yields `0 ≤ -1` cannot
have all constituents hold, so `¬goal` is refuted and `goal` holds in `env`. The
target `IsTrue(evalAtom(goal,env))` is exactly the L1/L2 Int-sugar proposition, so
the result plugs straight into the existing refinement pathway and hands off to #4.
An exported, Cure-proven `check_lia_true_implies_valid` connects
`IsTrue(check_lia(...))` to `ValidFarkasCertificate`, preserving the §2 reflection
diagram without asking the elaborator to invent structural facts.

### 3.4 Completeness boundary (honest)

The Farkas core is **sound for ℤ, complete over ℚ**. Integer-only unsat instances
(e.g. `2n = 1`) need cutting planes. This exactly matches Micromega's layering:
`RatProof` (shipped here) vs `CutProof`/`SplitProof`/`EnumProof` (follow-on). The
checker and certificate types are designed so cut/split constructors can be *added*
without reshaping `check_lia_sound` — new constructors, new sub-proofs, same theorem
shape. Until then, the *producer* (§4) reports `Unknown` for ℤ-only instances (legal)
— `check_lia` itself never returns `Unknown`; see §6's boundary case for what that
means at the checker level.

### 3.5 Canonical integer algebra substrate

P1 reuses `Std.Proof.IntOrder` for reflexivity, transitivity, same-addend
monotonicity, sign facts, and the `0 ≤ -1` refutation. Before checker soundness it
adds general integer addition identity/associativity/commutativity,
first-argument and two-sided addition monotonicity, `scale_nat_int : Nat -> Int
-> Int`, monotonicity of that scaling for arbitrary signed operands, and the
signed coefficient-application laws required by affine evaluation.

The existing `scaling_by_nonneg_preserves_less_than_or_equal` only covers
`FromNat(left) ≤ FromNat(right)`. It is not sufficient for Farkas atoms, whose
evaluated sides may be negative.

### 3.6 Affine-vector semantics

P1 proves that syntactic coefficient operations agree with evaluation: zero
coefficients evaluate to zero, pointwise addition evaluates to integer addition,
natural scaling evaluates to scaling of the dot product, and folding a witness
over atoms preserves evaluation. These homomorphism lemmas are the necessary
bridge between syntactic Farkas combination and semantic inequality.

### 3.7 Shape and totality discipline

Certificate validity carries a common variable dimension, atom/valuation length
agreement, exact witness length, and deterministic rejection of malformed input.
Ordinary lists with evidence or length-indexed vectors are both acceptable; silent
truncation is not.

### 3.8 Boolean/list reflection substrate

`AllHold` has constructive head/tail and append/snoc elimination lemmas so the
soundness induction can extract atom proofs and append the negated goal. The
checker also proves the Boolean-to-`ValidFarkasCertificate` inversion bridge.

### 3.9 Goal-negation correctness

P1 proves `not (a ≤ b)` iff `b < a`, `not (a < b)` iff `b ≤ a`, and, when
strict atoms are normalized away, `a < b` iff `a + 1 ≤ b`. Existing
decidability does not by itself prove that a generated negated atom is the
semantic complement of the original goal.

## 4. The untrusted producer (Elixir, `lib/cure/*`, NOT TCB)

- A deterministic Fourier–Motzkin / simplex search over the hypothesis system,
  modeled on `certificate.ml` + `simplex.ml`, emitting a `FarkasWitness`.
  Result mirrors `certificate.mli`'s `res`: `Prf witness | Model counterexample |
  Unknown`.
- **Determinism is required** so oracle probes replay identically (fixed variable
  order, fixed pivot rule, committed iteration bound).
- **External-solver producers (Z3/cvc5/veriT) are a documented drop-in**, not built
  now: any process that emits a `FarkasWitness` our checker accepts can register at
  the producer plug point. This is the weak-sense "plug in veriT" — solver as
  coefficient-finder, native proof discarded, zero new verified code.
- Independent of `lib/cure/smt/process.ex` (that Z3 process backs the separate
  `guard_lint` untrusted lint; left untouched).

## 5. Layer map, files, discipline

- **Checker + soundness** = K/metatheory: Cure proofs in `lib/std/` (new
  `proof_linear_arithmetic.cure`), oracle-verified. Trust rests on the kernel
  checking `check_lia_sound`.
- **Producer** = untrusted tooling in `lib/cure/*` (Elixir).
- **Seam** = E-layer, in `lib/cure/elab/*`, additive; kernel re-checks.
- **Layer steer:** P1 works in `lib/std/*` only. P2 adds untrusted producer code
  under `lib/cure/*`; P3 alone touches `lib/cure/elab/*`. IGNORE
  `lib/cure/compiler/*` for dependent proof discharge. No P1 core edit is allowed.
- **TCB discipline:** no kernel rules. If P1 seems to need one, STOP and report
  (prove no untrusted term works first — elaborator-hard-stop).
- **Ghost commits:** author as the user only; no Co-Authored-By; explicit-pathspec
  staging.

## 6. Testing (oracle discipline)

Paired `.cure`/`.idr` probe: `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic.{cure,idr}` — `otp/`
is the existing general-purpose oracle-probe directory (already home to non-OTP
probes like `bst.cure`/`bag.cure`/`gbt.cure`), so this needs no new harness support.
`mix cure.oracle`, `rel=same`, replay green before commit. Watch the 30s per-probe budget — a self-contained probe
re-deriving only the needed subset is safer than extending a heavy module.

Must include:
1. **Positive certificate** — an inequality the current paths cannot close, e.g.
   multi-hypothesis Farkas: from `a ≥ 0`, `b ≥ 0` conclude `2a + 3b ≥ 0`; and a
   genuine refinement-shaped obligation such as proving `n + 1 > n` from an open
   `n`, represented in P1 as symbolic atoms and exercised through the actual surface
   only after the P3 bridge exists.
2. **Negative antibody** — a bad witness where `check_lia = False` (soundness of the
   checker: it *rejects* forged certificates).
3. **Shape antibodies** — wrong witness length and coefficient/valuation dimension
   mismatch are rejected rather than truncated.
4. **Boundary case (§3.4)** — record `2n = 1` as a producer-level `Unknown` case for
   P2. A finite enumeration of rejected witnesses is only a regression sample and
   must not be described as proving that no Farkas witness exists.
5. The soundness theorem `check_lia_sound` type-checks (that is the kernel-level
   guarantee), Idris mirror `rel=same`.

**Discipline:** write these four probes (or explicit skeletons of their
assertions) before `check_lia`/`check_lia_sound` are implemented, and confirm
each is currently undischargeable by the existing syntactic-only paths — the red
signal here is elaboration failing to close the obligation, or a hole that
doesn't fill, without the new checker. Land `check_lia`/`check_lia_sound` only to
make that red go green. Once a probe's expected outcome (accept / reject /
no-witness-exists) is fixed, it is immutable: reach green by fixing the checker,
never by weakening or deleting a probe or its assertions, unless the probe
itself is later shown to encode the wrong expectation — state why before
changing it. The same discipline applies to P2's producer/checker-agreement
property tests and P3's dispatch tests (§7): write the assertion, confirm it
fails against the pre-phase state, then implement to green.

## 7. Phasing

- **P1 — verified checker + soundness (stdlib metatheory; no producer).** Complete
  the canonical-`Int` algebra, affine-vector homomorphisms, shape evidence,
  negation/list reflection, `ValidFarkasCertificate`, `check_lia`, and
  `check_lia_sound`, over an explicit witness. Positive, negative, malformed-shape,
  and symbolic cases (§6), Idris `rel=same`. **This is the whole metatheory core and
  the definition of done for the branch's trusted part.**
- **P2 — untrusted producer.** Deterministic Fourier–Motzkin/simplex → `FarkasWitness`,
  with the `Prf | Model | Unknown` result. Property-test that every `Prf` it emits is
  accepted by `check_lia` (producer/checker agreement), and every `Model` genuinely
  falsifies.
- **P3 — seam / reflection integration.** E-layer dispatch: recognize an LIA
  obligation the syntactic path can't close, call P2, build `check_lia(...)`, let the
  kernel discharge by computation. Fall back to syntactic path / honest error on
  `Model`/`Unknown`. Additive.

## 8. Definition of done

**P1** — the canonical-`Int` algebra, vector semantics, shape/reflection layer,
`ValidFarkasCertificate`, `check_lia`, and `check_lia_sound` are proven in Cure,
Idris `rel=same`, with a positive certificate outside the current syntactic
fragment plus forged and malformed antibodies, all green under replay. P2/P3
are follow-on integration once P1 lands. Honest generality statement in the final
report: which LIA instances the checker decides (ℚ-complete / ℤ-sound Farkas core) vs
the producer's completeness.
