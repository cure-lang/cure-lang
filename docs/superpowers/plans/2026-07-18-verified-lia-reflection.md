# Verified LIA Reflection Implementation Plan

**Rebased:** 2026-07-20, after inductive `Int`, `Std.Proof.IntOrder`, auto-lemma
search, and open-refinement discharge landed.

**Goal:** Implement the P1 trusted metatheory core from
`docs/superpowers/specs/kernel/2026-07-18-verified-lia-reflection-design.md`: a total
Farkas certificate checker and kernel-checked soundness theorem over canonical
`Std.Int.Int`. P2 (untrusted producer) and P3 (elaborator integration) remain
separate follow-on phases, but this plan pins the interfaces they consume.

**Supersession:** This plan replaces the earlier `Std.Integer.Zed` plan in full.
Do not create `lib/std/integer.cure`, `Std.Integer`, or a second integer family.
Use `Std.Int.Int = FromNat(Nat) | NegativeSuccessor(Nat)` and extend/reuse
`Std.Proof.IntOrder`.

## Constraints

- No kernel rules, axioms, `@extern` arithmetic laws, or trusted solver calls.
- New proofs are ordinary Cure terms checked by the existing kernel.
- The runtime `Std.Builtin.int_mul` may compute but is not a substitute for the
  inductive equations required by soundness.
- Every proof surface has an Idris mirror and `rel=same` oracle coverage.
- Malformed vector/witness shapes reject; `List.zip_with` truncation is forbidden.
- Write focused red probes before each implementation slice, then run the full
  oracle replay and suite once at the final gate.
- Preserve the Farkas boundary: P1 is sound over integers and complete only for
  the rational/Farkas fragment. No cuts, splits, equality goals, or nonlinear
  arithmetic are smuggled into this plan.

## Existing substrate (consume, do not rebuild)

`lib/std/proof_int_order.cure` already provides integer order tests/evidence,
reflexivity, transitivity, same-addend monotonicity, decidability, sign facts,
and `zero_is_not_at_most_negative_one`. Its current scaling theorem is only for
`FromNat(left) <= FromNat(right)` and does not satisfy Task 2 below.

## Task 1: Pin the proof-level integer operations

**Files:** modify `lib/std/proof_int_order.cure`; add paired
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_additive_group.{cure,idr}`.

- [x] Choose and document the proof-level operations used by LIA:
  `add_int`, canonical zero/one/negative-one, `scale_nat_int`, and signed
  `multiply_int` or an equivalently total signed coefficient application.
- [x] Add closed computation probes covering every sign quadrant and zero.
- [x] Ensure definitions recurse structurally on `Nat`/inductive `Int`; do not
  rely on an opaque builtin reduction in a proof.
- [x] Run the focused oracle cluster and commit.

## Task 2: Complete the general integer additive/order kit

**Files:** modify `lib/std/proof_int_order.cure`; extend the Task 1 probe.

Prove the exact reusable signatures (names may follow existing module style):

- [x] left/right identity for `add_int`;
- [x] associativity and commutativity of `add_int`;
- [x] first-argument monotonicity;
- [x] two-sided addition monotonicity:
  `a<=b -> c<=d -> a+c<=b+d`;
- [x] `scale_nat_int(0, x) = 0` and its successor equation;
- [x] monotonicity of `scale_nat_int(k, _, _)` for arbitrary signed operands;
- [x] distributive laws needed to move natural scaling through integer addition;
- [x] signed coefficient-application equations required by dot evaluation.

The red probe must include a genuinely negative inequality, for example scaling
`-2 <= 1`; a nonnegative-only fixture does not exercise the missing theorem.
Run the focused oracle and commit only when every theorem is kernel-accepted.

## Task 3: Define dimension-safe affine syntax and semantics

**Files:** create `lib/std/proof_linear_arithmetic.cure`; add paired
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic_compute.{cure,idr}`.

Define:

- `Relation = LessOrEqual | LessThan`;
- `LinearAtom` with `List(Int)` coefficients and an `Int` constant;
- `Hypotheses`, `FarkasWitness = List(Nat)`, and `Valuation = List(Int)`;
- explicit common-dimension/shape checks or proof evidence;
- total `dot`, `evaluate_atom`, strict-to-nonstrict normalization,
  `negate_atom`, coefficient addition/scaling, and atom combination.

- [x] Reject coefficient/valuation length disagreement.
- [x] Reject witness length other than `length(hyps) + 1`.
- [x] Add positive, forged-witness, wrong-length, and wrong-dimension compute
  probes before implementation.
- [x] Include the documented integer-only boundary example without claiming
  that a finite witness sample proves global nonexistence.
- [x] Run focused oracle replay and commit.

## Task 4: Prove affine evaluation homomorphisms

**Files:** extend `lib/std/proof_linear_arithmetic.cure`; add paired
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic_semantics.{cure,idr}`.

Prove, under the selected shape evidence:

- [x] zero coefficients evaluate to zero;
- [x] pointwise coefficient addition evaluates to integer addition;
- [x] natural coefficient scaling evaluates to `scale_nat_int` of the dot product;
- [x] atom normalization preserves its proposition;
- [x] combining two holding atoms yields a holding combined atom;
- [x] folding aligned atoms/witnesses preserves evaluation.

This task is the load-bearing syntactic-to-semantic bridge. Do not proceed to
checker soundness if any fold step is justified only by computation on closed
examples rather than a theorem quantified over valuations.

**Completed evidence (2026-07-21):** `Std.Proof.LinearArithmetic.Semantics`
proves all six obligations over symbolic lists, valuations, coefficients, and
fold witnesses. `ZeroCoefficientsAt`, `AddedCoefficientsAt`, and
`ScaledCoefficientsAt` carry the shape evidence; `WeightedAffineFold` carries
the recursive fold alignment. The proofs use generated `dot_empty`/`dot_cons`
equations, `have`, `proof chain`, directed `rewrite`, `simplify using`, and
structured induction. The paired `linear_arithmetic_semantics` oracle accepts
in both Cure and Idris, while `linear_arithmetic_semantics_wrong` rejects in
both. The focused proof gate is 43 tests with 0 failures; the full suite is
5,417 tests with 0 failures and 6 excluded; complete Antigen is 318/318.

## Task 5: Prove list and negation reflection

**Files:** extend `lib/std/proof_linear_arithmetic.cure`; extend the semantics
probe or add `linear_arithmetic_reflection.{cure,idr}`.

- [ ] Define proof-relevant `AllHold(hyps, env)` or prove complete inversion for
  its Boolean implementation.
- [ ] Prove head/tail elimination and append/snoc construction/elimination.
- [ ] Prove `not (a <= b)` iff `b < a`.
- [ ] Prove `not (a < b)` iff `b <= a`.
- [ ] If strict atoms normalize to shifted non-strict atoms, prove
  `a < b` iff `a + 1 <= b` and normalization preservation.
- [ ] Run focused oracle replay and commit.

## Task 6: Implement proof-relevant certificate validity

**Files:** extend `lib/std/proof_linear_arithmetic.cure`; add paired
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic_certificate.{cure,idr}`.

Define `ValidFarkasCertificate(hyps, goal, witness)` carrying at least:

- exact witness/atom alignment;
- common coefficient dimension;
- the normalized combined atom;
- all combined coefficients equal zero;
- a contradiction-strength constant/relation fact.

Then implement:

- [ ] a total decision procedure for validity;
- [ ] `check_lia(...) -> Bool` as its Boolean facade;
- [ ] `check_lia_true_implies_valid` (or an equivalent proved bridge);
- [ ] acceptance of a valid multi-hypothesis witness;
- [ ] rejection of forged, malformed, and dimension-invalid witnesses.

The elaborator may compute `check_lia`, but it must never manufacture
`ValidFarkasCertificate`; the bridge is Cure code checked by the kernel.

## Task 7: Prove `combine_preserves_evaluation`

**Files:** extend the checker module and certificate oracle pair.

- [ ] Induct over aligned atoms and witness coefficients.
- [ ] Use Task 2 two-sided monotonicity and arbitrary-signed natural scaling.
- [ ] Use Task 4 dot-product homomorphisms at each induction step.
- [ ] Use Task 5 `AllHold` inversion to obtain the current atom and tail proofs.
- [ ] Prove the combined valid contradiction cannot hold under any valuation.

Commit only after the theorem is exercised with a symbolic valuation in the
paired oracle, not merely a closed numerical valuation.

## Task 8: Prove `check_lia_sound`

**Files:** extend `lib/std/proof_linear_arithmetic.cure`; add paired canonical
`https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/linear_arithmetic.{cure,idr}`.

Target:

```cure
fn check_lia_sound(
  hyps: Hypotheses,
  goal: LinearAtom,
  witness: FarkasWitness,
  valid: ValidFarkasCertificate(hyps, goal, witness),
  env: Valuation,
  holds: AllHold(hyps, env)
) -> IsTrue(evaluate_atom(goal, env))
```

- [ ] Decide the goal Boolean constructively.
- [ ] In the false branch, use goal-negation correctness to append the negated
  goal to `AllHold`.
- [ ] Apply `combine_preserves_evaluation`.
- [ ] Use validity's zero-coefficient/negative-bound evidence and
  `zero_is_not_at_most_negative_one` to derive `Empty`.
- [ ] Export a convenience theorem accepting `IsTrue(check_lia(...))` via
  `check_lia_true_implies_valid`.
- [ ] Mirror the complete proof in Idris and obtain `rel=same`.
- [ ] Commit.

## Task 9: P1 integration and verification gate

- [ ] Confirm the new module is `@group(:core)` and included by the automatic
  stdlib bundling path; there is no hand-maintained manifest to edit.
- [ ] Run all new focused tests.
- [ ] Run full `mix cure.oracle` and offline replay.
- [ ] Run the full project test gate serially.
- [ ] Run the relevant Antigen/TCB gates even though no kernel file should change.
- [ ] Update the spec status and write a completion report stating the exact
  rational-complete/integer-sound boundary.
- [ ] Commit the phase documentation.

## Follow-on phases (not P1)

### P2: untrusted producer

Implement deterministic Fourier–Motzkin/simplex search returning
`Prf witness | Model valuation | Unknown`. Property-test that every `Prf` passes
the checker and every `Model` really satisfies the hypotheses and falsifies the
goal. Fix variable order, pivot policy, rational normalization, and iteration
bound. External Z3/cvc5 coefficient producers remain optional plugins.

### P3: elaborator seam

Register LIA behind the existing ordered proof-search seam. Recognize affine
`IsTrue` goals and local/refinement hypotheses, assign a stable variable order,
invoke P2, encode the witness as Core, obtain validity through the proved checker
bridge, apply `check_lia_sound`, and let the kernel re-check the resulting term.
On `Model`/`Unknown` or unsupported/nonlinear syntax, fall back honestly.

P3 must include an end-to-end mapping proof/test connecting elaborator variable
ordering, coefficient positions, valuation construction, local `AllHold`
evidence, and the original surface refinement goal.
