# Axiom-Free Refinement Reflection: connecting `IsTrue` to the inductive Nat families — Design

**Date:** 2026-07-18
**Status:** DESIGN (unbuilt). Follows [`2026-07-18-int-refinement-prelude-design.md`](2026-07-18-int-refinement-prelude-design.md) and the auto-lemma proof-search work (`2026-07-18-auto-lemma-proof-search-design.md`).
**Layer:** Stdlib (`lib/std/*.cure`) + elaborator (E, `lib/cure/elab/*`) + oracle fixtures. **No kernel (K) change.** `lib/cure/core/*` is untouched; if a change seems required, STOP per the elaborator-hard-stop principle. This is doubly load-bearing right now: certificate checking is being built in the kernel, so this feature must add **zero new trust** — no axioms, no postulates, no `@extern`, no kernel edit.

## 1. Goal

Let an **open** refinement obligation stated as a boolean comparison —
`IsTrue(some_comparison)` with a free binder inside it — draw on the existing
inductive proof library in `Std.Proof.Math` (`IsPositive`, `IsLessThan`,
`IsLessThanOrEqual` and their lemmas), **without a solver and without a single
new axiom.** Today those two worlds are disconnected: the inductive families
have a rich, kernel-checked lemma library but are only reachable by hand-writing
proof terms, while `IsTrue(boolean_comparison)` obligations discharge only when
*closed* (by computation, the int-refinement level-2 path). An open obligation
in `IsTrue` form has nowhere to go.

We connect them with three constructive, zero-trust layers, and we are explicit
about the one thing that is *not* reachable without trust (§6), so the boundary
is documented rather than smuggled. Concretely, three items (referenced by
these letters throughout the rest of this design):

- **(a)** an open **conjunction** or bounded-range obligation — `IsTrue(and(0 <=
  n, n <= 100))` — should discharge from its two halves without a solver (§4);
- **(b)** an open **`Nat`** obligation should stop being computation-only and
  reach the full `Std.Proof.Math` lemma library — transitivity, monotonicity,
  positivity of products and sums (§5);
- **(c)** a refined value should be usable directly where its base type is
  expected, the reverse of the existing base→refined injection (§7).

## 2. The trust posture (why this design exists in this shape)

`Int` in Cure is a primitive with no induction, and the only `Int → Nat` map
(`Std.Nat.of_int`) is already an asserted FFI boundary. Any *static* proof about
abstract **primitive-`Int`** arithmetic (e.g. `∀ a b : Int. a > 0 → b > 0 →
a * b > 0`, held in primitive form) must ultimately rest on trusted axioms about
the native operators — there is no term that proves it. That route (a ledgered
`Int ↔ Nat` homomorphism interface) is real and was sketched during design, but
it is **deferred** (§6): while the kernel's certificate checker is under
construction we hold the line on trust and ship only what is *proved*.

The insight that makes "proved only" cover most of the surface: **stop treating
primitive `Int` as the carrier of a refined quantity.** Represent refined
non-negative quantities as `Nat` (or `Bounded`), do the arithmetic and proofs on
`Nat` where induction is available, and project to a machine `Int` only at the
boundary. Then the entire lemma library applies by ordinary proof, and the only
`Int`-specific step left is a *runtime* check at genuine external boundaries
(§5, Layer 3), which asserts nothing.

## 3. Naming discipline (a first-class requirement, not a nicety)

Cure aims to be the friendliest dependently typed language ever made, and the
standing directive is to **spell names out in full even where the tradition
abbreviates.** This module is exactly where that tradition is worst — Agda calls
the reflection lemma `<ᵇ⇒<` and the connective lemma `T-∧`; Idris writes `So`,
`Oh`, `LTE`. We do the opposite, deliberately:

| Tradition (Agda / Idris) | Cure name (this design) |
|---|---|
| `T`, `So` | `IsTrue` (already shipped) |
| `Oh`, `tt` | `Confirmed` (already shipped) |
| `_<ᵇ_` | `natural_is_less_than` |
| `_≤ᵇ_` | `natural_is_less_than_or_equal` |
| `<ᵇ⇒<` | `less_than_holds_when_boolean_comparison_is_true` |
| `<⇒<ᵇ` | `boolean_comparison_is_true_when_less_than_holds` |
| `T-∧` (proj₁ / proj₂) | `left_operand_is_true_from_true_conjunction` / `right_operand_is_true_from_true_conjunction` |
| `T-∧` (intro) | `conjunction_is_true_when_both_operands_are` |
| `T-∨` (inj₁ / inj₂) | `disjunction_is_true_from_left_operand` / `disjunction_is_true_from_right_operand` |
| `soToNotSoNot` (Idris `Data.So`) | `true_negation_contradicts_truth` |

Note on the last row: agda-stdlib's `Data.Bool.Properties` has no lemma named
`T-not` — the nearest names, `T-not-≡ : T (not x) ⇔ x ≡ false` and `¬T-≡ : (¬ T
x) ⇔ x ≡ false`, state a different fact (an iff with propositional equality on
`Bool`), not the ex-falso shape proved here. Idris (`~/Develop/Idris2/libs/base/
Data/So.idr`) does have the exact match: `soToNotSoNot : So b -> Not (So (not
b))` is `claim_is_true -> negation_is_true -> Empty` (curried the other way
round), so this row's tradition name is Idris's, not Agda's, unlike every other
row in this table.

Bound variables are spelled out too: `left`, `right`, `value`, `predecessor`,
`left_predecessor`, `evidence`, `claim`, `left_is_true` — never `m`, `n`, `x`,
`h`, `pf`. A reader who has never seen a reflection lemma should be able to read
the *name* and know what it proves. Long names are the feature.

## 4. Layer 1 — the boolean-connective algebra over `IsTrue` (constructive, zero trust)

`IsTrue` reflects `Bool`, and `Std.Bool` defines `and`/`or`/`not` by
`case`-elimination that reduces definitionally (`and(True(), right) ≡ right`).
So these lemmas are proved by matching on the reducing operand — they never
inspect what a comparison *means*, and therefore apply to `Int` and `Nat`
obligations alike. New module `Std.Proof.BooleanReflection`:

```
mod Std.Proof.BooleanReflection
  use Std.Bool
  use Std.Decision           # for Empty (true_negation_contradicts_truth's codomain)
  use Std.Proof.IntMath      # for IsTrue / Confirmed

  ## Split a true conjunction into its left operand's truth.
  fn left_operand_is_true_from_true_conjunction(
    {left: Bool},
    {right: Bool},
    conjunction_is_true: IsTrue(`and`(left, right))
  ) -> IsTrue(left) = match left
    True()  -> Confirmed()
    False() -> absurd(conjunction_is_true)   # and(False, right) ≡ False; witness uninhabited

  fn right_operand_is_true_from_true_conjunction(
    {left: Bool},
    {right: Bool},
    conjunction_is_true: IsTrue(`and`(left, right))
  ) -> IsTrue(right) = match left
    True()  -> conjunction_is_true            # and(True, right) ≡ right
    False() -> absurd(conjunction_is_true)

  ## Combine two truths into the truth of their conjunction.
  @lemma
  fn conjunction_is_true_when_both_operands_are(
    {left: Bool},
    {right: Bool},
    left_is_true: IsTrue(left),
    right_is_true: IsTrue(right)
  ) -> IsTrue(`and`(left, right)) = match left
    True()  -> right_is_true
    False() -> absurd(left_is_true)

  ## Either operand's truth suffices for a disjunction.
  @lemma
  fn disjunction_is_true_from_left_operand(
    {left: Bool}, {right: Bool}, left_is_true: IsTrue(left)
  ) -> IsTrue(`or`(left, right)) = match left
    True()  -> Confirmed()
    False() -> absurd(left_is_true)

  @lemma
  fn disjunction_is_true_from_right_operand(
    {left: Bool}, {right: Bool}, right_is_true: IsTrue(right)
  ) -> IsTrue(`or`(left, right)) = match left
    True()  -> Confirmed()
    False() -> right_is_true

  ## A claim and its negation cannot both hold.
  fn true_negation_contradicts_truth(
    {claim: Bool},
    negation_is_true: IsTrue(`not`(claim)),
    claim_is_true: IsTrue(claim)
  ) -> Empty = match claim
    True()  -> absurd(negation_is_true)       # not(True) ≡ False
    False() -> absurd(claim_is_true)
end
```

**Discharge idiom.** `absurd(evidence)` above is *shorthand*, not a Cure
primitive: in every such arm the evidence has an uninhabited type
(`IsTrue(and(False(), right))` reduces to `IsTrue(False())`), and the real
program discharges it by an **empty `match evidence`** — exactly the shipped
`true_is_not_false(proof: IsTrue(False())) -> Empty = match proof` shape in
`Std.Proof.IntMath`. The implementation plan writes the empty match; the spec
writes `absurd(_)` only for readability. (If a genuine ex-falso *coercion* to an
arbitrary goal type is wanted, it is `true_is_not_false` composed with the
existing `Empty` eliminator — still no new primitive.)

**What this buys immediately:** an open **bounded-range** or **conjunction**
obligation over a primitive `Int` binder — `IsTrue(and(0 <= n, n <= 100))` —
decomposes into and recombines from its two halves, with no representation change
and no knowledge of `<=`. This is the item-(a) "conjunctions discharge open"
goal, done constructively.

## 5. Layer 2 — the Nat reflection bridge (constructive, zero trust)

This is the literal "connect `IsTrue` to `IsPositive`/`IsLessThan`" ask, and it
is fully constructive **because both sides are inductive `Nat`.** Extend
`Std.Proof.Math` with boolean-valued comparisons and the reflection lemmas that
tie them to the existing families (transliterated from agda-stdlib
`Data.Nat.Properties` `<ᵇ⇒<` / `<⇒<ᵇ` / `≤ᵇ⇒≤`, snapshotted at
`reference/agda-stdlib/`).

```
  ## Boolean-valued natural-number comparisons (the reflected surface).
  fn natural_is_less_than_or_equal(left: Nat, right: Nat) -> Bool = match left
    Z() -> True()
    S(left_predecessor) -> match right
      Z() -> False()
      S(right_predecessor) -> natural_is_less_than_or_equal(left_predecessor, right_predecessor)

  fn natural_is_less_than(left: Nat, right: Nat) -> Bool =
    natural_is_less_than_or_equal(S(left), right)

  fn natural_is_positive(value: Nat) -> Bool = match value
    Z() -> False()
    S(predecessor) -> True()

  ## Reflection: the boolean comparison being true is the same information as the
  ## inductive relation holding. Both directions, proved by induction.
  @lemma
  fn less_than_holds_when_boolean_comparison_is_true(
    {left: Nat}, {right: Nat},
    evidence: IsTrue(natural_is_less_than(left, right))
  ) -> IsLessThan(left, right) = ...   # mirrors <ᵇ⇒< : induction on left, right

  fn boolean_comparison_is_true_when_less_than_holds(
    {left: Nat}, {right: Nat},
    proof: IsLessThan(left, right)
  ) -> IsTrue(natural_is_less_than(left, right)) = ...   # mirrors <⇒<ᵇ

  # …and the analogous pair for less-than-or-equal and for positivity:
  #   less_than_or_equal_holds_when_boolean_comparison_is_true / …_is_true_when_…_holds
  #   positive_holds_when_boolean_comparison_is_true          / …_is_true_when_positive_holds
```

With these, an open **`Nat`** obligation stated either way can cross into the
inductive family and use the *entire* `Std.Proof.Math` library — transitivity,
`adding_the_same_number_preserves_less_than`,
`multiplying_positive_numbers_is_positive`, positivity of sums — then reflect
back if a boolean conclusion is wanted. This is item (b) ("the Int world stops
being computation-only") realized for every quantity carried as `Nat`:
`a * b > 0`, monotonicity, and range facts become **proofs**, not axioms.

**The free boundary projection (`Std.Nat`).** The only direction needed to hand
a `Nat` back to primitive-`Int` code is the easy one — a structural fold, total,
no clamp, no trust:

```
  ## Project a natural number to a machine integer (structural, total; the
  ## constructive inverse of the trusted `of_int` clamp — this direction needs
  ## no assertion because Nat is well-founded).
  fn to_integer(value: Nat) -> Int = match value
    Z() -> 0
    S(predecessor) -> to_integer(predecessor) + 1
```

## 5b. Layer 3 — runtime decision at genuine external boundaries (zero *new* trust)

When a primitive `Int` genuinely arrives from outside (user input, FFI, an
`Int`-typed API) and cannot be re-represented as `Nat`, do not assert its sign —
**decide it.** The shipped `Std.Proof.IntMath.decide_is_true` already matches the
boolean comparison (which reduces at runtime) and returns kernel-valid evidence
in the `Yes` branch:

```
match decide_is_true(external_value > 0)
  Yes(evidence) -> # evidence : IsTrue(external_value > 0), carry it inward
  No(_)         -> # reject / handle the out-of-range input
```

This asserts nothing — it is a checked branch, the smart-constructor pattern. It
is the honest form of "certify a primitive": you cannot statically *know* an
abstract `Int`'s sign, but you can *check* it and carry the proof. No new code is
required beyond documenting the pattern and shipping a worked example; this layer
is guidance plus a test, not machinery.

## 5c. Automation: how the search *uses* these lemmas (no new solver)

The machinery to *apply* lemmas already exists in this tree — `lemma_candidates`
looks up `@lemma`-tagged theorems under a goal's conclusion head, and `try_lemma`
unifies the goal against a candidate's conclusion and recursively resolves any
unsolved hypothesis as a sub-goal (`lib/cure/elab/proof_search.ex`). There is no
separate "positivity solver": `multiplying_positive_numbers_is_positive` already
goes through this same generic path today (it is `@lemma`-tagged in
`Std.Proof.Math` and nothing else), which is exactly why the new reflection and
connective lemmas need no bespoke seam either — they are additional entries
under the identical mechanism. This design supplies **lemmas**, not a solver.
Two minimal wirings:

1. **Introduction and reflection lemmas carry `@lemma`.** `conjunction_is_true_
   when_both_operands_are`, the two disjunction lemmas, and the "…holds_when_
   boolean_comparison_is_true" reflection lemmas are conclusion-directed, so the
   existing `try_lemma` (unify goal with conclusion, recursively discharge
   premises) applies them directly. No seam change.
2. **Conjunction *elimination* is a context-saturation step, not a search
   direction.** Eliminating a conjunction from the *goal* would force the search
   to guess the other operand. Instead, before search, saturate the local
   context: for each hypothesis of shape `IsTrue(and(left, right))`, add
   `IsTrue(left)` and `IsTrue(right)` (via the two `…_from_true_conjunction`
   lemmas). This is a small, terminating structural pass in `ProofSearch`
   (decompose-then-search), and it is what makes an open
   `IsTrue(and(0 <= n, n <= 100))` *hypothesis* usable to prove either half.
   It introduces no backtracking and no new solver.

## 6. Scope boundary — what needs axioms and is therefore deferred (honest ledger)

**Out of scope, deferred to a future *ledgered* trust decision:** a **static**
proof about **abstract primitive-`Int`** arithmetic held in primitive form — the
`∀ a b : Int. a > 0 → b > 0 → a * b > 0` shape where the value must remain a
primitive `Int` and is neither re-represented as `Nat` nor runtime-decided
(the `moneta`/`scale` case under a forced primitive representation). Reaching it
requires a small audited set of trusted reflection axioms — the `Int ↔ Nat`
homomorphism-on-the-non-negative-cone interface:

- `is_positive_of_integer_reflects(n: Int) : IsTrue(n > 0) ↔ IsPositive(of_int(n))`
- `of_int` is additive on the cone: `n >= 0 → m >= 0 → of_int(n + m) = plus(of_int(n), of_int(m))`
- `of_int` is multiplicative on the cone: same guards, `of_int(n * m) = multiply(of_int(n), of_int(m))`

Each is a **named ledger entry with its non-negativity guard** (the guard is
load-bearing: `of_int(2 + (-1)) = 1` but `plus(of_int 2, of_int(-1)) = 2`, so the
homomorphism is false off the cone), and each is **property-testable** on
concrete non-negative integers even though it is unprovable. This is the honest,
minimized successor to SMT — trust as a handful of auditable, tested equations
rather than an opaque oracle. **It is not built here.** It is recorded so the
boundary is explicit and so the interface is designed before it is ever trusted.

Why deferring is parity, not regression: the deleted SMT refinements could not
soundly discharge this nonlinear-over-primitives case either (the
`th-lemma`-without-certificate case), and the int-refinement prelude already
scoped it out for the same reason.

## 7. The refinement→base projection coercion (item (c); axiom-free, orthogonal)

Independent of the reflection work and equally trust-free: a refined value
`{refined_value: T | predicate}` is a `Sigma`, and today it cannot be used where
its base type `T` is expected (`conversion_failure` — the symmetric companion to
the int-refinement level-2 base→refined injection). Add an elaborator coercion:
when checking a term whose inferred type is `Sigma(refined_value: T,
predicate(refined_value))` against an expected type `T`, insert the first
projection — the kernel builtin `sigma_first`, the same global the level-1
refinement-type sugar and the generic `.1` projection already lower to
(`declarations.ex`'s `idx_to_core` clause for `{:attribute_access, meta, [inner_ast]}`,
which reads the `"1"`/`"2"` selector from `meta`'s `:attribute` key and dispatches
to `:sigma_first`/`:sigma_second` accordingly). Using
the builtin directly, rather than `Std.Refine.refined_value`, keeps the
coercion independent of whether the enclosing module `use`s `Std.Refine` — a
refined value built purely from the level-1 `{n: Int | n > 0}` sugar never
requires that import, so the coercion that unwraps it must not either. Pure E
change in `elaborator.ex` (a coercion site, alongside the existing injection),
no trust, no kernel touch. This is what unblocks a refined parameter flowing into ordinary
`T`-typed arithmetic — the other half of making refined values usable, and the
concrete `moneta` blocker from the int-refinement §8 ledger (that ledger's own
sub-item "(a)", a different letter scheme from this design's (a)/(b)/(c) above —
not to be conflated).

## 8. Testing strategy (TDD, differential oracle where it applies)

Strict red→green per slice; behavioral and immutable once green.

1. **Connective algebra (Layer 1).** Unit tests: from `IsTrue(and(a, b))` derive
   each operand; from both operands derive the conjunction; disjunction from
   either side; `true_negation_contradicts_truth` yields `Empty`. Oracle probe
   `test/oracle/refine/refine03_boolean_and.{cure,idr}` /
   `refine04_boolean_or.{cure,idr}` (numbered-prefix naming, matching the
   directory's existing `refine01_is_true`/`refine02_is_false` convention)
   against Idris `Data.So` `andSo`/`orSo`, relation `same`.
2. **Nat reflection (Layer 2).** Unit tests: each `…_holds_when_boolean_
   comparison_is_true` and its converse round-trip on concrete `Nat`; a *proof*
   of `IsLessThan` obtained through the boolean surface equals the hand-written
   one (structural equality). Oracle probe
   `test/oracle/refine/refine05_nat_reflection.{cure,idr}` (same numbered-prefix
   convention) against agda-stdlib-style reflection expressed in Idris
   `Data.Nat`/`Data.So`, relation `same`.
3. **`to_integer`.** Unit test totality + round behavior (`to_integer(of_int(k))`
   on non-negative `k`); a structural, non-`@extern` definition (guard: the
   function has a real body, not an FFI boundary).
4. **Automation.** An open `IsLessThan(a, b)` goal with an `IsTrue(natural_is_
   less_than(a, b))` hypothesis discharges via the `@lemma`-tagged reflection
   (codegen-ready gate, red without the tag). An open `IsTrue(and(p, q))`
   *hypothesis* lets either half discharge after context saturation (red without
   the saturation pass).
5. **Refinement→base coercion (§7).** A refined `{n: Int | n > 0}` parameter used
   in `n + 1` type-checks (red today with `conversion_failure`); a non-refined
   mismatch still fails.
6. **Layer 3 example.** A worked `decide_is_true`-at-boundary demo compiles and
   both branches type-check.
7. **Full gate once, alone.** `mix test --include slow` + `mix antigen` + oracle
   replay green.

## 9. Files

- **Create:** `lib/std/proof_boolean_reflection.cure` (`use Std.Bool`, `use
  Std.Decision` for `Empty`, `use Std.Proof.IntMath` for `IsTrue`/`Confirmed` —
  per the codebase's must-import convention, every one of these is a direct,
  explicit import: `Std.Proof.IntMath` already imports `Std.Decision` itself,
  but that import is not transitive, matching how `Std.Proof.Math` and
  `Std.Proof.IntMath` each import `Std.Decision` directly for the same
  `Empty`);
  `test/cure/stdlib/proof_boolean_reflection_test.exs`;
  `test/cure/stdlib/nat_to_integer_test.exs`;
  `test/cure/elab/refinement_base_projection_test.exs`;
  `test/oracle/refine/refine03_boolean_and.{cure,idr}`,
  `refine04_boolean_or.{cure,idr}`, `refine05_nat_reflection.{cure,idr}`
  (numbered-prefix names, matching the directory's existing
  `refine01_is_true`/`refine02_is_false` convention) — all three add entries to
  the *existing single* `test/oracle/refine/verdicts.json` (one shared,
  name-keyed JSON object per directory — not a separate file per test).
- **Modify (stdlib):** `lib/std/proof_math.cure` (boolean comparisons + reflection
  lemmas; add `use Std.Proof.IntMath` for `IsTrue`); `lib/std/nat.cure`
  (`to_integer`).
- **Modify (E):** `lib/cure/elab/proof_search.ex` (context-saturation pass for
  `IsTrue(and …)` hypotheses; the new lemmas are picked up via their `@lemma`
  tags — confirm no seam edit needed); `lib/cure/elab/elaborator.ex`
  (refinement→base projection coercion).
- **Untouched:** `lib/cure/core/*` (K). Any perceived need to edit it is a
  hard-stop and a scope violation — especially while certificate checking is in
  flight.

## 10. Non-goals

- **No new axioms, postulates, `@extern`, or `believe_me`.** Zero new trust.
- **No kernel change.** `lib/cure/core/*` is untouched.
- **No `Int → Nat` homomorphism interface** (§6) — designed, ledgered, not built.
- **No solver.** Existing `ProofSearch` applies the new lemmas; the only addition
  is a terminating structural context-saturation pass.
- **No static discharge of abstract primitive-`Int` arithmetic** in primitive
  form (§6) — use a `Nat` carrier, or decide at the boundary (§5b).
- **No `implies` connective lemma** unless `Std.Bool` gains `implies`; implication
  is `or(not(left), right)` and composes from the shipped lemmas if needed.

## 11. Summary

Three constructive layers — the boolean-connective algebra, the `Nat` reflection
bridge, and runtime decision at boundaries — plus a free structural `Nat → Int`
projection and an axiom-free refinement→base coercion, let open refinement
obligations draw on the full inductive lemma library with **zero new trust and no
kernel change.** The one case that genuinely needs trust (static abstract
primitive-`Int` arithmetic) is designed as a minimized, guarded, testable ledger
interface and explicitly deferred until after certificate checking lands. Every
new name is spelled out in full, because the reader who most needs to understand
a reflection lemma is the one who has never seen one.
