# Int Refinement Prelude (decidable-boolean reflection) — Design

**Date:** 2026-07-18
**Status:** LANDED (UNMERGED, branch `implicit-goal-solving`). Prelude + level-1
sugar + level-2 auto-discharge + differential oracle shipped and green.
`dependent_types.cure` re-refined and **un-skipped** (now a live checked example,
`main() == 6`). Two acceptance sites scoped out with honest reasons — see §8.
**Layer:** Stdlib (`lib/std/*.cure`) + parser (P) + elaborator (E) + oracle fixtures + example re-refinement. **No kernel (K) change** — `lib/cure/core/*` is untouched; if a change seems to require it, STOP per the elaborator-hard-stop principle.

**Superseded framing:** an earlier draft said "no E change expected." That is retired. Making the natural surface work needed, and the operator approved, three untrusted changes below the stdlib:
- **P** — comparison/boolean operators parse inside a type-application argument (`-> IsTrue(5 > 0)`), reparsing the argument as an expression when a proposition operator trails a type (`parser.ex`, landed `6ea68573`).
- **E1 (index lowering)** — `idx_to_core` structurally lowers a comparison/connective index to the same Int-builtin Core spine the term elaborator emits (`declarations.ex`).
- **E2 (refinement sugar, §3a)** — the `{x: T | φ}` desugarer auto-wraps a `Bool`-typed clause `φ` in `IsTrue(φ)`, so the author writes `{n: Int | n > 0}` (level 1), and a **closed** obligation on a value checked at a refinement type is auto-discharged with `Confirmed()` by computation (level 2). This is the ergonomic surface and it dissolves the `refine`-implicit-predicate discharge friction (a bare literal never routes through `refine`'s unsolved `{predicate}` implicit).

## 1. Goal

Close the one real gap between the restored proof-backed refinement surface and
feature parity with the deleted SMT refinements: **refinements are usually stated
over `Int`, but the proposition/lemma prelude is entirely over `Nat`.** Today
`Std.Proof.Math` proves `IsPositive`/`IsLessThan(OrEqual)` only for `Nat`, so an
`{n: Int | …}` refinement — the common case, and what every deleted example used
(`dependent_types`, `motif`, `moneta`) — has no foundation to discharge against.
Those examples currently sit as plain `Int` aliases with "unchecked pending
SMTCoq" comments. This builds the Int foundation and re-refines them as the
acceptance demo.

## 2. The Nat-vs-Int decision (the gating question §5.1 flagged)

`Int` in Cure is a **primitive** (`{:int_type}`, native BEAM integer), not an
inductive. There is no structural induction on it, which is exactly why the
classic-deletion spec called Int "proof-hostile vs Nat." Two candidate routes:

- **(A) Nat-bridge** — map `Int → Nat` and reason on `Nat`. Rejected: requires
  `IntToNat`/`NatToInt` with round-trip lemmas, and the kernel still cannot
  *compute* on an abstract `Int`, so the bridge buys nothing for the abstract
  case while taxing the closed case (which already computes fine).
- **(B) Decidable-boolean reflection (CHOSEN)** — reflect the primitive
  comparison, which already returns the inductive `Bool`, into a proposition.
  This is the idiom **all three reference languages use for primitive integers**:
  Idris `So : Bool -> Type` / `Oh : So True`; Agda `T : Bool -> Set`; Lean
  `Decidable` + `decide`. It aligns with the north star and needs no kernel work.

**Why (B) is sound and computes — verified against source, not assumed:**
`lib/cure/core/eval.ex:341` — `vbool(true) = {:vctor, :"Std.Bool#True", []}`. A
closed comparison like `5 > 0` folds to the *inductive* `True()` constructor
value. So a proposition indexed by that Bool — `IsTrue(5 > 0)` — normalizes to
`IsTrue(True())`, and its sole constructor `Confirmed : IsTrue(True())` inhabits
it **by pure computation** (whnf + delta — path 1 of the deletion spec). No
solver, no postulate, no kernel change.

## 3. Surface

New module `Std.Proof.IntMath` (sibling to `Std.Proof.Math`; Nat stays where it
is). Descriptive names per the standing naming directive — the Idris `So`/`Oh`
become `IsTrue`/`Confirmed`.

```
mod Std.Proof.IntMath
  use Std.Bool
  use Std.Int       # `>`, `>=`, `<`, `<=`, `==` on Int → Bool
  use Std.Decision

  ## Evidence that a decided Boolean condition holds. The reflection primitive:
  ## a closed condition reduces to True() and is inhabited by computation; an
  ## open condition is carried as evidence by whoever constructs the value.
  type IsTrue indices (claim: Bool)
    Confirmed : IsTrue(True())

  ## Int refinement predicates, each reflecting the primitive comparison.
  ## These stay available for callers who want a named predicate, but the sugar
  ## in §3a means a refinement can also state the bare comparison inline.
  fn is_positive(n: Int) -> Type = IsTrue(n > 0)
  fn is_non_negative(n: Int) -> Type = IsTrue(n >= 0)
  fn is_non_zero(n: Int) -> Type = IsTrue(n != 0)
  fn is_in_range(low: Int, high: Int, n: Int) -> Type = IsTrue(and(low <= n, n <= high))

  ## Decide a condition, carrying evidence in the Yes branch (Nat-style ergonomics).
  fn decide_is_true(claim: Bool) -> Decision(IsTrue(claim)) = match claim
    True()  -> Yes(Confirmed())
    False() -> No(fn(evidence) -> absurd_true_is_false(evidence))
```

## 3a. Refinement surface sugar (operator-approved: "Both")

Requiring `{n: Int | IsTrue(n > 0)}` leaks the `So`-reflection encoding through
the refinement bar. Every system with a *native* refinement binder takes the
bare boolean/prop and reflects it: Liquid Haskell `{v:Int | v > 0}`, F\*
`x:int{x > 0}`, Lean `{n : Int // n > 0}`. (Idris/Agda write `So`/`T`
explicitly only because they hand-roll a `Subset`/`Σ` with no refinement
syntax — which Cure has.) Cure joins the native-binder camp.

**Level 1 — auto-wrap the clause.** In the `{x: T | φ}` desugarer: elaborate
`φ`; if it has type `Bool`, use `IsTrue(φ)` as the predicate; if it already has
type `Type` (e.g. `IsSorted(xs)` or a user proposition), use `φ` unchanged. So
`{n: Int | n > 0}` and `{n: Int | IsTrue(n > 0)}` are equivalent, and
non-boolean propositions still pass through. This also consolidates lowering:
the clause goes through the *term* elaborator once at the desugaring site, which
is the canonical path for the reflected comparison (the §-E1 `idx_to_core`
structural lowering remains only for comparisons that appear as bare type-family
*indices*, not behind the refinement bar).

**Level 2 — auto-discharge closed obligations.** When a value is checked against
a refinement type `{x: T | φ}` and the obligation `φ[x := value]` is *closed*, it
reduces by computation — `IsTrue(50 > 0)` → `IsTrue(True())` — so the elaborator
fills the proof with `Confirmed()` automatically. The author writes `50` at
`{n: Int | n > 0}`; no `refine`, no `Confirmed()`. This is the SMT-parity
ergonomic for the closed case, and it is why the acceptance demo does not depend
on fixing `refine`'s `{predicate}` implicit inference: a bare literal constructs
the underlying Σ directly and never routes through that unsolved implicit.

**`refine(value, proof)` stays** as the explicit-evidence path for *open* terms
(binder-carried evidence, the `scale` shape), where the obligation cannot reduce
to a closed `True()` and the author supplies the witness.

**Boundary of auto-discharge:** level 2 fires *only* when the reduced obligation
is `IsTrue(True())` (whnf + delta decides it). If it reduces to `IsTrue(False())`
the value is rejected (the refinement is violated); if it is stuck/open (mentions
a free binder), the elaborator does **not** invent a proof — it leaves the
obligation for the author's explicit evidence or `refine`. No solver, no
postulate, no kernel change.

## 4. Scope boundary (the honest limit, unchanged from SMT)

- **In scope — discharges by computation:** any refinement whose obligation is
  closed at the constructing site — literals (`Percentage` of `50`), and
  binder-carried evidence threaded through (`scale`'s `factor` carrying
  `IsTrue(factor > 0)`). This is the bulk of what the examples need.
- **Out of scope — deferred to the §5.2 verified linear decision procedure:**
  abstract *quantified* Int arithmetic lemmas, e.g. `∀ a b. a>0 → b>0 → a*b>0`
  over primitive `Int`. These are **not constructively provable** over a
  primitive integer without induction, and are exactly the nonlinear
  `th-lemma`-with-no-certificate case the deletion spec noted SMT could not
  soundly discharge either. Deferring them is parity, not regression. The
  auto-lemma search's solver seam (auto-lemma spec §4.2) is where that procedure
  later slots in, behind the same trigger, with nothing here rewritten.

This asymmetry is the whole point of §5.1: closed/decidable Int facts get full
automation now; abstract nonlinear Int facts wait for the decision procedure —
and Nat retains structural-induction lemmas (`Std.Proof.Math`) for the abstract
cases that *can* route through Nat.

## 5. Testing strategy (TDD, differential oracle where it applies)

Strict red→green per slice, behavioral and immutable once green.

0. **Parser (landed `6ea68573`)** — a comparison/connective parses as a
   type-application argument (`test/cure/compiler/comparison_type_arg_parse_test.exs`).
1. **`IsTrue`/`Confirmed` + computation** — paired `test/oracle/refine/int_is_true.{cure,idr}`
   (`.idr` uses `Data.So`/`Oh`), relation `same`. Cure unit test: a closed
   `IsTrue(5 > 0)` type-checks with `Confirmed()`; `IsTrue(5 < 0)` is rejected.
2. **Refinement sugar (level 1)** — `{n: Int | n > 0}` desugars to the same Σ as
   `{n: Int | IsTrue(n > 0)}` (Core-term golden or structural equality of the two
   desugarings); a `Type`-valued clause `{xs: List(a) | IsSorted(xs)}` passes
   through unwrapped; a clause that is neither `Bool` nor `Type` is rejected.
3. **Auto-discharge (level 2)** — a literal `50` checked at `{n: Int | n > 0}`
   type-checks with no explicit proof; `-3` at the same type is rejected; an
   *open* obligation (free binder) is NOT auto-discharged (left for evidence).
4. **`decide_is_true`** — returns `Yes`/`No` with evidence; unit test both branches.
5. **Binder-carried evidence via `refine`** — a function taking a refined binder
   and threading the evidence type-checks through the explicit `refine(value, proof)`
   path. NOTE: the named-predicate form `{n: Int | is_positive(n)}` was superseded
   by the bare sugar (level 1); a `-> Type = IsTrue(n > 0)` *predicate body* still
   fails on comparison-in-term-position (see §8). Named predicates are therefore
   not shipped; the bare comparison surface covers the acceptance cases.
6. **Example re-refinement (acceptance)** — `dependent_types.cure` `NonZero`/
   `Positive`/`Percentage` moved from plain-`Int` aliases (which collided on
   ctor `:Int`, the reason the file was a dependent-gap skip) to distinct
   `{… | …}` refinements with closed literal demonstrators that auto-discharge.
   The file is **removed from `@known_dependent_gaps`** and now runs as a live
   green check; `main()` is byte-identically `6`. `moneta.cure`'s `scale` factor
   is **not** re-refined — see §8 for the two blockers.
7. **Full gate once, alone** — `mix test --include slow` + `mix antigen` + oracle replay.

## 6. Files

- Create: `lib/std/proof_int_math.cure`, `test/cure/stdlib/proof_int_math_test.exs`,
  `test/oracle/refine/refine0{1,2}_*.{cure,idr}` + `verdicts.json`,
  `test/cure/elab/refinement_sugar_test.exs`, `test/cure/elab/refinement_autodischarge_test.exs`.
- Modify (P): `lib/cure/compiler/parser.ex` (landed `6ea68573`).
- Modify (E): `lib/cure/elab/declarations.ex` (`idx_to_core` comparison/literal
  lowering + `reflect_boolean_proposition` level-1 auto-wrap) and
  `lib/cure/elab/elaborator.ex` (`try_discharge_refinement` level-2 auto-discharge).
- Modify: `examples/dependent_types.cure` (re-refined, un-skipped) and
  `lib/mix/tasks/cure.check.examples.ex` (drop `dependent_types` from
  `@known_dependent_gaps`). `moneta.cure` **untouched** — see §8.
- **Untouched:** `lib/cure/core/*` (K). If it needs a change, STOP and report —
  that is a scope violation and a hard-stop per the elaborator principle.

## 7. Non-goals

- No decision procedure / omega (that is §5.2, ledgered).
- No Nat↔Int bridge lemmas.
- No new refinement bar *grammar* (the `{x: T | φ}` syntax already exists; §3a
  changes only how the clause is *elaborated*, not how it parses).
- No auto-discharge of *open* obligations (only closed `IsTrue(True())` fires;
  open/stuck obligations wait for explicit evidence or `refine`).
- No change to `Std.Proof.Math` (Nat) beyond what re-refinement forces.

## 8. Delivered vs. scoped-out (post-implementation, honest ledger)

**Delivered & green:**
- `Std.Proof.IntMath` (`IsTrue`/`Confirmed`/`decide_is_true`/`true_is_not_false`).
- Level-1 sugar (`declarations.ex`) + level-2 auto-discharge (`elaborator.ex`),
  each with unit tests (`refinement_sugar_test.exs`, `refinement_autodischarge_test.exs`).
- Differential oracle cluster `test/oracle/refine/refine0{1,2}_*` (accept/accept,
  reject/reject vs Idris `Data.So`), replay green.
- `dependent_types.cure` re-refined, un-skipped, `main() == 6`.

**Scoped out, with reasons (follow-ups, not workarounds):**
1. **`moneta.cure` `scale`'s `factor`.** Blocked by two independent gaps: (a) a
   *refined parameter cannot be used where its base type is expected* — there is no
   refinement→base projection coercion (`{n: Int | n>0}` used as `Int` fails with
   `conversion_failure`; the symmetric companion to level-2's base→refined
   injection), so `scale_amount(amount, factor)` would not type-check; and (b)
   moneta's build compiles with `check_types: false`, so no refinement is actually
   *verified* there regardless. A refinement→base projection coercion in the
   elaborator (E) is the enabling feature; ledger it before claiming this site.
2. **`moneta.cure` unused typealiases (`PositiveAmount`/`NonNegAmount`).**
   Refining these is cosmetic (unchecked build) AND hits a nested-stdlib-module
   resolution gap: out-of-tree builds (via `CURE_LIB`) fail to resolve
   `use Std.Proof.IntMath` (`Std.Proof.*` nested name → source-path mapping),
   though `Std.String` resolves. In-tree builds (`Program.elaborate`,
   `cure.check.examples`) resolve it fine. Fix the nested-module source mapping
   in the codegen/out-of-tree resolver before importing nested stdlib modules
   from example subprojects.
3. **Named predicates (`fn is_positive(n: Int) -> Type = IsTrue(n > 0)`).**
   A comparison in *term position* inside a `-> Type` body still raises
   `unsupported_expression` (the `idx_to_core` fix covered type/index positions,
   not term-elaboration of a type-family index argument). Superseded by the bare
   sugar for the acceptance cases; if named predicates are wanted, lower
   comparison args of a type-family application through the same reflection path.
