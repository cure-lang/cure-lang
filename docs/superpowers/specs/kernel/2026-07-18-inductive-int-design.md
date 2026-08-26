# Inductive `Int` — design

**Branch:** `autopilot/inductive-int` (off `feature/idris-parity`)
**Date:** 2026-07-18
**Status:** design approved → spec review → `writing-plans`

## 0. Motivation

Cure's `Int` is a kernel **primitive**: `lib/std/int.cure` declares
`@builtin(:int) primitive Int`, and `builtins.ex:seed_primitives` installs
`Int → {:int_type}` as a "machine base-type floor" alongside `Float`/`Binary`/
`Atom`. Core node `{:int_type}` is a hardwired type former with *no constructors*
(`shift`/`subst` are no-ops, it evaluates to `{:vint_type}`), `{:int_lit, n}` is
a primitive literal, and arithmetic is a set of seeded builtin ops (`int_add`,
`int_sub`, `int_mul`, comparisons) that fold straight to BEAM operators. Genuine
inductive families (`:nat`, `:bool`, `:list`, …) instead go through
`builtins.ex:seed_builtin` with a constructor schema. Because a primitive has no
constructors, `Int`
admits **no structural induction and no `match`**. That is the root cause behind
a whole family of workarounds: refinements over `Int` could only ever be
discharged by (removed) Z3, by curated positivity lemmas, or by a bespoke
reflected decision procedure — never by ordinary induction, the way facts about
`Nat` are proved.

This initiative replaces primitive `Int` with an **inductive `Int`** that still
compiles to a native BEAM integer, exactly the way `Nat` already works in-tree.
The typechecker gains `match` and structural induction on integers; the runtime
is unchanged (native bignums); the bridge between the two is one audited fold
table. This is precisely Lean's `Int` (`ofNat | negSucc`, `@[extern]`-backed).

Downstream, this is the foundation two other efforts build on:
- The parked **verified LIA reflection** branch (`autopilot/verified-lia-reflection`)
  rebases onto this `Int`; its local `Integer`/`Zed` substrate stops existing and
  its soundness theorem quantifies over the canonical inductive `Int` directly.
- Agent **#4**'s `IsTrue ↔ inductive-family` bridge continues in parallel and is
  *helped*, not obsoleted (§6): its bridge becomes a provable lemma once both
  sides talk about the same inductive `Int`.

## 1. Prior-art models (all local, in-family + the in-tree precedent)

| Model | What it shows | Path |
| --- | --- | --- |
| **Cure's own `Nat`** | THE in-tree precedent: `@builtin(:nat)` inductive family + compact `{:nat_lit}` literal defeq to the spine (`Eval.nat_to_ctor`/`nat_to_ctor_if`) + audited arithmetic fold + codegen lowering `{:nat_lit,n}`→BEAM integer (`Z→0`, `S n→n+1`). | `lib/std/nat.cure`, `lib/cure/core/builtins.ex`, `lib/cure/core/{term,eval,value,normalise,conv}.ex`, `lib/cure/elab/emit.ex:529` |
| **Lean 4 core `Int`** | Canonical two-constructor inductive integer, `@[extern "lean_nat_to_int"]` native-backed | `~/Develop/lean4/src/Init/Data/Int/Basic.lean:46` |
| **Agda stdlib `ℤ`** | Same `+_ / -[1+_]` shape (Pos / NegSucc) | `~/Develop/agda-stdlib/src/Data/Integer/Base.agda` |
| **Rocq `Z`** | Binary `Z0 | Zpos | Zneg` alternative (rejected here, §2) | `~/Develop/rocq/theories/Corelib/Numbers/BinNums.v:68` |

The design is modeled on Cure's own `Nat` machinery (the mechanism already exists
and is proven in-tree); Lean's `Int` is the shape authority. Idris remains the
**differential oracle** (`rel=same`), not the algorithmic model — note Idris's
own `Integer` is a *primitive* bignum and offers no inductive presentation to copy.

## 2. Representation

```cure
@group(:core)
@prelude
mod Std.Int
  @prelude
  @builtin(:int)
  type Int = FromNat(Nat) | NegativeSuccessor(Nat)
  #  FromNat(n)            =  n          (0, 1, 2, …)
  #  NegativeSuccessor(n)  =  -(n + 1)   (-1, -2, -3, …)
```

Two constructors, built on the existing inductive `Nat`. This is **canonical** —
every integer has exactly one representation (zero is only `FromNat(Z())`), so
structural equality stays decidable and the fold table only ever cases on two
constructors.

**Rejected:** Rocq's binary `Z0 | Zpos(Positive) | Zneg(Positive)`. It is
log-size and faster, but needs a whole `Positive` bit-string type and makes every
arithmetic proof heavier. We do **not** need speed in the *proof presentation*
(§3 keeps the runtime native regardless), so the two-constructor form wins on
simplicity. Descriptive names (`FromNat`/`NegativeSuccessor`) per the standing
naming directive, mirroring Lean's `ofNat`/`negSucc`.

## 3. Native-parity mechanism (the crux — mirror `Nat` exactly)

We do **not** ship `FromNat(S(S(…)))` terms at runtime. We mirror the machinery
`Nat` already uses:

1. **Compact canonical value.** `{:int_lit, n}` (which already exists as a Core
   node) becomes the compact canonical form of the inductive `Int`, exactly as
   `{:nat_lit, n}` is for `Nat`. Its typing is `{:int_lit, n} : Int` for any
   `n ∈ ℤ`.
2. **Audited fold `reduce_int`.** The precedent is **not** `Eval.fold`
   (that table is the separate arithmetic/comparison-op folder, §3.3) — it is
   `Eval.nat_to_ctor/1` / `nat_to_ctor_if/1` in `lib/cure/core/eval.ex:244-252`,
   documented in-tree as "the single audited literal→constructor mapping
   (Lean's `toCtorIfLit` / Agda's `matchLitSuc`)." `Nat`'s version peels one `S`
   layer per call (`{:vnat,0}` ⇓ `{:vctor,:Z,[]}`; `{:vnat,n}` ⇓
   `{:vctor,:S,[{:vnat,n-1}]}`, predecessor left compact) and is invoked from
   exactly **four** ι-sites that a `reduce_int`/`int_to_ctor_if` analog must
   also be wired into: `eval`'s own `:case` handling (`eval.ex:119`),
   `Normalise`'s two `ncase` arms (`normalise.ex:279`, `normalise.ex:321`), and
   `conv.ex:107,110` (structural **conversion-checking** — literal-vs-explicit-
   ctor equality during unification, not just case reduction). `conv.ex` is
   the soundness-critical site: it is what actually makes constructor,
   eliminator, and literal *defeq* to each other, and it is currently missing
   from §9's file list.
   - `FromNat({:nat_lit, k})` ⇓ `{:int_lit, k}`
   - `NegativeSuccessor({:nat_lit, k})` ⇓ `{:int_lit, -(k+1)}`
   - **eliminator / `match` on `{:int_lit, n}`:** `n ≥ 0` selects the `FromNat`
     arm binding `{:nat_lit, n}`; `n < 0` selects the `NegativeSuccessor` arm
     binding `{:nat_lit, -n-1}`. This is what gives `match`/induction their
     computational meaning on the compact form — the `Int` analog of
     `nat_to_ctor`/`nat_to_ctor_if`, single-step (no recursive peel needed,
     since `Int` has only the two outermost constructors).
3. **Arithmetic ops.** The existing `int_add`/`int_sub`/`int_mul`/comparison
   builtin ops already fold `{:int_lit}` operands to native BEAM results; they are
   retained and are now understood as the audited computational rule on the
   canonical form of the inductive type.
4. **Codegen — closed vs. open ctor applications differ, and this is new work,
   not "verify, don't rewrite."** `emit.ex` already lowers `{:int_lit, n}` to a
   native BEAM integer, and a **closed** `FromNat`/`NegativeSuccessor`
   application folds to `{:int_lit, _}` before codegen ever sees it (§3.2) —
   generated code for those is genuinely unchanged. But an **open** application
   (e.g. `fn to_int(n: Nat) -> Int = FromNat(n)`, or the constructor terms an
   induction proof builds in its own inductive step) reaches `emit.ex` as a
   literal `{:ctor, :FromNat/:NegativeSuccessor, [n]}` Core node that **cannot**
   fold at compile time. `emit.ex`'s existing per-family erasure hooks
   (`nat_ctor?`/`bounded_ctor?`, `lib/cure/elab/emit.ex:1079-1092`) dispatch
   **by arity** — `[] -> 0`, `[n] -> lower(n)+1` — because `Nat`'s `Z`/`S` and
   `Bounded`'s `First`/`Next` each have exactly one 0-ary and one 1-ary
   constructor, so arity alone disambiguates. `Int`'s two constructors are
   **both 1-ary** (`FromNat(Nat)`, `NegativeSuccessor(Nat)`) — arity cannot
   tell them apart. Phase 1 must therefore add a **new**, **name-keyed**
   `int_ctor?`/lowering case (there is no existing precedent shaped exactly
   like this) that dispatches on the constructor's identity, not its arity:
   `FromNat(n)` → `lower(n)` (the identity — no `+1`, unlike `S`);
   `NegativeSuccessor(n)` → `-(lower(n) + 1)`. This is still small, mechanical,
   and audited by the same one `reduce_int`/erasure-correspondence argument
   (§4) — but it is new code, and the plan must say so rather than assume
   `emit.ex` needs no change.

### 3a. The one open representation question (resolve in the plan)

Currently the *type* `Int` is the primitive former `{:int_type}`, seeded by
`seed_primitives` and special-cased across the kernel (literal typing, the
builtin-op signatures, and the sites enumerated in (i) below). `Nat`, by
contrast, has a single spelling:
its type *is* the inductive family seeded by `seed_builtin(:nat, …)`. Two ways to
reconcile:

- **(i) Faithful — move `Int` out of `seed_primitives` into a genuine
  `seed_builtin(:int, …)` inductive family** like `Nat` (and flip
  `lib/std/int.cure` from `@builtin(:int) primitive Int` to the family
  declaration), with `{:int_lit}` as its literal. `Float`/`Binary`/`Atom` stay in
  the primitive-floor cohort — only `Int` moves. Cleanest, most Nat-faithful,
  avoids dual-spelling conversion hazards. Higher blast radius: every
  `{:int_type}`/`{:int_lit}` special-case must be repointed at the family — as
  of this writing that is `lib/cure/core/kernel.ex` (`infer/2` clauses,
  `rigid_index?/1`; note `infer_prim` itself is **already retired**, K2 spec
  2026-07-09 — arithmetic/comparison typing goes through the seeded builtin-op
  globals in `builtins.ex`, not a dedicated prim-typing function), `meta_check.ex`
  (`canonical_head?/1`), `printer.ex`, `quote.ex`, `serialize.ex`, `term.ex`
  (`term?`/`shift`/`subst`/`to_external`/`from_external`), `declarations.ex`
  (`primitive_tag_node/1`), `implementation.ex` (`head_atom/4`), `resolve.ex`
  (`head_type_core/1`), `unify.ex` (`escapes?/3`), and `union.ex`
  (`member_key/1`, `class_of_core/2`) — confirmed by grep, not exhaustively
  audited; the plan's Task 1 should re-grep before starting. **Recommended —
  this is the "just like Nat" the design calls for.**
- **(ii) Facade — keep `{:int_type}` as the canonical type, register the family
  behind it, make the two defeq.** Smaller diff, but introduces a second spelling
  of the same type and the conversion-checker must treat `{:int_type} ≡
  Inductive(Int)`, which is a real soundness-sensitive seam.

Plan Task 1 picks **(i)** and only falls back to **(ii)** if (i)'s blast radius
proves unmanageable under the back-compat gate (§5) — and any fallback is
recorded, not silent.

## 4. TCB analysis

- **What is trusted:** the `reduce_int` fold table (§3.2) — it asserts "the
  inductive eliminator and constructors ≡ the native BEAM integer ops." This is
  the **one TCB addition**, the exact analog of the already-trusted `Nat`
  literal↔constructor mapping (`Eval.nat_to_ctor`/`nat_to_ctor_if`, §3.2).
- **Why it is approved:** it is Lean-aligned (`Int.ofNat` is literally
  `@[extern]`-backed in Lean core), so it falls under the standing
  `tcb-change-blanket-approval` (Idris/Agda/Lean alignment suffices). The change
  is still gated on the full kernel/soundness suite.
- **Why it is sound:** BEAM integers are **arbitrary-precision**. The inductive
  ℤ is unbounded, and BEAM bignums never wrap, so the native ops and the
  inductive semantics coincide on every value. On a fixed-width target this
  correspondence would be **unsound** (wraparound ≠ unbounded ℤ) — this
  requirement is load-bearing and must be stated in the module doc.
- **No new kernel *rule* beyond the fold.** Induction/`match` on `Int` reduces
  via the existing eliminator machinery once the family is registered; if
  anything *seems* to need a new kernel rule beyond `reduce_int`, that is an
  elaborator-hard-stop: STOP and report.

## 5. Back-compat — the hard gate

Every existing `Int` program — all of stdlib, every example, the phase demos —
MUST typecheck and compile **byte-identically**. `{:int_lit}` and the constructor
forms are fully interchangeable through the fold, so:

- `5 : Int` stays `{:int_lit, 5}`; `a + b`, `a < b : Bool` fold exactly as before.
- Generated BEAM for every program expressible **today** (none of which uses
  `FromNat`/`NegativeSuccessor` — they don't exist yet) is unchanged, since
  today's programs only ever produce `{:int_lit}` and the existing builtin-op
  forms. New surface use of the constructors (Phase 1's own smoke-test
  included) exercises the **new** name-keyed codegen case from §3.4, which is
  additive, not a back-compat concern — but it is a new runtime code path, not
  a "codegen already targets `{:int_lit}`, nothing to do" claim.

**The gate is:** the full existing test suite stays green (kernel/soundness
suite, stdlib, oracle replay `rel=same`, Antigen), with **no** expected-output
churn attributable to `Int` re-representation. Any regression that is not a
*provably equivalent* re-spelling is a **Halt condition**, not a fixup — a
back-compat regression means the fold or the family registration is wrong.

## 6. Coexistence with `IsTrue` and agent #4

`IsTrue`/`Confirmed` (`Std.Proof.IntMath`) **stays** and is untouched by this
initiative. It is not an `Int` workaround — it is (a) the generic decidable-`Bool`
predicate reflector (Idris `So`), and (b) the refinement-type surface encoding
`{x: T | φ}` ≡ `Sigma(T, λx. IsTrue(φ))` for *every* base type. Inductive `Int`
slots in *underneath* it as the proof layer that lets *open* arithmetic
`IsTrue`-claims be discharged by induction.

Agent #4's `IsTrue ↔ inductive-family` bridge runs in **parallel** and coexists.
This initiative defines the `Int`-side order theory (§7 Phase 2) freely; #4's
bridge becomes a *provable* lemma against it later rather than a stopgap. This
spec does not modify #4's files or `IsTrue`'s semantics — the type, its
constructor, and `decide_is_true` are untouched.

**Doc-comment exception (in scope, semantics untouched):** two files carry
prose that hardcodes "`Int` is primitive" and goes stale once Phase 1 lands —
`lib/std/proof_int_math.cure`'s module doc ("`Int` is a primitive, not an
inductive, so it admits no structural induction") and `lib/std/nat.cure`'s
`of_int` doc ("A primitive machine `Int` is not structurally well-founded, so
this is an asserted FFI boundary"). Phase 1 MUST update both comments to match
reality (`of_int`'s *behavior* stays exactly as-is — it remains the trusted
clamp-to-`Z` FFI boundary regardless of `Int`'s representation, since the
inductive family still has no upper bound and `of_int` still has to clamp
negatives; only the prose describing *why* is stale). This is a doc-only edit,
not a semantic change to `IsTrue` or `#4`'s bridge — do not read the
"untouched" rule above as blocking it.

## 7. Scope & phasing — single plan, two sequenced phases

**Phase 1 — Substrate (must land green before Phase 2 begins).**
`Std.Int` inductive family + `{:int_lit}` canonical form + audited `reduce_int`
fold + native codegen + §3a resolution. Deliverable: `match`/induction on `Int`
works, and the full existing suite is byte-identically green (§5). Includes a
**minimal induction smoke-test**: one or two trivial lemmas proved *by induction
on `Int`* (e.g. `negate(negate(i)) = i`), oracle `rel=same`, purely to prove the
substrate genuinely enables induction and defeq-to-literal. No arithmetic theory
beyond that.

**Phase 2 — Ordered-ring lemma kit (on top of the green Phase-1 substrate).**
The reusable order/ring theory on `Int`, the shared dependency of LIA and #4:
an order family (`IsLessThanOrEqual`/`IsLessThan` on `Int`, or the reflected
`IsTrue`-form), plus: add-monotonicity, transitivity, reflexivity,
nonneg-scaling monotonicity, sign lemmas, and the `0 ≤ -1` contradiction
extractor. Each an ordinary dependent proof, Idris-mirrored `rel=same`. This is
genuine long-pole proof work; a proof wall is an elaborator-hard-stop (apply
index-generalization inversion first, then Halt with the exact stuck lemma).

**Out of scope (follow-on, not this plan):** rebuilding the LIA checker on the
new `Int`; migrating the refinement-surface desugaring; any change to `IsTrue`
or #4's bridge.

## 8. Testing & oracle discipline

- **Phase 1 correctness gate = the existing full suite, byte-identical green**
  (§5). This is the primary and non-negotiable check for the substrate.
- **Differential oracle:** paired `.cure`/`.idr` probes under `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/`
  (e.g. `int_inductive.{cure,idr}`), ``mix otp.oracle` in `cure-otp`` + the replay check,
  `rel=same` before each commit. Idris2 at `~/Develop/Idris2/build/exec/idris2`.
  Phase 1 probe: `match` on `Int` + the induction smoke-test compute/prove as
  asserted. Phase 2 probes: each order/ring lemma applied to closed instances.
- **Red-green for proofs:** "red" = the module fails to compile (unfilled hole /
  type error at the theorem signature) and/or the oracle probe does not replay;
  "green" = compiles + `rel=same`. Probes are immutable once their expected
  outcome is fixed — reach green by fixing the proof, never by weakening the
  statement.
- **One build at a time.** Never run concurrent full suites.

## 9. Layer map & files

- **Modify:** `lib/std/int.cure` — flip `@builtin(:int) primitive Int` to the
  inductive family `type Int = FromNat(Nat) | NegativeSuccessor(Nat)`, then add
  Phase-1 ops/smoke-test and the Phase-2 kit. Author in `lib/std/` (NEVER
  `priv/std`, which is generated).
- **Kernel/TCB:** `lib/cure/core/builtins.ex` (move `Int` out of
  `seed_primitives`; add `seed_builtin(:int, …)` with the FromNat/NegativeSuccessor
  schema, mirroring `:nat`), `lib/cure/core/{term,eval,value}.ex` (the
  `reduce_int` fold + `{:int_lit}` literal handling), `lib/cure/core/normalise.ex`
  (the two `ncase` ι-arms) and `lib/cure/core/conv.ex` (literal-vs-ctor
  conversion-checking — see §3.2), and the full `{:int_type}`/
  `{:int_lit}` repoint of §3a(i): `lib/cure/core/kernel.ex`, `meta_check.ex`,
  `printer.ex`, `quote.ex`, `serialize.ex` (all confirmed live special-case
  sites — see §3a for the specific functions), plus
  `lib/cure/elab/{declarations,implementation,resolve,unify,union}.ex`.
  `lib/cure/elab/emit.ex` — `{:int_lit}` lowering (line 525) is unchanged, but
  a **new** name-keyed `int_ctor?` case is required for open constructor
  applications (§3.4); this is new code, not a verify-only site.
- **Doc-only (§6):** `lib/std/proof_int_math.cure`, `lib/std/nat.cure` —
  refresh the two stale "`Int` is primitive" comments; no semantic change.
- **Steer:** work in `lib/cure/core/*` + `lib/cure/elab/*`. IGNORE
  `lib/cure/compiler/*` and `lib/cure/types/*` (non-dependent decoys).
- **Tests:** `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.{cure,idr}` (+ Phase-2 probes).
- **Ghost commits:** author as the user only (`--author="Made In Heaven
  <madeinheaven@madeinheaven.com>"`), no `Co-Authored-By`, explicit-pathspec
  staging.

## 10. Non-goals

- Rocq-style binary `Z` representation (§2).
- Rebuilding LIA / migrating the refinement surface / touching `IsTrue` or #4 (§6, §7).
- Any fixed-width / machine-word integer semantics (§4 — soundness needs bignums).
- Runtime performance work beyond parity with today's primitive `Int`.

## 11. Definition of done

- **Phase 1:** `Std.Int` is an inductive `@builtin(:int)` family; `match` and
  structural induction on `Int` work; the induction smoke-test proves + replays
  `rel=same`; the **entire existing suite is byte-identically green** with no
  `Int`-re-representation churn; the `reduce_int` fold is documented as the sole
  TCB addition with its bignum-soundness caveat.
- **Phase 2:** the ordered-ring lemma kit is proven in Cure, each lemma
  Idris-mirrored `rel=same`, suite green. The kit's public lemma names/signatures
  are documented so LIA and #4 can consume them.

## 12. Risks & Halt conditions

- **Back-compat regression** (§5) that is not a provably-equivalent re-spelling →
  Halt (the family/fold is wrong; do not paper over).
- **§3a approach (i) blast radius** unmanageable → fall back to (ii), recorded.
- **`reduce_int` cannot be given a sound audited rule** without a kernel rule
  beyond the fold → elaborator-hard-stop, Halt.
- **Phase 2 proof wall** the index-generalization technique cannot route around →
  Halt naming the exact stuck lemma; Phase 1 remains valid, committed, and useful.
