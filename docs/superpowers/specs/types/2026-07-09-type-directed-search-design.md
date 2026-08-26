# Type-Directed Search — Instance & Hint Resolution (Elaborator Engine)

**Date:** 2026-07-09
**Status:** design (operator-directed). A reusable E-layer component. Its
**first and only built-now client** is typeclass instance resolution
([`2026-07-09-typeclasses-elaborator-feature-design.md`](2026-07-09-typeclasses-elaborator-feature-design.md)
§6, which references this spec). Other clients (§6) are **reserved, not built**.

**One-line decision:** goal-directed proof/term search over registered hint
databases lives in the **untrusted elaborator**; it produces a candidate Core
term that the **kernel checks**. Search may be arbitrarily heuristic,
incomplete, or buggy without threatening soundness — a bad search fails or
yields a rejected term, never an unsound proof. This is the LCF discipline and
the Coq/Idris/Lean architecture (`eauto` + hint databases, `%hint` + `auto`,
`aesop`).

---

## 1. Purpose and boundary

Several elaborator tasks are the same shape: *given a goal type, construct a
term of that type by applying registered rules, backtracking on failure.*
Typeclass instance resolution is the well-behaved special case; general lemma
search (for refinement obligations and `auto`-style goals) is the powerful
superset. This spec defines the one engine both use, so we build the seam once
and correctly rather than hard-coding a resolution loop inside typeclasses that
later fights generalization.

**Trust boundary (the load-bearing property):** the engine is entirely
untrusted. Every term it returns is re-checked by `Cure.Core.Kernel` before
use, exactly as a hand-written term would be. Therefore:

- Incompleteness is acceptable (an unsolved goal is a typed error, never
  unsoundness).
- Heuristics, priorities, and fuel limits are free to tune — they change *what
  is found*, never *what is trusted*.
- This is strictly stronger than the retired Z3 lint, which was
  trusted-but-unchecked. Here search is untrusted-**and**-checked.

This is the same lesson as the typeclass and effect specs: the kernel checks,
the elaborator searches. The kernel gains nothing from this spec.

## 2. The engine

A backward, goal-directed search:

```
solve(goal, db, fuel) :
  1. if fuel = 0 → fail
  2. try each hint h in db whose conclusion head unifies with goal, by priority:
       - unify h's conclusion with goal (may bind metavariables)
       - for each premise pᵢ of h (in order): solve(pᵢ, db, fuel-1)
       - if all premises solved → return  h applied to the subproofs
       - else backtrack to the next hint
  3. if no hint succeeds → fail
```

Components:

- **Hint** = a registered global definition usable as a rule: its type is read
  as `∀ params. premise₁ → … → premiseₙ → conclusion`. An instance
  (`dict_C_τ`), an arithmetic lemma (`mul_nonneg`), or a plain constructor can
  all be hints.
- **Hint database** = a named set of hints with per-hint priority. Multiple
  databases (e.g. `instances`, `arith`) so a client searches only the relevant
  set (Coq's `with` selection).
- **Unification / matching** = the existing elaborator unifier
  (`lib/cure/elab/unify.ex`), reused. Higher-order goals restrict to pattern
  fragments where matching is decidable (§4).
- **Fuel / depth bound** = a hard recursion limit; exhaustion is a typed
  "could not resolve" error carrying the residual goal, never a loop.
- **Result** = a Core term. The caller feeds it to the kernel, which is the
  actual soundness gate.

## 3. Two profiles over one engine

The engine is parameterized so the constrained and general cases don't pay for
each other:

| profile | database | goal shape | backtracking | fuel | coherence |
|---|---|---|---|---|---|
| **instance resolution** | `instances` | `Dict_C(τ)`, class-headed | none (coherence ⇒ ≤1 match) | shallow | one instance per `(class, head)` |
| **hint / lemma search** | `arith`, user dbs | arbitrary proposition | full backtracking | deep, tunable | N/A (multiple lemmas expected) |

Instance resolution is the profile that must be **predictable**: coherence
(§ typeclasses spec §8.2) guarantees at most one matching instance per
`(class, type head)`, so it is deterministic and needs no backtracking — the
reliability typeclass users expect. General search accepts nondeterminism and
backtracking as the price of power. **Same `solve/3`, different knobs.** The
open design choice — whether instance resolution is `solve` with settings
(Coq's `typeclasses eauto`) or a thin deterministic core sharing only the
unifier — is decided in implementation and recorded here (§8 ledger #1); the
spec commits only to the shared substrate, not to that internal cut.

## 4. Termination and decidability

- **Fuel is mandatory**, not advisory — the backstop against divergent search.
- **Instance profile**: additionally require decreasing instance heads
  (structural recursion on the type argument), as Idris/Lean do, so resolution
  terminates independently of fuel for well-formed instance sets.
- **Higher-order matching**: restrict to Miller pattern unification (the
  fragment the existing unifier already handles decidably); goals outside it
  fail cleanly rather than guessing. General higher-order proof search is out
  of scope.
- **No solver, ever.** This engine is syntactic rule application, categorically
  distinct from SMT. It never calls Z3/cvc5 and shares no code with the retired
  refinement machinery.

## 5. Hint registration

- **Instances** register into `instances` automatically when an
  `implementation` elaborates (typeclasses spec §5).
- **Lemmas / user hints** register via an attribute on an ordinary definition
  — e.g. `@hint(:arith)` on `mul_nonneg` — placing it in a named database with
  optional priority. (Surface syntax ledgered §8 #2; `@hint` illustrative.)
- Registration is **elaborator metadata**, not a kernel concept: the kernel
  holds these as ordinary global defs; only the E-layer knows they are
  searchable. "Positing lemmas to the kernel" = registering globals + tagging
  them as hints.
- A hint is only ever as good as its proof: a hint *is* a kernel-checked
  definition, so a wrong "lemma" cannot be registered unless it typechecks —
  the DB cannot be poisoned with false facts.

## 6. Surface: `by search` (compute-first)

The engine's surface entry point is the tactic **`by search`**, written where a
proof is expected. The name states the mechanism — it *searches* — which is the
whole reason it isn't Lean's opaque `simp`. Its semantics are **computation
first, search only when needed**:

1. Try to close the goal by computation (whnf / reflexivity). E.g. `So(5 > 0)`
   normalizes to `So(True())`, inhabited by `Oh()`. If this closes the goal,
   done — **no search runs**.
2. Otherwise, run hint search (§2) over the relevant database.
3. If search fails, a typed error carrying the residual goal (§8 ledger #5,
   diagnostics) — never a loop, never a silent pass.

The consequence is the intended rule: **a refinement pays for proof search only
when its obligation is not decidable by computation.** Concrete/literal
refinements (`five() -> {r | r>0} = 5`) close in step 1 with zero search;
abstract ones (`scale`, `x*k ≥ 0`) fall to step 2.

This is what lets the desugaring macro stay **uniform and dumb**: it *always*
emits `by search` on the obligation it generates and never inspects the
predicate. Step 1 makes `by search` a no-op wherever the goal is already closed,
so "always emit it" costs nothing on the concrete cases and does the right thing
on the abstract ones — `by search` absorbs the decision the macro would
otherwise have to make.

```cure
%[5, by search]           # macro-emitted; step 1 (computation) closes it, no search
%[x.1 * k.1, by search]   # macro-emitted; step 2 finds mul_nonneg in `arith`
```

In hand-written code `by search` appears only where the author wants
automation, so its presence in source is informative — it marks exactly the
spots where the compiler did non-trivial proof work. (A `by search` on an
already-computationally-closed goal is a successful no-op; whether to warn on a
redundant hand-written one is ledgered §8 #6.)

## 7. Clients

**Built now:**

1. **Typeclass instance resolution** — the instance profile (§3). The
   typeclasses spec's §6 defers to this engine.

**Reserved (named so the design stays honest; NOT built here):**

2. **Refinement `So(…)` discharge** — if `{x: T | φ}` sugar is re-added
   (dropped in the post-parity teardown; re-addition unqueued), the desugared
   `So(φ)` obligation is discharged by: computation first (concrete cases,
   `Oh()` by whnf), then hint search over `arith` (applies pre-proven lemmas
   like `mul_nonneg` — this is how certified **nonlinear** coverage is obtained
   without a solver: the nonlinear content is proven once, in the lemma, and
   search only *applies* it), then manual proof (which grows the DB). Its own
   client spec when queued.
3. **Verified linear decision procedure** — a reflection-based `omega`/
   `linarith` procedure, *complete* for linear integer arithmetic, run by
   computation. Distinct from hint search (a decision procedure, not rule
   application) but a sibling automation rung for the same refinement client.
   Own spec when queued.
4. **General `auto` tactic** — user-invoked proof search for explicit goals.
   Reserved.

The completeness/certifiability trade for clients 2–4: hint search is
*incomplete* (only what the DB covers) but every result is kernel-checked and
the DB grows monotonically as users prove new lemmas — the Mathlib/Idris-prelude
accretion model. This is the deliberate inverse of SMT (more complete, but
uncertifiable on exactly the nonlinear cases that matter).

## 8. Ledger (open decisions)

1. **Instance profile factoring** — `solve` with settings vs. a thin
   deterministic instance core sharing only the unifier (§3). Implementation
   call; affects nothing this spec commits to.
2. **Hint-registration surface** — `@hint(:db, priority)` attribute vs. a
   declaration form; database naming/namespacing; whether users may define new
   databases.
3. **Priority / ordering semantics** — how ties and priorities resolve; whether
   ordering is stable/documented (it must be, for reproducible builds).
4. **Fuel budget defaults** — per-profile depth limits; whether user-tunable
   per call site.
5. **Diagnostics** — an unresolved goal must report the residual obligation and
   the search trace usefully (the typeclass "no instance for `Show(τ)`" error
   and the lemma "no hint produced `So(x*k≥0)`" error come from here).
6. **Redundant `by search`** — whether a hand-written `by search` on a goal that
   step 1 (computation) already closes is silent, or warns "no search needed
   here." Macro-emitted `by search` on closed goals is always silent.

## 9. Non-goals

- No kernel changes — the kernel checks found terms, nothing more.
- No SMT / solver integration — syntactic rule application only.
- No general higher-order proof search beyond the pattern fragment (§4).
- Not building clients 2–4; they are reserved seams, specified when queued.
