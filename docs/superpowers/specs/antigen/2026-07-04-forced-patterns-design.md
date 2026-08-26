# Forced / Dot Patterns + Forced-Argument Erasure — Design (roadmap #5)

**Date:** 2026-07-04
**Roadmap row:** §2 #5 — "Forced/dot patterns + forced-argument erasure" (K+P+E, additive; no
`lib/cure/compiler/codegen.ex` change — see §4.4 correction).
**Layers touched:** K (kernel `unify_indices`), P (parser dot-pattern syntax), E (elaborator
dot-pattern elaboration **and** the existing `Cure.Elab.Erase` forced-argument erasure pass,
§4.4).
**Verification:** differential oracle (`mix cure.oracle dotpat` vs `idris2 --check`) for the
type-level behaviour; a codegen/run test for erasure (not oracle-measurable, exercises the
E-layer erasure pass end-to-end through codegen). Kernel change carries the **mandatory TCB
gate** (new Antigen antibody + full Antigen suite + full test suite). **Blocking dependency:**
§1.2 documents a pre-existing, independent kernel/declaration-checking defect (the
**auto-generalization defect**) that must be fixed or worked around before the primary oracle
probes can exercise this design — see §5.1.

> **Landed correction (2026-07-04; re-verified 2026-07-17).** The blocking
> auto-generalization defect described below is fixed by `dc2b6355` (`check_result_indices`
> now seeds the family-parameter neutrals, matching `check_ctor_app`). This commit is contained
> in `core-let-binder`. Live verification on 2026-07-17 reports `dp01`, `dp01b`, `dp02`, and
> `dp03` as Cure/Idris `accept/accept`, and `dp06` as `reject/reject`; every `dotpat` relation is
> `same`. Sections retaining “blocked” language are historical diagnosis, not current status.

---

## 1. Goal

Make Cure accept the class of dependent matches where **matching a constructor forces an
equation between the scrutinee's index variables**, exactly as Idris2/Agda/Lean do, and give
the surface language the tools to express and optimise it:

- **K** — teach the kernel's index unifier the *Solution* step so a forced equation
  (`b := a`) is produced instead of silently dropping the equation as `:undecided` (§2.2).
- **P** — accept explicit `.e` dot-pattern syntax so a user can *write* the forced value.
- **E** — elaborate dot patterns: check the written forced value agrees with what
  unification determined; mark forced positions. Route the kernel's forced substitution into
  branch-body elaboration (§4.3), and erase forced constructor arguments at runtime via the
  existing `Cure.Elab.Erase` pass (they are recoverable from an already-matched position, so
  they need not be scrutinised or stored) — §4.4.

### 1.1 The characterised gap (oracle probe `dp01`, this session)

```cure
mod Dp01
  type Nat = Z | S(Nat)
  type MyEq(a: Type) indices (x: a, y: a)
    mrefl : MyEq(a, w, w)
  fn congS({a: Nat}, {b: Nat}, p: MyEq(Nat, a, b)) -> MyEq(Nat, S(a), S(b)) = match p
    mrefl() -> mrefl()
end
```

Idris `--check` **accepts** the equivalent program; Cure **rejects** with
`{:conversion_failure, {:var,1}, {:var,0}}`. Matching `mrefl` should force `b = a` in the
branch (so the body `mrefl() : MyEq(S(a), S(a))` satisfies the goal `MyEq(S(a), S(b))`), but
Cure never derives that equation.

This is **not** covered by the landed #6 (`with`-abstraction) or #26 (inline `match`).

### 1.2 Empirical correction (this review) — `dp01` as written does not reach case-branch checking

Direct invocation of `Cure.Elab.Program.elaborate/1` on the `dp01` source above reproduces
the quoted error exactly — but **not** via `check_case_branches`/`unify_indices`. The
stacktrace at the point of failure is:

```
Cure.Core.Kernel.check/3            (kernel.ex:344, generic conversion-check fallback)
  ← Cure.Core.Kernel.do_spine/3     (kernel.ex:492)
  ← Cure.Core.Kernel.check_result_indices/3   (kernel.ex:961)
  ← Cure.Elab.Declarations.check_all_ctors/3-fun-0-  (declarations.ex:997)
  ← Cure.Elab.Declarations.declare_indexed_at_min_level/6  (declarations.ex:871)
```

This is the kernel's **family-declaration well-formedness check** (`check_ctor/2`,
kernel.ex:409-423, calling `check_result_indices/3`, kernel.ex:959-968) — it validates that
`MyEq`'s constructor `mrefl` is itself well-formed, and runs *before* `congS` (or any
`{:case}` term) is elaborated at all. `check_case_branches`/`unify_indices` is never reached.

Isolating the trigger (three minimal variants, verified by direct `elaborate/1` calls):

| Family shape | Free ctor var repeated across indices? | Result |
|---|---|---|
| `MyEq2(a: Type) indices (x: a)`, `mrefl2 : MyEq2(a, w)` | no (1 occurrence) | **accepts** |
| `Pair2 indices (x: Nat, y: Nat)` (no `Type` param), `same2 : Pair2(w, w)` | yes | **accepts** |
| `MyEq3(a: Type) indices (x: a, y: a)`, `mrefl3 : MyEq3(a, w, w)` (`dp01`'s exact shape) | yes | **fails**, identical `{:conversion_failure, {:var,1}, {:var,0}}` |

So the trigger is specifically **a `Type`-parametrized family whose constructor's
auto-generalized free index variable is repeated across ≥2 index positions** — a
pre-existing, independent defect in constructor-declaration checking, unrelated to
case/pattern forcing. It is not part of this design's scope and is not fixed by §4.1-§4.4;
it must be tracked and fixed separately (call it the **auto-generalization defect**) before
`dp01`/`dp02` (both `MyEq`-shaped) can validate anything in this design. Every subsequent
reference to `dp01`'s "rejection" in this document describes the **intended, post-declaration-fix
symptom** (the forced-pattern gap this design targets), not literally what today's
interpreter does to the `dp01` source as written — see the corrected trace in §2.2 and the
revised oracle-probe scope in §5.1.

A substitute construction that avoids the `Type`-param trigger (drop the `(a: Type)` param,
use two concrete `Nat` indices) —

```cure
mod Dp01Fix
  type Nat = Z | S(Nat)
  type SameLen indices (n: Nat, m: Nat)
    same : SameLen(k, k)
  fn cong({a: Nat}, {b: Nat}, p: SameLen(a, b)) -> SameLen(S(a), S(b)) = match p
    same() -> same()
end
```

(`a`/`b` kept implicit, mirroring `dp01`'s own `{a: Nat}`/`{b: Nat}` — see the transliteration
caveat below) does clear the family declaration, but still does not reach
`check_case_branches`'s `:impossible`/`:undecided` path directly: it fails one layer up, in the
**untrusted elaborator's** own metavariable solver, with `{:unsolved_metavariables, _}` — the
elaborator cannot pin `same()`'s implicit index `k` because it cannot simultaneously satisfy
`k = a` and `k = b` while `a` and `b` remain distinct free variables (verified for both explicit
and implicit `a`/`b`). This *is* the forced-pattern gap the design targets, and it confirms
§4.3's routing work (not only §4.1's kernel change) is necessary: without the kernel producing a
`b ↦ a` forced substitution *and* the elaborator applying it to the branch context before
elaborating the body, the body's own implicit-argument solve can never succeed, regardless of
what `check_case_branches` would eventually do with a fully-elaborated body. §2.1's "no
elaborator dodge" argument is about the **kernel re-check** should an elaborator try to bypass
it with an unverified `Eq`-witness; it is a distinct claim from "the elaborator's own
metavariable solver can make forward progress," which is the actual blocker demonstrated here.
Both are real; the document was previously conflating them.

**Idris transliteration caveat (verified with `idris2 --check`, this review):** a *naive* `.idr`
transliteration of this shape — writing `a`/`b` as two separately-**named**, explicit top-level
clause patterns, e.g. `cong2 a b Same = Same` — is **rejected by Idris2 itself**, independent of
the forced-pattern feature: `Error: ... Pattern variable a unifies with: ?b ... Suggestion: Use
the same name for both pattern variables, since they unify.` This is an Idris LHS-elaboration
quirk about separately-named pattern variables that provably unify, unrelated to what this
probe is meant to test. The **faithful** translation (verified to `--check`-accept) keeps `a`/`b`
implicit — `{a : Nat2} -> {b : Nat2} -> SameLen a b -> ...` with `cong2 Same = Same` — or,
matching Cure's actual `match`-as-nested-`case` structure (following this project's own
established convention, e.g. `test/oracle/match/mt02_nested_arm_dep.idr`'s `case k of`), keeps
`a`/`b` as ordinary explicit parameters and matches only `p` via `case p of Same => Same`. Either
faithful form accepts; only the naive "spell every argument out as a named top-level LHS
pattern" form spuriously rejects. Whoever writes `dp01b`'s (and `dp01`'s, once unblocked) `.idr`
fixture must use one of the faithful forms and must not "fix" a spurious rejection by silently
switching relation to `cure_stricter` — that would misattribute an Idris-side naming quirk to
this design's semantics.

---

## 2. Background — how Cure unifies indices today, and why it fails

### 2.1 The index unifier lives in the KERNEL

When the kernel type-checks a `{:case, scrut, motive, branches}` term
(`lib/cure/core/kernel.ex:208`, `infer/2`), it independently unifies each constructor's
result indices against the scrutinee's indices in `check_case_branches`
(`kernel.ex:703-745`):

```elixir
case unify_indices(ctx, result_indices, scrut_indices, arity) do
  :impossible -> {:cont, :ok}         # branch treated as unreachable; body NOT checked
  verdict ->
    subst = case verdict do {:solved, s} -> s; :trivial -> %{} end
    ctx_branch = specialize_branch_context(extend_with_telescope(...), subst)
    # expected = motive applied at (result_indices ++ [ctor_value])
    ...
end
```

`unify_indices/4` returns `{:solved, subst} | :trivial | :impossible` (`kernel.ex:756`). The
same routine is exposed as `branch_unify/4` (`kernel.ex:770`) and reused by the elaborator
(`lib/cure/elab/elaborator.ex:1219, 1701`). **Both the kernel's own case checker and the
elaborator inherit `unify_indices`' verdict** — so there is no elaborator-only fix: a
carried-`Eq` trick in the elaborator is overridden when the kernel re-checks the `{:case}`
and computes `:impossible` itself. (This is the elaborator-hard-stop conclusion: no untrusted
term dodges the blocked judgement, because the kernel runs that judgement during re-check.)

### 2.2 The specific defect in `unify_one`

`unify_indices` walks the two index vectors pairwise via `unify_one` (`kernel.ex:805-833`).
Constructor-scope variables have de Bruijn index `< arity`; outer (scrutinee) variables have
index `>= arity`:

```elixir
defp unify_one({:var, i}, s, arity, subst) when i < arity, do: bind_index(i, s, subst)
defp unify_one(r, {:var, j}, arity, subst) when j >= arity, do: bind_index(j, r, subst)
defp unify_one(r, s, _arity, _subst) do
  if rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s),
    do: :impossible, else: :undecided
end
```

For `dp01`'s constructor shape, `mrefl`'s `result_indices = [{:var,0}, {:var,0}]` (both the
ctor arg `w`), unified against scrutinee indices `[a, b]` (as shifted `{:var, j}` terms with
`j >= arity`, per `unify_indices`'s pre-shift, kernel.ex:790-794):

1. `unify_one({:var,0}, a)` → `bind_index(0, a, %{})` → key `0` absent → `{:ok, %{0 => a}}`.
2. `unify_one({:var,0}, b)` → `bind_index(0, b, %{0 => a})` → key `0` already `= a`. `bind_index`
   (kernel.ex:846-859) only reports a conflict (`:impossible`) when **both** the existing and
   new value are `rigid_index?` (ctor/data/type-former heads) with different heads
   (kernel.ex:853-854); `{:var, _}` is **not** classified as rigid (kernel.ex:861-870,
   catch-all `false`), so comparing two plain variables `a` and `b` falls through to the final
   `true -> :undecided` clause (kernel.ex:855) — **not** `:impossible`.

Because `reduce_index_pairs` treats `:undecided` as "leave `subst` unchanged and continue"
(kernel.ex:805), the second pair is silently dropped rather than merged or rejected: the
overall verdict is `{:solved, %{0 => a}}` — a **solved-but-incomplete** substitution that
carries the ctor-arg binding but never records the `b := a` equation. `check_case_branches`
therefore does *not* skip the branch as unreachable (that only happens on literal
`:impossible`, kernel.ex:721-722); it proceeds to check the branch body against a goal in
which `b` is still free and un-unified with `a` — which is what actually blocks the program
(see §1.2 for exactly where that surfaces, since `dp01`'s literal source is separately blocked
by the auto-generalization defect before this trace can even run).

The unifier never **resolves** the already-bound ctor var `0` (=`a`) and unifies `a =? b`.
Because `a` and `b` are *scrutinee index variables* — the **flexible/solvable** side of a
case-split, not truly rigid — the correct step is to bind `b := a` (a forced equation) by
recursively re-unifying on the existing-key path, rather than degrading to `:undecided`.

---

## 3. Reference algorithm (Agda `unifyIndices`, Idris2 dot-as-constraint)

Vendored: `reference/agda/.../LHS/Unify.hs` (commit `7273757e5e`), Idris2 `fd405085b`.

- **Agda** runs eager first-class index unification producing a `PatternSubstitution` `sigma`
  and a specialized branch telescope `tel` (`Unify.hs:182-186`, invariant `tel ⊢ sigma :
  varTel`). Forced positions become `DotP`. This is the model to follow — it directly yields
  "context specialized by `b ↦ a`".
- The crux (`Unify.hs:305-372`, `Problem.hs:110-150`): **on a LHS the pattern/index variables
  are the flexible ones.** `x =? t` with `x` flexible ⇒ a **Solution** step (orient +
  substitute). When *both* sides are flexible, `chooseFlex` picks which to eliminate. A
  genuine `NoUnify` (empty branch) only arises from **distinct constructors** (`Conflict`) or
  a **strongly-rigid self-occurrence** (`Cycle`).
- **Idris2** has no substitution object: dot patterns are metavariables + a deferred equality
  constraint (`Core/UnifyState.idr:99`), and impossibility is a *separate* coverage-time
  `clash`/`isEmpty` computation (`Core/Coverage.idr`). We follow **Agda's** substitution model
  because Cure's kernel already threads a `{:solved, subst}` through `specialize_branch_context`.

### 3.1 Minimal sound MGU (reference §4) — what we implement

Three rules over homogeneous index equations:

1. **Solution** — `x =? t` where `x` is a scrutinee index variable and `x ∉ FV(t)` (after
   strengthening): extend the substitution `x ↦ t`, apply it to the remaining equations and
   goal, and mark `x`'s position forced.
2. **Injectivity** — `c ūs =? c v̄s` (same constructor): replace with `ūs =? v̄s` pointwise.
3. **Conflict / Cycle** — `c… =? c'…` (distinct constructors) or `x =? …x…` (strong-rigid
   self-occurrence): this branch is absurd/empty → `:impossible`.

Skip (defer): the higher-dimensional injectivity engine, eta/record/size/literal steps, and
`--without-K` restrictions.

---

## 4. Design by layer

### 4.1 K — forced-equation refinement in `unify_indices` (TCB)

**File:** `lib/cure/core/kernel.ex` (`unify_indices/4`, `unify_one/4`, `bind_index/3`).

Introduce **resolve-before-bind** and the **Solution orientation** for scrutinee variables.
`bind_index(i, s, subst)` currently (kernel.ex:846-859), when `subst[i] = v` already and
`v != s`: reports `:impossible` **only** if both `v` and `s` are `rigid_index?` with different
heads (kernel.ex:853-854); otherwise — including the dp01-relevant case of two distinct plain
variables — it degrades to `:undecided` and the equation is silently dropped rather than
merged or rejected (§2.2). Change it so that, when `subst[i] = v` already:

- unify `v =? s` recursively (`unify_one`), threading the growing `subst`;
- if that yields a **scrutinee-variable = term** equation (`{:var,j}` with `j >= arity` on
  either side), record the **forced substitution** for that scrutinee variable
  (`j ↦ other`), subject to the **occurs guard** (`j ∉ FV(other)`);
- Injectivity for equal-constructor terms; distinct constructors / occurs-cycle → `:impossible`.

The verdict grows from `{:solved, subst}` where `subst` currently only carries **ctor-arg →
term** entries to *also* carry **scrutinee-var → term** (forced) entries. The elaborator and
kernel already apply `subst` to the branch context/goal via `specialize_branch_context(_subst)`
(`kernel.ex:731-732`, `elaborator.ex:1287-1300`) — those consumers must accept forced
scrutinee-var keys (see §4.3).

**Soundness obligations (TCB gate).** A new Antigen antibody must witness that the refined
`unify_indices`:
- **terminates.** Two distinct recursions need distinct measures, and the plan must state both:
  (a) `reduce_index_pairs`'s existing outer recursion over the equation list, well-founded
  because each step consumes one pair (unchanged by this design); (b) the **new**
  resolve-before-bind chase *inside* `bind_index` itself, which does not consume an equation
  pair — it recurses on `unify_one(v, s, …)` where `v` is whatever the existing key was already
  bound to, and if `v` is itself a variable with its own existing binding, the chase continues.
  This must be shown to terminate independent of (a) — e.g. bounded by `map_size(subst)`,
  because each chase step must resolve to either a fresh (unbound) key or a rigid head, never
  revisiting an already-visited key. The Antigen antibody must specifically construct **chained**
  bindings (a chase of depth > 1, i.e. a scrutinee var forced through two or more intermediate
  already-bound keys in one branch) to exercise measure (b), not only single-step cases;
- **introduces no binding cycle across distinct keys.** The existing per-key `occurs_index?`
  guard (kernel.ex:848, 877-883) only rejects a key occurring in its *own* proposed value; it
  does not, by itself, rule out two *different* keys ending up mutually bound through separate
  equations in the same `unify_indices` call (e.g. `i ↦ {:var, j}` from one pair and, if the
  resolve-before-bind chase ever proposes rebinding `j`, `j ↦ {:var, i}` from another). The plan
  must state why this cannot arise given Cure's ctor-signature shape (result-index terms are
  always written over the *ctor's own* telescope, so only chase-derived rebinds ever touch an
  outer/scrutinee key) or add an explicit multi-key occurs/cycle check if it can;
- **collapses no distinct normal forms** — a forced `b := a` is only recorded when the
  indices are *provably* equal under the match (both are the same ctor-scope variable's image),
  never equating two independent values;
- preserves the existing `:impossible`/`:trivial`/`{:solved,_}` contract for all currently
  passing cases (no regression in the frozen oracle clusters or the kernel property suite).

This aligns Cure's `unify_indices` with Agda's `unifyIndices` Solution step, so per the
standing TCB policy it is pre-approved *conditional on passing the full gate*.

### 4.2 P — explicit `.e` dot-pattern syntax

**Correction (this review):** there is no `parse_pattern` function, and no separate
"pattern position" in the grammar. Every pattern-consuming call site — `parse_match_arm`
(parser.ex:1623, via `parse_expr(state, 0)`) and `parse_clause_patterns`
(parser.ex:2076-2098, via `parse_expr(state, 42)`) — parses a pattern by calling the **general
expression parser** (`parse_expr`/`parse_prefix`, parser.ex:167-338) and treating whatever
expression AST comes back as a pattern (constructor applications, variables, literals). There
is no dedicated pattern grammar to hook a "pattern-position-only" rule into.

**File:** `lib/cure/compiler/parser.ex` — add a new `parse_prefix` case for a leading `:dot`
token (the `case token.type do … end` at parser.ex:203-338 currently has **no** `:dot` clause,
so a leading `.` at the start of *any* expression is unclaimed today: it falls through to the
catch-all `{:unexpected_token, …}` error, parser.ex:333-336). Concretely:

- Surface: `.x` (simple), `.(expr)` (compound / unambiguous form). The parenthesised form is
  primary and always accepted; bare `.name` / `.<literal>` are the sugar.
- AST: a new pattern node `{:forced_pattern, meta, expr_ast}` (name TBD-in-plan but fixed once
  chosen), where `expr_ast` is an ordinary expression AST parsed in pattern-expression mode.
- **Disambiguation is not a "pattern vs. expression position" split — it can't be, since both
  share `parse_expr`.** Adding a `:dot` case to `parse_prefix` makes `.expr` parseable
  *everywhere* `parse_expr` is called, not just where a pattern is expected. The existing
  dotted-module-name syntax (`Std.String`) is unaffected regardless, because that `.` is
  **infix** (lexed as `:dot` following an already-parsed `left`, handled by the `:dot ->` clause
  in `parse_infix`'s `handle_infix_op`, parser.ex:476-482, producing `{:attribute_access, …}`),
  not a leading/prefix `.`; a leading `.` and an infix `.` are different grammar positions and
  don't collide. The real restriction the plan must add is **semantic, not syntactic**: reject
  a `{:forced_pattern, …}` node wherever the parsed AST is consumed as an ordinary expression
  (not a pattern) — e.g.
  in whatever validates/lowers a `match`-arm or clause-pattern AST today. The plan must name
  that validation site explicitly (it does not yet exist for this purpose) and include a
  negative test that a bare `.x` used as an expression (not a pattern) is rejected there, plus
  a positive test that `Std.String`-style dotted names still parse unaffected in every context
  that uses them.

### 4.3 E — elaborate dot patterns + accept forced scrutinee-var substitutions

**File:** `lib/cure/elab/elaborator.ex` (branch elaboration, `specialize_branch_context_subst`,
constructor-arm elaboration), possibly `lib/cure/elab/*` pattern lowering.

Two responsibilities:

1. **Consume forced scrutinee-var subst (from §4.1).** `specialize_branch_context_subst/2`
   (`elaborator.ex:1287`) and the branch-goal refinement must apply forced scrutinee-variable
   entries, not only ctor-arg entries. Because the elaborator's `branch_unify` call
   (`elaborator.ex:1219,1701`) is the *same* `unify_indices`, the forced entries appear
   automatically once §4.1 lands; the elaborator work is to **route them into the branch
   context + goal** so the arm body checks against the refined goal. This step is not optional
   polish: per §1.2's `SameLen`/`same()` probe, a branch body that is itself a constructor
   application needing an implicit index solved (e.g. `mrefl()`, `same()`) fails at
   **elaboration time** with `{:unsolved_metavariables, _}` — the untrusted solver cannot
   satisfy `k = a` and `k = b` while `a`/`b` are still distinct — before the kernel's own
   `check_case_branches` re-check would even get a chance to run. Only routing the forced
   `b ↦ a` substitution into the branch context *before* elaborating the body collapses `a`/`b`
   to one variable and lets that solve succeed; without this, §4.1 alone (kernel-only) does not
   flip `dp01`-shaped probes whose branch body forces an implicit index.
2. **Elaborate `{:forced_pattern, _, expr}`.** When a constructor argument position carries a
   dot pattern, elaborate `expr` to a Core term and **assert it is convertible** to the value
   that index unification determined for that position. Agreement ⇒ accept; disagreement ⇒
   reject (`{:forced_pattern_mismatch, written, determined}`). A forced position binds no new
   pattern variable. The forced Core term is recorded so §4.4 can erase it.

### 4.4 E (pattern-erasure pass) — forced-argument erasure, *not* codegen

**Correction (this review):** an earlier draft of this section put this work in
`lib/cure/compiler/codegen.ex` and described it as reusing the ctor's static
`quantities :: [:erased | :present]` field (`lib/cure/core/inductive.ex:110-116`) directly.
Both claims don't survive contact with the existing pipeline:

- **Erasure already happens inside the elaborator, before codegen runs.** `Cure.Elab.Erase`
  (`lib/cure/elab/erase.ex`) already drops `:erased`-quantity arguments from `{:ctor, cname,
  args}` **construction** terms (`erase.ex:20-30`), and is invoked from `Cure.Elab.Emit`
  (`lib/cure/elab/emit.ex:95,110`) — i.e. entirely inside the E-layer pipeline stage that runs
  *before* `lib/cure/compiler/codegen.ex` ever sees the term. By the time `compile_pattern_match`
  (codegen.ex:1433) runs, the term has already been through `Erase.erase`; codegen no longer
  necessarily has the dependent/index context (`Inductive` family/ctor records) available in
  the same form. This is the P+E+C **codegen-vs-elaborator conflation** this review was asked
  to check for (task risk area 5) — it was real. The natural home for forced-pattern erasure is
  the **same E-layer pass**, alongside `Erase.erase`'s existing `{:ctor,…}` handling — most
  directly by extending its `{:case, s, m, branches}` clause (`erase.ex:75-77`), which today
  recurses into branch bodies but leaves each branch's arity/bindings untouched.
- **`quantities` is the wrong data to overload.** It is a static property of the constructor's
  *declaration*, fixed across every construction site of that constructor (confirmed by
  `Erase.erase`'s own use: one `quantities` list per `cname`, applied uniformly regardless of
  call site). Forced-ness is a property of a **specific pattern-match site**: the same
  constructor argument can be forced in one `match` (because that branch's index equation pins
  it) and genuinely free in another. Writing forced positions into the ctor's shared
  `quantities` would erase the argument at *every* use of that constructor, including sites
  where it is not determined — unsound. Forced positions need their own **per-branch** signal
  (exactly what §4.3's `{:forced_pattern,…}` marks / the unification-derived forced set already
  are) threaded alongside the branch, not folded into `quantities`.

Revised design:

- **File:** `lib/cure/elab/erase.ex` (extend `erase/2`'s `{:case,…}` clause), consuming the
  same `{:forced_pattern,…}` marks / forced-position set produced by §4.3, threaded through the
  `{cname, arity, body}` branch triple (or an accompanying per-branch structure — the
  implementation plan must pin the exact shape, since `erase/2`'s branch triple has no room for
  it today and needs a field added or a side-table keyed by `{cname, branch}`).
- A constructor argument whose value is **determined by index unification** (a forced position,
  specific to this match branch) is recoverable at runtime and need not be scrutinised or
  bound. At erasure time:
  - compute the **forced positions** for each constructor pattern (from the same unification /
    the `{:forced_pattern,…}` marks from §4.3);
  - lower those positions to a wildcard (no binding, no match test) so the runtime pattern does
    not depend on the forced argument — this changes what codegen (`compile_pattern_match`)
    receives, so no change to `codegen.ex` itself should be needed if `Erase.erase` runs to
    completion first, as it already does today.

Per reference §5 this is a **separable optimisation** keyed off the forced marks; it changes
runtime shape but not typing. It is **not oracle-measurable** (the oracle only sees
`--check`), so it gets its own codegen/run test (§5.2). Erasure must be **conservative**: if a
position's forcedness is not established, keep it present (never erase a genuinely-matched arg).

---

## 5. Test plan

### 5.1 Oracle probes (type-level: K + P + E) — cluster `dotpat`

Each is a faithful `.cure`/`.idr` pair; `.idr` carries `%default total`, no module line.

| Probe | Program | Expected (post-fix) | Status |
|---|---|---|---|
| `dp01_forced_eq` | `mrefl : MyEq(w,w)` matched vs `MyEq(a,b)`, body needs `a=b` (the base gap) | accept / accept | **blocked** — see caveat below |
| `dp01b_forced_eq_min` | `same : SameLen(k,k)` (no `Type` param) matched vs `SameLen(a,b)`, body needs `a=b` — §1.2's minimal, non-confounded analogue of `dp01` | accept / accept | reach flip (verified pre-fix: rejects today with `{:unsolved_metavariables, :same}`) |
| `dp02_explicit_dot` | same as `dp01`, written with an explicit `.a` dot pattern for the forced index | accept / accept | **blocked** — same caveat |
| `dp03_vect_head` | `vhead : Vec(S(n)) -> a` matching `vcons` (length index forces `S n`) | accept / accept | reach flip, not `Type`-param-indexed, unaffected by the caveat |
| `dp04_absurd_distinct` | a match whose indices force **distinct constructors** ⇒ impossible/absurd branch (empty), Idris accepts via impossibility | accept / accept | **regression guard, already passing today** — verified: a `Vec`-style example with a `vnil()`-branch whose result index clashes with a concrete `S(_)` scrutinee index already elaborates successfully via the pre-existing Conflict/`rigid_index?` clauses (kernel.ex:817-833), independent of this design |
| `dp05_occurs_cycle_neg` | a forced equation `x := …x…` (strong-rigid self-occurrence) | reject / reject | **needs a concrete `.cure` construction** — not yet demonstrated to be expressible against Cure's current inductive-family model; pin one during implementation, mirroring `dp01b` |
| `dp06_dot_mismatch_neg` | explicit dot `.c` written where unification determined a **different** value | reject / reject | depends on §4.2 (`.e` syntax), not yet implemented; construct once P lands |

**Caveat on `dp01`/`dp02` (both use the `Type`-parametrized `MyEq(a: Type) indices (x: a, y:
a)` shape):** per §1.2, this shape independently fails **before** reaching case-branch
checking, due to the auto-generalization defect. `dp01`/`dp02` cannot be used to validate this
design until that defect is fixed (tracked separately). `dp01b` is the interim primary reach
probe — same essential shape (a single constructor forcing two outer index variables equal),
built on a concrete (non-`Type`-parametrized) family so it isn't blocked by the same defect. Once the
auto-generalization defect is fixed, `dp01`/`dp02` should be re-verified and, if they then
behave as originally intended, kept as the `Type`-polymorphic-family variant of the same reach
flip (not a duplicate — polymorphic vs. monomorphic families exercise different code paths in
`check_ctor`/`check_result_indices`).

`dp01b` and `dp03` are the (non-blocked) reach flips; `dp04` is a same-cluster regression guard
that already passes without this design's changes; `dp05`/`dp06` are the soundness guards (must
stay `reject`) and need concrete programs pinned during implementation. Frozen in
`test/oracle/dotpat/verdicts.json`, replayed by `test/oracle_replay_test.exs`. **No pre-existing
cluster may regress.**

### 5.2 Non-oracle tests

- **Kernel unit tests** for `unify_indices`: Solution (forced `b:=a`), Injectivity, Conflict,
  occurs-cycle rejection, and the existing ctor-arg cases (regression).
- **Antigen antibody** for the refined unifier (termination + no normal-form collapse) — the
  TCB gate; plus the full Antigen suite.
- **Parser unit tests** for `.e` / `.(expr)`, the module-path (`Std.String`) non-regression, and
  (per §4.2's correction) a negative test that a bare `.x` used in an ordinary expression
  position — not a pattern — is rejected by the semantic check, not silently accepted because
  `parse_prefix` is shared between patterns and expressions.
- **Erasure test (E, `Cure.Elab.Erase`):** compile a program with a forced constructor argument
  and assert the erased Core term (post-`Erase.erase`, pre-codegen) does not bind/scrutinise
  the forced position, and/or a `run-on-unix` execution that observes correct behaviour with
  the arg erased end-to-end through codegen.

---

## 6. Scope boundaries / non-goals

- **In:** Solution + Injectivity + Conflict/Cycle MGU (homogeneous indices); explicit `.e`
  dot syntax; forced-arg erasure keyed off forced marks.
- **Out (deferred):** higher-dimensional injectivity engine; eta/record/size/literal unify
  steps; `--without-K` cycle restrictions; heterogeneous equation stacks. If a probe needs one,
  reach-pin it (an Antigen must-eventually-accept), do not silently widen scope.
- **Out (separate ticket, blocking `dp01`/`dp02` only):** the auto-generalization defect (§1.2)
  — `check_ctor`/`check_result_indices` rejecting a `Type`-parametrized family whose
  constructor repeats a free index variable across ≥2 index positions. Not a forced-pattern
  concern; do not fold its fix into this design's K-layer change.
- Erasure is conservative and optional to correctness — a forced arg left present is sound.

## 7. Risks

1. **TCB soundness.** The kernel unifier is soundness-critical. Mitigated by the Antigen
   antibody (termination + no normal-form collapse) and the full gate; the change mirrors
   Agda's documented Solution step.
2. **`subst` key overlap.** Forced scrutinee-var keys (`j >= arity`) share the substitution map
   with ctor-arg keys (`i < arity`). This is disjoint **by construction today**, not something
   requiring new bookkeeping: both `unify_one` binding clauses (kernel.ex:811-815) are guarded
   by `i < arity` / `j >= arity` on the single shared "branch de Bruijn frame" (`ctor-args ++
   outer`, per `branch_unify`'s own doc comment, kernel.ex:756-757), and the generic consumers
   (`replace_branch_vars`, kernel.ex:911 / elaborator.ex's mirror) key on `{:var, i}` uniformly
   regardless of which range `i` falls in — no per-consumer special-casing exists or is needed.
   The actual risk is **regression**: a future edit to `unify_one`/`bind_index` could
   accidentally violate the `i < arity` / `j >= arity` partition (e.g. by shifting one side and
   not the other) and silently conflate a ctor-arg and a forced scrutinee-var under the same
   key. Mitigation: a red test asserting a branch with *both* a ctor-arg refinement and a forced
   scrutinee-var refinement resolves both correctly guards this regression, not an
   initial-disjointness bug.
3. **Parser scope leak.** Patterns and expressions share one grammar (`parse_expr`, no separate
   `parse_pattern` — §4.2 correction), so a `:dot`-prefix case added to `parse_prefix` makes
   `.expr` parseable in *every* expression context, not only where a pattern is expected;
   module-path dotting (`Std.String`) is a different, infix grammar position and does not
   collide, but a stray `.x` used as an ordinary expression would parse successfully unless
   separately rejected. Mitigated by a semantic (post-parse) check rejecting `{:forced_pattern,
   …}` outside pattern-consuming positions, plus the negative/positive tests named in §4.2.
4. **Erasure over-eagerness.** Erasing a genuinely-matched argument is a runtime bug.
   Mitigated by conservative forcedness (erase only positions unification determined) and the
   `Cure.Elab.Erase` erasure test (§5.2).
5. **Blocking dependency: the auto-generalization defect (§1.2).** The primary illustrative
   probe (`dp01`, `Type`-parametrized `MyEq`) is rejected today for a reason unrelated to this
   design — a pre-existing bug in `check_ctor`/`check_result_indices` for `Type`-parametrized
   families whose constructor repeats a free index variable across ≥2 index positions. Left
   unacknowledged, work could be scoped, tested, and reported "done" against `dp01b`
   (unblocked) while `dp01`/`dp02` (the more general, polymorphic-family case the roadmap
   presumably cares about) remain silently broken for an unrelated reason. Mitigation: track
   the auto-generalization defect as a separate ticket, keep `dp01`/`dp02` in the oracle cluster
   marked `blocked` rather than deleting them, and re-verify them (not just `dp01b`) once that
   defect is fixed, before declaring this design's `Type`-polymorphic-family coverage complete.
