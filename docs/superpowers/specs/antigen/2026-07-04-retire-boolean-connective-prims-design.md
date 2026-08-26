# Retire the Boolean Connective Primitives — Design

**Date:** 2026-07-04 · **Status:** proposed (for the TCB agent) · **Target tree:** `autopilot/lean-shape-matching`

> Authored from the `antigen-tier-b` worktree while building coverage-guided
> generators; the Antigen work surfaced that `Eval.fold`/`Kernel.infer_prim`
> still carry Boolean-connective clauses even though `Bool` is now inductive.
> This spec hands the kernel side to the TCB agent. **No Antigen changes are
> required by this spec** (the Antigen v1 menu already seeds `Bool`); §8 records
> the one downstream effect.

## 1. Goal

Move the Boolean **connectives** `and`, `or`, `not` (and Boolean-operand
`eq`/`ne`) out of the trusted kernel primitive machinery and define them as
ordinary certified Cure functions that `case`-eliminate the inductive `Bool`
(`False | True`). Preserve native BEAM performance by lowering their applications
to the same BEAM operators at code-gen. **Do not** touch the numeric comparison
or arithmetic primitives — those must stay primitive (§4.2).

Net effect: a smaller TCB, definitional computation of the connectives on open
terms, and closer alignment with how Agda/Lean define `_∧_`/`_∨_`/`not`.

## 2. Motivation

Two independent wins, plus an alignment argument that satisfies the standing
TCB-change approval bar (kernel changes are pre-approved **iff** they align Cure
with Agda/Lean).

1. **Smaller TCB.** Each connective is trusted kernel code in two places today —
   a clause in `Eval.fold` and a clause in `Kernel.infer_prim`, plus the
   `as_bool/1` plumbing. As prelude definitions they become ordinary code the
   kernel *checks* (via the already-trusted `case`/eliminator machinery), rather
   than code the kernel *is*. This deletes trusted surface rather than relocating
   it: the eliminator path already has to exist for every inductive.

2. **Definitional computation on open terms — the substantive win.** A primitive
   `and` fires only when **both** operands reduce to concrete `True`/`False`
   constructor values (`fold`'s `as_bool/1` demands it); an open term like
   `and(x, True)` with `x` a variable stays a **stuck neutral**
   (`{:vneutral, {:nprim, :and, …}}`) and never unfolds. The `case`-defined
   `and(x, b)` instead reduces by splitting on `x`, so
   `and(True, b) ≡ b` and `not(not b) ≡ b` hold **definitionally** (provable by
   `refl`) and the connectives compose with `case`/induction inside proofs and
   types. This is the behaviour a dependent kernel wants the moment Boolean
   operators appear in a type or proposition.

3. **Agda/Lean alignment.** Both define the connectives as ordinary
   pattern-matching functions on the `Bool` datatype, *not* as kernel
   primitives. This change makes Cure match them, and is continuous with the
   in-flight builtin-inductive-foundation work (Bool-as-inductive, `bool_elim`
   retirement).

## 3. Current state (anchors — `lean-shape-matching` worktree)

- `lib/cure/core/eval.ex`
  - `fold(:and, …)` line 143; `fold(:or, …)` 147; `fold(:not, …)` 151 —
    connective folds via `as_bool/1`.
  - `fold(:eq, [a, b])` 158; `fold(:ne, [a, b])` 162 — the **Boolean-operand**
    equality folds (must stay *after* the numeric `:eq`/`:ne` clauses; they use
    `as_bool/1`).
  - `vbool/1` 168–169 — maps an Elixir bool to a `True`/`False` **ctor value**.
  - `as_bool/1` 171–173 — maps a `True`/`False` ctor value back to an Elixir
    bool; `_other -> :stuck`.
- `lib/cure/core/kernel.ex`
  - `infer_prim(ctx, op, [a, b]) when op in [:and, :or]` line 1056 — types both
    operands at `bool_type_value`, result `Bool`.
  - `infer_prim(ctx, :not, [a])` line 1066 — types operand at `Bool`, result
    `Bool`.
  - `bool_type_value/1` — resolves the `:bool` builtin family (stays; comparisons
    still use it).
- `lib/cure/elab/emit.ex`
  - `lower(env, {:prim, op, [a, b]}, ctx) when op in […, :and, :or]` line 161 →
    `{:op, @line, erl_binop(op), …}`.
  - `lower(env, {:prim, op, [a]}, ctx) when op in [:not, :neg]` line 165.
  - `erl_binop(:and) → :and`, `erl_binop(:or) → :or` (≈239); `erl_unop(:not) →
    :not` (242). **Note:** current lowering uses the *strict* BEAM boolean ops
    (`:and`/`:or`), which evaluate both operands.
- `lib/cure/elab/elaborator.ex` line 362 — surface binary operators lower to
  `{:prim, op, [l_core, r_core]}`. (`emit.ex` is the value/codegen path; confirm
  which of the two is authoritative for the runtime lowering during planning.)
- `lib/cure/core/builtins.ex` — `seed/2` (line 54) declares the canonical `Bool`
  (`False | True`) and registers the `:bool` builtin; `@builtin` machinery
  (validated ctor name+arity) is how a prelude module claims a builtin key.

## 4. Design

### 4.1 What moves to the prelude (retire the prims)

Define, in the prelude/stdlib over the inductive `Bool`:

```
not(a : Bool) : Bool = case a of True -> False | False -> True
and(a : Bool, b : Bool) : Bool = case a of True -> b     | False -> False
or (a : Bool, b : Bool) : Bool = case a of True -> True  | False -> b
```

Boolean-operand equality (currently `fold(:eq/:ne, [a,b])` via `as_bool`):

```
booleq(a : Bool, b : Bool) : Bool = case a of True -> b       | False -> not(b)
boolne(a : Bool, b : Bool) : Bool = case a of True -> not(b)  | False -> b
```

All five are total, non-recursive, and pass the existing certifier. `case a of
True -> b | False -> False` is short-circuiting on `a` (b forced only in the
`True` branch), matching `orelse`/`andalso` semantics.

### 4.2 What stays primitive (do NOT touch)

- **Arithmetic** `add/sub/mul/div/rem/neg` (Int/Float): irreducible.
- **Numeric comparisons** `lt/le/gt/ge` and **numeric** `eq/ne` on Int/Float:
  these consume opaque native BEAM `Int`/`Float`, which have **no constructors
  to `case` on**. They cannot be eliminator-defined. They remain in `fold`
  (numeric clauses, lines 124–138) and `infer_prim`, and they still **return**
  the inductive `Bool` via `vbool/1` + `bool_type_value/1`. Therefore `vbool/1`
  and `bool_type_value/1` **stay**; only `as_bool/1` and the connective/Bool-eq
  clauses are deleted.

### 4.3 Kernel deletions

- `eval.ex`: delete `fold(:and)` 143, `fold(:or)` 147, `fold(:not)` 151, the
  Boolean-operand `fold(:eq, [a,b])` 158 and `fold(:ne, [a,b])` 162, and
  `as_bool/1` 171–173. Keep `vbool/1`. Verify the numeric `:eq`/`:ne` clauses
  (comparison, lines ~124–127) are unaffected — with the `[a,b]` Boolean
  clauses gone, an unmatched `:and`/`:or`/`:not`/Bool-`:eq` now correctly falls
  through to `fold(_op,_args) -> :stuck` (which is what should happen if a raw
  connective prim ever survives — it should be an *ill-formed* term post-change;
  see §7 open question on hard-error vs stuck).
- `kernel.ex`: delete `infer_prim … [:and, :or]` 1056 and `infer_prim :not`
  1066. After deletion a residual connective prim hits
  `infer_prim(_ctx, op, _args) -> {:error, {:unknown_prim, op}}` — the desired
  rejection.

### 4.4 Elaborator / code-gen

Surface `&&`, `||`, `!`, and Bool-typed `==`/`!=` must now elaborate to
**applications of the prelude defs**, not `{:prim, …}` nodes:

- Update the surface-operator lowering (elaborator.ex:362 and/or the value path)
  so `&&/||/!` produce `{:app, {:global, :and/:or/:not}, …}` (or the prelude's
  qualified names) instead of `{:prim, :and/:or/:not, …}`.
- **`==`/`!=` are operand-type-directed** (this is the trickiest part): the
  surface `==` is polymorphic over Int/Float/Bool. Numeric operands must keep
  lowering to the `:eq`/`:ne` **prim** (native compare); **Bool** operands must
  lower to `booleq`/`boolne`. The elaborator already knows the operand type at
  this point — dispatch on it. Do not collapse both into one path.

Preserve native BEAM performance: `@builtin`-tag (or name-recognize) the five
prelude defs so `emit.ex` lowers a *saturated application* of them to the native
BEAM op (`erl_binop`/`erl_unop`), exactly as it lowers the prim today. Decision
for the plan: emit strict `:and`/`:or` (byte-for-byte the current behaviour) or
switch to short-circuit `:andalso`/`:orelse` (faithful to the `case`-def
semantics, a small refinement). Recommend `:andalso`/`:orelse`; call it out
explicitly since it is an observable evaluation-order change.

## 5. Non-goals

- No change to arithmetic or numeric-comparison prims.
- No removal of `vbool/1`, `bool_type_value/1`, or the `:bool` builtin.
- No change to the `Bool` datatype itself (already `False | True`).
- No Antigen/tooling changes (see §8).

## 6. Verification

1. **Certifier:** the five prelude defs certify (total, well-typed).
2. **Definitional equalities (new, must hold by `refl`):** `not True ≡ False`,
   `not False ≡ True`, `and True b ≡ b`, `and False b ≡ False`,
   `or True b ≡ True`, `or False b ≡ b` for a *variable* `b`
   (the open-term win — impossible with the old prims).
   **Correction (verified 2026-07-04, `1b5e510`):** `not (not b) ≡ b` is NOT
   definitional — for a neutral `b` it reduces to a stuck `case`-of-`case` and is
   only *propositionally* equal, exactly as in Agda/Lean. Only the four one-step
   equations above are definitional wins. `test/cure/core/bool_connective_defeq_test.exs`
   asserts the four and `refute`s the double-negation (and `refute`s all four
   without the defs, proving the equality comes from δ-unfolding, not vacuity).
3. **Native-op lowering fidelity:** compiled `and/or/not` still emit a BEAM
   boolean op; add a codegen/round-trip test. If switching to
   `:andalso`/`:orelse`, assert the short-circuit evaluation order.
4. **Regression:** full kernel + conformance suite green. Existing programs using
   `&&/||/!/==` recompile and evaluate identically (modulo the intended
   short-circuit refinement).
5. **Rejection:** a hand-built residual `{:prim, :and, …}` term is rejected by
   `infer` (`{:unknown_prim, :and}`) — confirms the prim path is gone.

## 7. Risks & open questions

- **`==`/`!=` type-directed split** (§4.4) is the highest-risk piece — a
  mis-dispatch would send Bool `==` to the numeric prim or vice-versa. Needs
  explicit operand-type tests (Int==, Float==, Bool==, and a mixed/ill-typed
  rejection).
- **Stuck vs hard-error for a residual connective prim.** After deletion, a
  surviving `{:prim, :and, …}` is `:stuck` in `eval` but `{:unknown_prim}` in
  `infer`. Decide whether `eval` should also hard-signal (defensive) or stay
  stuck (a well-typed term can never contain one, so stuck is unreachable in
  practice). Prefer: leave `eval` stuck, rely on `infer` rejection.
- **Prelude bootstrap / load order.** The defs depend on `Bool` being seeded
  before they certify. Confirm the prelude declares/obtains `Bool` (via
  `@builtin(:bool)`) ahead of the connective defs.
- **Short-circuit change** is observable if any program relied on both operands
  of `&&`/`||` being evaluated for effects — but Cure is pure, so this should be
  benign. Note it in the changelog regardless.
- **Erasure / quantities:** ensure the connective defs carry the expected
  quantity vectors (both args computationally relevant) so erasure is a no-op on
  them.

## 8. Downstream effect on Antigen (informational — no action here)

The `antigen-tier-b` worktree recently added a structure-directed primitive
generator that, among other things, drives `Eval.fold`'s connective clauses
(`:and/:or/:not`, Bool-operand `:eq/:ne`) and `as_bool/1` for coverage. Once
those clauses are deleted, that slice of coverage becomes moot; the **numeric**
prim coverage (arithmetic + comparisons) stays valid. The Antigen v1 menu
already seeds `Bool` (matching `Builtins.seed`), so nothing in Antigen needs to
change for this spec — the Antigen generator will simply need its Bool-operand
cases retargeted to the new prelude defs *if and when* coverage of those defs is
desired. Coordinate timing so Antigen doesn't bank coverage into code this change
removes.
