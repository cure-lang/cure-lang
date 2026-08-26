# The minimal primitive eliminator: a dependent `Bool` eliminator (TCB)

**Status:** implemented on `autopilot/lean-shape-matching`, gated, **not merged**
(operator reviews all TCB diffs at merge). Approved as TCB item #1 of the
primitive-value-eliminator menu.

## Problem

Cure's Core has exactly one eliminator — `{:case, scrut, motive, branches}` over
an inductive `:vdata` scrutinee. There is no way to branch on a *primitive*
value, so `when` guards, `if`, integer/atom/float **literal patterns**, and
`match` on `Bool`/`Int` are all unrepresentable. This is the single
highest-leverage parity gap (roadmap rows #4 literals + guards).

## Key realization — the change is tiny

`{:prim, op, args}` already exists and the kernel already:

- **types** `:eq/:ne/:lt/:le/:gt/:ge/:and/:or/:not` at `Bool`
  (`kernel.ex` `infer_prim`), and
- **evaluates** them to `{:vbool, true|false}` or leaves them stuck neutral
  (`eval.ex` `fold`).

So the *only* missing kernel primitive is a way to **branch on a `Bool`**.
Everything else — comparing integers/atoms/floats, chaining literal tests,
desugaring guards and `if` — is expressible in the **untrusted elaborator** as
`{:prim}` comparisons feeding that one eliminator. The TCB delta is one node.

## The construct

`{:bool_elim, scrut, motive, tt, ff}` — Lean's `Bool.rec`:

- `scrut : Bool`
- `motive : Bool → Type` (a `{:lam, {:bool_type}, _}` in practice)
- `tt : motive @ true`, `ff : motive @ false` — **both mandatory**, each binds
  nothing
- result type: `motive @ scrut`
- ι-rule: `bool_elim true  m tt ff ⟶ tt`, `bool_elim false m tt ff ⟶ ff`

**Total by construction.** Exactly two branches, both required, so there is no
coverage rule, no default, and no literal-matching *in the kernel*. Subject
reduction is immediate: reduction fires only when `scrut` whnfs to a concrete
boolean `b`, at which point `scrut ≡ b`, so `motive @ scrut ≡ motive @ b` — the
type of the taken branch.

## Reference grounding (Lean 4, per `reference/MANIFEST.md` §B)

Lean's kernel carries `Lit` as a first-class `expr_kind` (`src/kernel/expr.h`)
and special-cases primitive reduction (`reduceNat` in `type_checker.cpp`). Its
recursors (`Bool.rec`, `Nat.rec`) are the trusted large-elimination primitives.
We mirror the **trust split** (a total, mandatory-branch recursor in the TCB),
not the surface. We deliberately take only `Bool.rec`: the infinite primitive
types (Int/Atom/Float) never enter the kernel as matchable literals — they are
compared via `{:prim}` (already trusted, already decidable) and the *result*
(a `Bool`) is what the kernel eliminates.

## Files (all additive)

| Layer | File | Change |
|---|---|---|
| K | `term.ex` | node in `term?`/`shift`/`subst`/`to_external`/`from_external`; also completed serialization of the pre-existing literal/`prim` nodes |
| K | `value.ex` | `neutral?({:nbool_elim,…})` |
| K | `eval.ex` | ι-reduction + `:nbool_elim` freeze |
| K | `quote.ex` | reify `:nbool_elim` |
| K | `conv.ex` | `conv_neutral?` for `:nbool_elim` (scrutinee up to conversion, motive + branches via `conv_closure?`) |
| K | `normalise.ex` | `nf_neutral` + whnf `unfold_certified_head` ι-rule |
| K | `kernel.ex` | `infer` clause + `check_bool_motive_wf` (motive must be `Bool → Type`) |
| K | `certificate.ex` | **SOUNDNESS**: `calls?`/`guarded_node?` clauses — a self-call hidden in a branch must be visible to the termination checker |
| A | `generators/totality.ex` | two banked antibodies (`diverging_bool_elim_branch`, `terminating_bool_elim_branch`) |

## The one genuine soundness risk (closed)

`certificate.ex`'s `calls?/2` and `guarded_node?/5` both have catch-alls
(`false` / `true`). Without explicit `:bool_elim` clauses, a recursive self-call
hidden in a branch would be **invisible** to the termination checker →
`terminating?` would report `true` → a non-total def would be **certified total**
(δ-unfolding it can loop the normalizer). The added clauses descend into both
branches carrying the current `root`/`smaller` (the node binds nothing, so no
shift). Banked as `diverging_bool_elim_branch` (must stay rejected forever) with
`terminating_bool_elim_branch` guarding against over-correction.

## Gate

Red-green (`test/cure/core/bool_elim_test.exs`, 20 cases incl. the totality
antibody, a dependent-motive large elimination, and the conversion-faithfulness
regression below) · core suite 188 · two new Antigen antibodies · full Antigen
182 · full suite 2533, zero regressions · independent adversarial verification.
**Not merged.**

### A soundness hole the gate caught (conversion faithfulness)

The first adversarial pass **found a real hole** in the initial `conv.ex`
`:nbool_elim` clause: it compared the `tt`/`ff` branch bodies with
`conv_closure?`, which prepends one fresh binder. That is correct for the motive
(a genuine 1-binder λ) but wrong for `tt`/`ff`, which bind nothing — the prepend
drops env index 0, masking a captured variable to the fresh var on *both* sides,
so two distinct branch values compared equal. It propagated into `Kernel.check`
(a `T(Int)` term accepted at type `T(Bool)` for a Bool-indexed family
`T(x) = bool_elim(b, λ_.Type, x, Bool)` — an `Int ↔ Bool` coercion).

**Fix:** compare `tt`/`ff` with the arity-0 nullary path `:ncase` already uses
(`conv_branch_bodies?(0, …)`), which prepends nothing and compares at `depth`.
The `:case` eliminator was always correct here because its nullary branches go
through that same path; the bug was an asymmetry unique to the new clause.
Captured as a red-green regression test (`T(Int)` ≢ `T(Bool)`, and the kernel
rejects the coercion). Re-verified by a second adversarial pass.

**Lesson:** a "symmetric prepend on both sides preserves equality" argument is
*false* when the prepend can mask a differing value to the same fresh var —
symmetry hides the difference rather than preserving it.

## Follow-ups (untrusted, separate increments)

The surface desugaring — `if`/guards/literal patterns → `{:prim}` + `bool_elim`
— and BEAM codegen (`emit.ex`/`erase.ex` lowering `bool_elim` to a BEAM
`case`) are **E/C-layer, non-TCB**, each with its own oracle probe and
BEAM-verified increment.
