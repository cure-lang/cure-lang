# Sound Effect Discipline (surface-level `!` effects)

**Date:** 2026-07-07
**Branch:** `feature/idris-parity`
**Status:** historical decision record — superseded as the primary effect
architecture by `2026-07-21-cure-computation-effect-typing.md` and its
stackless-Flow companion. The surface `!` rules remain migration guidance.

> **Superseded (2026-07-09 and 2026-07-21):** the stance that effects stay
> surface-only and out of Core is no longer the target state. The current
> architecture separates values from computations and represents qualitative
> effects as rows — see
> [`2026-07-21-cure-computation-effect-typing.md`](2026-07-21-cure-computation-effect-typing.md).
> The surface `!`-discipline fixes described below remain valid as an
> independent honesty repair for the classic pathway, but "the later
> evolution (option b)" is now the locked direction, not a someday.

## Purpose

Cure advertises an explicit effect system via the `!` annotation (e.g.
`lib/std/io.cure`: "carries the `! Io` effect so callers are forced to declare
it"). That guarantee does not currently hold. This spec defines the smallest
honest fix — **option (a)** from the effect-system discussion: make the existing
*surface* effect discipline sound, enforced, and mandatory, driven off types
rather than hardcoded names. It deliberately does **not** move effects into Core
or build algebraic effects / handlers; those are the later evolution (option b).

## Background — current state and its four defects

The machinery half-exists. `Cure.Types.Effects.infer_effects/2` walks a body AST
and collects an effect `MapSet`; `check_effects/3` compares declared vs inferred;
`classify_extern/1` classifies `@extern` targets by module. The surface type
`{:effun, params, ret, effects}` carries effects, and `Type.subtype?/2`
(`type.ex:160-172`) already implements **sound** subeffecting:

- `{:fun} <: {:effun}` (pure usable where effectful expected) — sound.
- `{:effun, E} <: {:fun}` only when `E = ∅` — sound.
- `{:effun, e1} <: {:effun, e2}` iff `e1 ⊆ e2` — sound subeffecting.

**The subtyping is correct and must be preserved. The defects are elsewhere:**

1. **Not enforced.** On a real violation, `checker.ex:770` `maybe_check_declared_effects`
   calls `Events.emit(:type_checker, :effect_error, …)` — it emits a *diagnostic
   event* and returns; the result is never folded into the `type_errors` list
   (unlike the neighbouring real `:extern_has_body` error). A function that
   violates its effect declaration still compiles.
2. **Not mandatory.** `maybe_check_declared_effects(nil, …) -> :ok`. A function
   with no `!` annotation is never checked, so it may silently perform any effect.
   This falsifies "callers are forced to declare it."
3. **Name-heuristic inference.** `infer_call_effects` matches hardcoded
   function-name tables (`@io_functions`, `@state_functions`, `@stdlib_effects`
   in `effects.ex:39-40, 32-36`). Rename an IO function and its effect vanishes;
   effects do not follow actual types.
4. **Higher-order blind spot.** Applying a function-typed parameter contributes
   no effects (a lambda param is not in the env with an effect signature), so an
   effectful callback silently launders its effects to `pure`.

Effects are surface-only: nothing in `lib/cure/core` or `lib/cure/elab` observes
them, and they are erased before elaboration. That layering is correct (Idris/Agda
keep effects out of the core) and is preserved here.

## Goals / non-goals

**Goals**

- A function's declared effects are a sound **upper bound** on what it does.
- Absent annotation means **pure**; using an effect without declaring it is a
  hard, build-failing type error.
- Effects **propagate**: a caller of an effectful function must itself declare (or
  otherwise account for) those effects.
- Effect information is read from **types/signatures**, not function-name tables.
- Higher-order calls are handled **soundly** (precisely when the callback's effect
  is known from its type; conservatively otherwise).

**Non-goals (explicitly deferred to option b / later)**

- No effects in Core / the trusted kernel. Effects stay a surface discipline,
  erased before elaboration.
- No algebraic effects, handlers, or resumable continuations.
- No effect *polymorphism* with effect variables (only monomorphic declared/known
  effects + a conservative top for unknowns).
- No change to the effect *kinds* taxonomy beyond what is stated below.

## Design

### D1. Effects are a surface join-semilattice, erased before Core

Effects are a set drawn from the fixed kind taxonomy (unchanged):
`:io`, `:state`, `:exception`, `:spawn`, `:extern` (conservative default). They
form a join-semilattice under union: `⊥ = ∅` (pure), `⊤ =` all kinds, join = set
union, order = subset (= subeffecting, already in `subtype?/2`). This is the same
shape as a future graded-effect axis, so the later migration is additive.

Boundary invariant: the elaborator drops effects when lowering surface → Core; the
dependent kernel never sees an effect. This keeps the fix independent of the
kernel-cleanup waves.

### D2. Default-pure, mandatory declaration

The absence of a `!` annotation means **declared effects `= ∅`** (not "unknown,
skip"). Replace the `nil -> :ok` short-circuit: `nil` declared effects is treated
as the empty set and still checked. Consequently a function that uses any effect
without declaring it fails to type-check.

### D3. Enforcement — violations are type errors, over-annotation is a lint

`maybe_check_declared_effects` must **return** diagnostics that are folded into the
function's `type_errors`, not emit-and-discard:

- `inferred ⊄ declared` (undeclared effect used) → **error `E091`**
  ("function `f` has undeclared effect(s): …; add them to its `!` annotation").
  Build fails.
- `declared ⊋ inferred` (over-annotation) → **warning** (not an error). Declaring a
  loose upper bound is sound and is a legitimate interface-conformance pattern, so
  it stays a lint, consistent with uniform strictness (it is not an unsoundness).
- `declared = inferred` → ok.

(`E091` is the next free code after the current maximum `E090`; register it in the
diagnostics registry.)

### D4. Type-driven inference; effects originate at externs and intrinsics

Effects have exactly two ground sources; everything else is propagation:

1. **`@extern` declarations** — the extern's effect is `classify_extern/1` of its
   target `{module, fun, arity}` (module-based classification tables `@io_modules`
   / `@state_modules` / `@spawn_modules` are the trusted FFI ground truth and are
   **kept**). This becomes the extern's `{:effun}` effect in the env.
2. **Intrinsic keywords** — `send`/message-send → `:state`; `receive`
   (`:async_operation`) → `:state`; `throw` → `:exception`; `spawn` → `:spawn`.
   (These already exist in `do_infer/3` and are kept.)

Propagation: a call to any other function reads that callee's effect set from its
**signature in the env** (`{:effun, _, _, E}` → `E`; `{:fun, …}` → `∅`). **Remove
the name-based Cure-function tables** `@io_functions`, `@state_functions`,
`@stdlib_effects`. Stdlib effects then come from the stdlib's own declared
signatures (e.g. `io.cure` declaring `! Io`), which already flow through the env —
no separate table needed.

### D5. Higher-order calls

When a function-typed value is applied, its effect is read from its **type**:

- Parameter/binding typed `{:effun, _, _, E}` → applying it contributes `E`.
- Parameter/binding typed `{:fun, …}` (pure) → contributes `∅`.
- A function-typed value whose effect set is **not statically known** (e.g. an
  unannotated higher-order parameter) → conservatively contributes `⊤` (all
  kinds), preserving soundness at the cost of precision.

This makes higher-order code sound today; precise higher-order tracking (effect
variables / polymorphism) is deferred to option (b). Programmers regain precision
by annotating callback parameters with `{:effun}` effect sets.

### D6. `@extern` annotations

Externs have no body to infer from; their effect is assigned by `classify_extern`.
An explicit `!` on an extern, if present, must **equal** the classification (a
mismatch is `E091`); otherwise the classification stands. Externs thus enter the
env as `{:effun}` with their classified effects, feeding D4 propagation.

## Migration & test impact

Per the cleanup strategy (compiler-gate-only; phase/ESP32 corpus out of scope;
dependent corpus may churn), the fallout is acceptable and expected:

- Programs that use effects without declaring them will newly fail with `E091` and
  must add `!` annotations. This is the point of the fix.
- Stdlib modules that already declare effects (`io.cure`, `time.cure`) should pass;
  any stdlib function that uses an effect without declaring it is a latent bug this
  surfaces and must be annotated.
- The removed name tables mean any effect that *only* worked via name-matching now
  requires a real signature; audit stdlib signatures during implementation.

## Testing

Red/green per defect (checker-level tests, mirroring
`test/cure/compiler/melquiades_parser_test.exs` effect probes):

1. Undeclared effect → build fails with `E091` (defect 1 + 2).
2. `nil` annotation + effectful body → fails (defect 2).
3. Over-annotation → warning, builds (D3).
4. Effect renamed function still tracked via signature, not name (defect 3).
5. Effectful callback passed to a higher-order function propagates its effect;
   unannotated callback conservatively forces `⊤` (defect 4 / D5).
6. Extern effect flows to callers via classification (D4/D6).
7. Subeffecting still accepted (`{:effun,e1} <: {:effun,e2}` for `e1 ⊆ e2`).

## Relationship to the kernel-cleanup strategy

Independent and non-blocking: this is a **surface** discipline, erased before Core
(D1), so it neither depends on nor blocks any Wave. It is the near-term half of the
effect story; the long-horizon evolution — library-level algebraic effects /
graded-monad handlers on the clean dependent core — is additive once the core
lands and is out of scope here. See
[`2026-07-07-dependent-kernel-cleanup-strategy-design.md`](2026-07-07-dependent-kernel-cleanup-strategy-design.md)
(effects deliberately stay out of Core).
