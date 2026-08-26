# Type-Aware Macro Tier (MetaM Analogue) — Design

**Status:** approved design, **PARKED** — not scheduled for implementation this
week (token budget). This document is the cold-start map for whoever picks it up.
**Branch:** `core-let-binder` (optic-path programme; sits above the Std.Optic stack)
**Date:** 2026-07-19
**Chosen route:** Route B of the two routes weighed in discussion (the general
type-aware tier), deliberately over Route A (a bespoke elaborator-level
reinterpretation of projection/bracket/`<~` for optics only). Route A is a strict
subset of this work and remains the fallback if Route B is descoped.

## Goal

Give Cure a **type-aware Tier-3 macro tier**: macros that run *during*
elaboration with access to the local typing context, so a macro can ask "what is
the type of this sub-expression?" and expand differently based on the answer.
This is the Lean `MetaM` model — macro code that runs in the elaboration monad
with `inferType`/`whnf` available — as opposed to today's macros, which are a
purely syntactic pre-pass.

The motivating client is **optic projection sugar**: reinterpreting `u.scores`,
`u.scores[0]`, and `lhs <~ rhs` as optic operations, synthesizing inline lenses
and affines with full knowledge of the record/field types at the use site. But
the deliverable of *this* spec is the **general mechanism**, not the optic
surface — the optic client is specified as a follow-on (see "The optic client"
below). The mechanism is
justified only if we want type-directed expansion to be a **reusable facility**
(future clients beyond optics, and ultimately user-authored type-aware macros).
If that reuse never materializes, Route A is the cheaper delivery and this spec
should be reconsidered before implementation.

## Background — why today's macro tier cannot be type-aware

The current Tier-3 `computed by` macro tier is **pre-elaboration** by
construction. In `Cure.Elab.Declarations.elaborate_real_body/3`
(`lib/cure/elab/declarations.ex:582`) the order is fixed:

1. `MacroExpand.expand(body_expr, env, callback_context: …)` — expand **every**
   macro in the body to completion;
2. `build_context(env, sig.telescope)` — *then* construct the typing context;
3. `elaborate_body_typed(body_expr, sig, ctx, def_env)` — *then* elaborate and
   type-check.

Macro expansion finishes **before the typing context exists**. Declaration-position
expansion (`Cure.Elab.Program.expand_declaration_nodes/2`,
`lib/cure/elab/program.ex:540`) runs even earlier — before any per-def
elaboration at all.

`Cure.Elab.MacroExpand.execute_with_env/5` (`lib/cure/elab/macro_expand.ex:222`)
reinforces this. It:

- reflects the use-site input to `Std.Syntax` Core values via
  `MacroSyntax.to_syntax/1` — **untyped surface AST**, no type annotations;
- elaborates the elab function with an **empty local context**:
  `Elaborator.elaborate_expr_typed(elab_ast, [], Context.empty(env), env)` — the
  `[]` is the local-names list, `Context.empty(env)` carries only globals;
- applies the elab to the reflected input, normalizes with the kernel, and
  reflects the result back to surface AST, which the ordinary declaration path
  then elaborates.

So a macro today sees: **raw surface syntax** + the **global env** (constructor
names, global signatures). It cannot see: local variable types, the enclosing
function's telescope, or the inferred type of any sub-expression — none of that
has been computed when it runs. `u.scores` cannot become "the `User.scores`
lens" because `u : User` is simply not known yet.

By contrast, the elaborator *does* hold everything needed. Every
`Elaborator.elaborate_expr_typed/4` clause receives `names, ctx, env`, and the
record-projection clause (`lib/cure/elab/elaborator.ex:607`) already infers the
base's type inside `record_projection/5`. The type context is present *there* —
it is only absent in the macro pre-pass. **Type-aware macros = move expansion
from the pre-pass into the elaborator, and give the macro a typed view of its
input.**

## Design

Three pieces: (1) interleave expansion into elaboration; (2) give the macro a
typed input and a query API; (3) preserve hygiene, termination, and the
quantity/erasure discipline now that expansion is re-entrant.

### 1. Interleaved expansion — a `computed_use` clause in the elaborator

Add a clause to `Elaborator.elaborate_expr_typed/4` matching
`{:computed_use, meta, [elab, input]}` (and `{:quoted_syntax, …}` passthrough).
When the elaborator reaches a use-site, it expands **then**, with the live
`names`/`ctx`/`env`, and re-enters `elaborate_expr_typed` on the produced AST.

Consequently, the pre-pass calls to `MacroExpand.expand` must be **removed from
the body path** (`declarations.ex:585`) and reduced to only what genuinely has no
typing context: declaration-position macros that produce *new top-level
declarations* (`program.ex:540`) legitimately run before per-def elaboration and
stay a pre-pass. The dividing line is precise:

- **Declaration-producing macros** (emit a `fn`/`rec`/`type`): stay pre-pass,
  unchanged — they have no local context by nature and this spec does not give
  them one.
- **Expression-position macros** (`computed_use` inside a body): move to
  interleaved elaboration. This is the set that gains type-awareness.

`build_context` therefore must run *before* expression-macro expansion. Since
interleaved expansion happens inside `elaborate_body_typed`, the context is
already built by then (step 2 precedes step 3 today), so this falls out naturally
once the body pre-pass call is deleted. The `function_signature`/`build_context`
sequencing in `elaborate_real_body/3` is unaffected.

### 2. Typed input + query API (the MetaM surface)

The macro must be able to consult types. Two sub-options, decided here:

**(a) Typed reflection (baseline, ship first).** Extend `MacroSyntax` so a
reflected sub-term optionally carries its **inferred type** as a companion
`Std.Syntax` value. At a use-site the elaborator infers the types of the macro's
immediate operands (using the live `ctx`) and threads them into the reflection
alongside the syntax. The macro reads `type_of(operand)` as data. This covers the
optic client fully: `u.scores` needs only the type of `u` and the field `scores`.

**(b) Elaboration callback (`inferType`/`whnf`) — the true MetaM (follow-on).**
Expose a reflected callback the macro's Core code can invoke to infer the type of
an *arbitrary* sub-term or reduce a type to WHNF on demand. This is strictly more
powerful (the macro drives inference, not just consumes pre-computed types) and
strictly harder: it means Core-level macro code calling back into the Elixir
elaborator mid-normalization, which entangles the macro evaluator with the
elaborator's reentrancy. **Not in the first cut.** Baseline (a) is specified as
the shipping target; (b) is a documented extension point.

Concretely, `execute_with_env` changes from
`elaborate_expr_typed(elab_ast, [], Context.empty(env), env)` to elaborate the
elab against the **live** `names`/`ctx` passed down from the elaborator, and the
input reflection gains a type-carrying variant. The `callback_context` plumbing
(`macro_expand.ex:41`, threaded as `:expansion_context`) is the existing channel
for "where was I invoked" and extends naturally to carry the typed context handle.

### 3. Hygiene, termination, erasure — re-established under re-entrancy

Moving expansion inside elaboration means it can now be **re-entered** (a macro
expands to a term containing another macro, elaborated recursively). The
safeguards currently living in the pre-pass must be preserved:

- **Termination / cycle detection.** `MacroExpand`'s active-stack cycle detection
  (`begin_expansion`/`end_expansion`, keyed by `expansion_key/1` on
  `{keyword, elab-syntax, input-syntax}`, `macro_expand.ex:128–152`) must move
  with expansion. Under interleaving, the active-stack state has to live in (or be
  threaded through) the elaboration context rather than `MacroExpand`'s local
  `state` map, so a macro re-entered via `elaborate_expr_typed` still sees the
  enclosing frames. **This is the single largest correctness risk** and needs its
  own test battery (a self-referential macro must still be rejected, not loop).
- **Freshening / hygiene.** `Parser.freshen_generated/2` (`macro_expand.ex:262`)
  currently freshens generated binders against a counter in `MacroExpand` state.
  Interleaved expansion must keep a monotone fresh-counter across nested
  expansions; source it from the elaborator's existing fresh supply if one exists,
  else thread it through the context.
- **Quantity / erasure (M8.3).** Macro output is elaborated like any term, so
  `Relevance.check` (`declarations.ex:606`) still runs on the *final* body.
  Because expansion now happens after `build_context`, a macro can legitimately
  produce terms mentioning local binders with grades — the relevance check must
  see the fully-expanded body, which it does (it runs on `body_term` after
  `elaborate_body_typed`). No change expected here, but it is an explicit
  verification point, not an assumption.

### TCB analysis

**Zero TCB growth.** Macro output is re-elaborated and kernel-checked exactly as
today — the kernel re-checks every term the macro produces. Type-awareness only
changes *which* well-typed term the macro emits, never whether the kernel
validates it. `inferType` results the macro consults are advisory inputs to
expansion, not trusted facts about the output. This holds for both sub-option (a)
and (b). The elaborator itself is elaboration-critical but not the trusted core;
the existing "kernel re-checks macro output" boundary (`macro_expand.ex`
moduledoc) is preserved verbatim.

## Phasing

Each phase is independently testable and commits before the next.

1. **Interleave without types.** Add the `computed_use` clause to
   `elaborate_expr_typed`; delete the body pre-pass call; move cycle-detection and
   freshening state into the elaboration path. Existing macros must produce
   byte-identical elaborated output (the whole macro-family test suite is the
   gate). No type-awareness yet — this is the risky plumbing move, done in
   isolation so a regression here is unambiguous.
2. **Typed reflection (sub-option a).** Add the type-carrying `MacroSyntax`
   variant; infer operand types at the use-site; thread them in. Gate: a trivial
   type-directed macro (expands to `:a` vs `:b` by operand type) elaborates each
   branch correctly.
3. **Erasure/hygiene re-validation.** Dedicated adversarial tests: self-referential
   macro rejected; hygienic capture avoided; a macro emitting a graded-binder term
   passes/fails `Relevance.check` correctly.
4. **(Deferred extension) `inferType`/`whnf` callback (sub-option b).** Only if a
   client needs macro-driven inference. Not scheduled.

## The optic client (follow-on, out of scope here)

Once the tier exists, the optic surface is a *client* spec:

- Postfix subscript `expr[i]` — **new parser syntax** (`:lbracket` is currently
  list-literal-prefix only; no postfix subscript exists today).
- `<~` — **new operator**, absent everywhere today (not in `lib/std/operators.cure`).
  Per the resolved operator architecture it is a fixity declaration (ambient via
  `operators.cure`) + a meaning; here the meaning is a type-aware macro that emits
  `set`/`over`. Gated harmlessly by `{:no_operator_meaning, op}` when not in scope.
- `u.f`, `u.f[i]` reinterpretation — a type-aware macro that, seeing `u : R`,
  emits the `R.f` field lens / `compose(R_f, ix(i))`, reusing the **already-proven
  handwritten-lens machinery** and the `Std.List.at`/`set_at`-backed `ix` affine
  (tasks #12/#13, landed).

These build on the `Std.Optic` substrate already in place; this spec is their
prerequisite, not their container.

## Risks & open questions

- **R1 (highest): cycle-detection under re-entrancy.** Threading the active-stack
  through elaboration is the crux; get it wrong and either infinite loops slip
  through or legitimate nested expansions get falsely rejected. Phase 1 must land
  this with explicit tests before any type work.
- **R2: order-of-elaboration determinism.** Interleaved expansion means a macro's
  operand types depend on elaboration order (esp. under implicit-argument
  postponement). Confirm expansion sees *resolved* types, or defines behavior when
  an operand's type is still a metavariable at expansion time (likely: postpone the
  expansion, mirroring `bidir_app_slot`'s stuck-arg handling).
- **R3: declaration- vs expression-macro split.** The two paths must not both
  process an expression-position `computed_use`. Verify the pre-pass no longer
  touches body-position uses after Phase 1.
- **O1 (product question, not semantics): user-authored macros.** The reuse
  argument for Route B rests on eventually letting users write type-aware macros.
  If that is not actually wanted, Route A delivers the optic surface far cheaper
  and this spec should be reconsidered before implementation begins.

## Effort

~1.5–3 weeks for phases 1–3 (baseline typed reflection). Phase 1 alone is several
days and carries most of the risk. Sub-option (b) is an open-ended extension, not
estimated here. **Parked; revisit when token budget allows.**
