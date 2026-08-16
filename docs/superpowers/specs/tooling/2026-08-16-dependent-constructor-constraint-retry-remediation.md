# Dependent-constructor constraint retry remediation

**Status:** phase 2 implemented; prefix-frame representation remains for a later performance pass
**Date:** 2026-08-16  
**Scope:** typed elaboration of indexed constructor applications

## Problem

The current cold compiler profile is dominated by typed elaboration of the
dependent Regex proof modules. A serialized profile of the complete standard
library measured approximately 156.7 seconds and 16,346 aggregate call-attempt
records. The largest repeated site is
`Std.Regex.Proof#complete_concat_left_acceptance` at
`lib/std/regex_proof.cure:2257`, whose nested `mk_pair` construction generated
729 `constructor_infer` failures and 729
`constructor_bidirectional` failures. The repeated failures are not evidence of
an invalid proof: the declaration elaborates successfully. They are evidence
that the same nested constructor syntax is elaborated again after a sibling
metavariable is refined.

The canonical retry authority is
`Cure.Elab.Elaborator.resolve_ctor_fields/12`. It currently:

1. scans every pending field on every fixpoint sweep;
2. rebuilds each de Bruijn frame prefix with `params ++ ...` and repeated
   `Enum.at/2` calls;
3. calls `try_infer_field/6`, which discards the reason for every failure;
4. treats a hard type mismatch exactly like a blocked metavariable;
5. re-elaborates a blocked nested constructor from its surface AST on every
   later sweep; and
6. retries contextual normalization in `unify_in_context/5` after failed
   unification, even when the same terms and metavariable state have already
   been seen.

This is a retry and constraint-scheduling defect. It is not a request to weaken
the kernel, accept unchecked terms, or make all definitions reducible.

## Reference architecture

The implementation should follow the useful common boundary in Agda and Lean:

* Agda's `checkArgumentsE` (in
  `/Users/ch/Develop/agda/src/full/Agda/TypeChecking/Rules/Application.hs`)
  retains the checked prefix and postpones only a
  problem blocked on a known metavariable. A blocked problem is resumed when
  that metavariable is woken; the whole application is not restarted.
* Agda's conversion checker (in
  `/Users/ch/Develop/agda/src/full/Agda/TypeChecking/Conversion.hs`) returns a
  blocked constraint instead of repeatedly
  normalizing an unchanged term in the caller.
* Lean's `ElabAppArgs.State` (in
  `/Users/ch/Develop/lean4/src/Lean/Elab/App.lean`) carries the current function
  type, already checked
  arguments, and remaining arguments in an array. `addNewArg` advances the
  state, so successful arguments are never elaborated again.
* Lean's defeq checker (in
  `/Users/ch/Develop/lean4/src/Lean/Meta/Basic.lean` and
  `/Users/ch/Develop/lean4/src/Lean/Meta/ExprDefEq.lean`) separates
  easy/explicit arguments from postponed
  higher-order or metavariable-dependent arguments and uses an attempt-local
  defeq cache. The cache is invalidated when local metavariable dependencies
  change.

The Cure implementation may use different data types, but it must preserve the
same observable invariants: successful work is monotone, blocked work is keyed
by its blockers, and hard errors are terminal for the current constructor
candidate.

## Goals

1. Preserve all currently accepted dependent-constructor programs, including
   nested and erased sibling refinement.
2. Preserve structured diagnostics for genuine result/index mismatches and
   unsolved fields.
3. Ensure a field is re-elaborated only when one of the metavariables occurring
   in its expected type or its blocker set has changed.
4. Ensure hard failures are reported immediately rather than converted into
   indefinite deferrals.
5. Remove avoidable quadratic frame-prefix construction.
6. Add bounded, attempt-local caching for contextual unification and
   meta-aware normalization.
7. Expose counters sufficient to demonstrate retry reduction without making
   profiling state part of semantic state.
8. Keep the kernel as the final checker of every assembled Core constructor.

## Non-goals

* No kernel or TCB change.
* No global memoization of terms across compilation units or metavariable
  contexts.
* No broadening of delta-reduction or transparency policy.
* No catch-all conversion of errors to `:defer`.
* No macro-specific path and no Regex-specific workaround.
* No change to the surface syntax of constructors, patterns, or proofs.

## Required red regressions

Add `test/cure/elab/dependent_constructor_constraint_retry_test.exs` before
changing the implementation. It must include:

1. A small indexed constructor whose first field determines a hidden index and
   whose later field is a nested constructor. It must elaborate successfully
   when the fields are written in either dependency order.
2. A nested erased-sibling example equivalent to the existing
   `SiblingContextRefinementTest` regression. The result must remain accepted
   and the erased field must remain erased in emitted Core.
3. A constructor whose nested field has a genuine incompatible type. It must
   fail with the existing structured constructor diagnostic, not become an
   `:unsolved_field_type` timeout or an `ArgumentError`.
4. A profile assertion around `Program.elaborate/2` that records constructor
   field attempts. The successful nested example must have no repeated attempt
   after a stable context; the assertion should use a generous upper bound
   rather than a machine-dependent wall-clock timeout.

The existing sibling-refinement and checked-constructor-diagnostic tests remain
mandatory compatibility gates. A red regression must fail before the fix for
the new retry metric or duplicate-attempt condition; semantic tests must remain
red/green in the usual way.

## Design

### 1. Explicit field-resolution result

Replace the implicit `:defer` protocol of `try_infer_field/6` with a tagged
result:

```elixir
{:ok, term, typed_type, mctx}
{:blocked, blockers, attempt_state}
{:error, diagnostic_reason}
```

`blockers` is the finite set of metavariable IDs occurring in the expected
field type, the inferred argument type, or a conversion constraint that could
not proceed. A failure with no blocker is a hard error. A unification failure
between two constructor/data heads, primitive types, or otherwise rigid terms
is therefore terminal and is never put back on the pending queue.

The classifier must be conservative: if it cannot prove that a failure is
blocked, it returns `:error`. The assembled term still goes through the kernel,
so this change can reject only cases that were previously retried and either
eventually rejected or accepted through another successful path.

### 2. Monotone work-list state

Represent constructor resolution with a state containing:

```elixir
%{
  fields: %{position => %{ast: ast, type: field_type, status: status}},
  values: %{position => core_term},
  prefix: tuple(),
  blocked_by: %{meta_id => MapSet.t(position)},
  deferred_indices: [...],
  mctx: mctx,
  revision: non_neg_integer()
}
```

Successful values are stored once. The prefix is an array/tuple or reverse
list that can be extended in O(1); it must not be rebuilt with `++` for every
field. The field's dependency fingerprint is the sorted set of metas in its
instantiated expected type plus the metas in its blocker set. A field already
attempted at the same fingerprint is not attempted again.

When `Unify` solves a metavariable, enqueue only fields registered under that
ID. If a deferred result-index equation is discharged, enqueue its dependent
fields as well. A fallback full scan is permitted only as a debug assertion or
when no blocker information can be recovered, and must increment a diagnostic
counter.

### 3. Preserve elaborated nested terms

On a blocked attempt, retain the typed result when it is structurally valid to
do so, together with its blocker fingerprint. On wake-up:

* reuse the typed Core term if only the expected type's metas were solved and
  the term's own inferred type remains valid;
* otherwise resume the nested application through its continuation/state;
* re-elaborate from the AST only when the previous attempt produced no reusable
  state or its local context changed.

This is the Cure equivalent of Agda's postponed problem and Lean's incremental
`ElabAppArgs.State`; it is not a second semantic elaborator.

### 4. Attempt-local defeq/normalization cache

Add a private cache to the elaboration operation (not to published interfaces)
for:

* `Unify.unify` outcomes on zonked term pairs;
* `contextual_normalize_meta_aware` results; and
* `Conv.conv?` outcomes for meta-free terms.

The key includes the operation kind, both terms, context identity/signature,
and the metavariable revision. Meta-free successful results may be retained for
the operation; meta-bearing results are valid only for the exact revision.
Failed results must retain whether they were blocked or rigidly incompatible.
Never cache a result across a solved metavariable or across modules.

The cache is populated at the existing `unify_in_context/5` construction site,
so all constructor and ordinary call paths share one authority. Add hit/miss
counters under the existing profiling scope; no semantic branch may depend on
profiling being enabled.

### 5. Outer candidate retry rule

The named-call dispatcher may try inference and bidirectional constructor
strategies, but a constructor candidate returning a classified hard error must
not be re-entered through another constructor strategy solely because the first
strategy failed. A blocked result may install one continuation; after it is
resumed, the dispatcher sees the same terminal success or diagnostic. Existing
overload candidates remain independent and retain their source-context
diagnostics.

### 6. Diagnostics and observability

Add operation-local counters:

* `constructor_field_attempts`;
* `constructor_field_retries`;
* `constructor_field_blocked`;
* `constructor_field_hard_failures`;
* `constructor_field_reused`;
* `contextual_normalize_calls`;
* `contextual_normalize_cache_hits`; and
* `contextual_normalize_cache_misses`.

Counters are returned only by explicit profiling APIs and are excluded from
interface hashes, Core terms, and diagnostics unless a diagnostic is already
being rendered. The regression test asserts counts; the benchmark reports them
alongside declaration timings.

## Implementation order

1. Add the red semantic/profile regressions and the operation-local counter
   plumbing.
2. Introduce the explicit field-result classifier, retaining the old full-scan
   path behind a temporary internal fallback counter.
3. Convert `resolve_ctor_fields/12` to the blocker-keyed work list and O(1)
   prefix representation.
4. Add the attempt-local contextual unification cache.
5. Thread reusable nested-attempt state through the field resolver.
6. Tighten named-call constructor fallback so hard failures are not retried.
7. Remove the temporary full-scan fallback only after the focused and full
   suites pass.
8. Run the canonical pipeline, the complete test suite, and one serialized cold
   profile. Update `docs/COMPILER_PERFORMANCE_BASELINES.md` with wall time and
   counters; do not claim a speedup from a single noisy sample.

## Implemented in phase 1

This change implements the first sound reduction in retry work at the canonical
constructor-dispatch authority:

* constructor inference installs an operation-local retry cache before entering
  the inference/bidirectional pair;
* nested constructors that fail with an underdetermined-index result are
  recorded by canonical constructor key and exact surface argument AST;
* the bidirectional fallback recognizes that blocked AST and postpones it until
  the sibling field refines its expected type, instead of invoking the nested
  elaborator a second time;
* the cache is process-local, scoped to one outer constructor operation, and
  deleted in an `after` clause, so it cannot affect interface hashes or leak
  between declarations; and
* `CallAttemptProfile` exposes operation-local counters and the regression suite
  asserts that the nested blocked constructor has one bidirectional attempt.

The existing all-present inference path remains the compatibility fallback. A
first attempt to classify every field failure as hard or blocked was rejected:
the experiment changed a legitimate `Std.Regex.Language` indexed refinement
into E093. Full blocker-keyed scheduling therefore remains a separate phase and
must be introduced with a smaller classifier regression before it replaces the
current fixpoint behavior.

## Implemented in phase 2

Phase 2 keeps the compatibility fixpoint but makes its retry authority explicit
and revision-aware:

* `try_infer_field/6` now returns tagged `{:ok, term, typed_type, mctx}`,
  `{:blocked, blockers, attempt_state}`, or `{:error, reason}` outcomes. The
  classifier only treats a constructor/data-head or primitive-head clash as
  rigid; global/application mismatches and unsupported nested expressions stay
  blocked because their surrounding telescope may still be refined.
* Blocker fingerprints include the instantiated expected field type, its
  metavariable IDs, the metavariable-context revision, and the deferred-index
  equations. A field is not retried at the same fingerprint, but a sibling
  solution or discharged deferred equation changes the fingerprint and wakes
  it. This fixes the earlier unsound skip, which omitted the context revision
  and regressed `Std.Regex.Language` with E093.
* The operation-local `AttemptCache` now also caches contextual normalization
  results. Its key includes the zonked term, metavariable revision, conversion
  signature, and context length; it is scoped by `Program.check_ast/1` and is
  never published in an interface or environment hash.
* Field retry, reuse, blocked, hard-failure, and contextual-normalization
  counters are exposed through `CallAttemptProfile`. The regression fixture
  observes two field attempts, one blocked retry, and one reused nested term;
  the cache regression also proves hit reuse and scope cleanup directly.
* The incompatible-field regression asserts the existing structured
  `index_mismatch` diagnostic, while the stdlib compatibility fixtures continue
  to pass. Kernel checking remains the final authority for every assembled
  constructor.

The full O(1) prefix-frame representation and a wake-list that enqueues only
fields registered under changed blocker IDs are intentionally not claimed here:
the current resolver still retains its deterministic compatibility sweep. Those
changes require a separate proof that local branch variables and deferred
computed indices cannot invalidate a cached prefix.

## Soundness and acceptance criteria

* All existing constructor, match, totality, TCB, Antigen, and doc-fence gates
  pass.
* The new incompatible-field test produces a structured diagnostic naming the
  constructor and field context.
* No emitted closure contains a bare unresolved definition.
* Kernel rechecking remains enabled for every assembled constructor.
* On the nested profile fixture, field re-elaboration count is bounded by the
  number of blocker revisions, not the product of fields and fixpoint sweeps.
* A warm compilation does not perform semantic elaboration for unchanged
  interfaces.
* A cold profile shows reduced nested-constructor attempts and contextual
  normalization calls without moving any correctness work into an unchecked
  cache.

## Rollback

If a regression appears, disable only the work-list/cache path with an internal
feature flag and retain the explicit `:blocked` versus `:error` classifier.
Revert the optimization after preserving the smallest failing source and its
counter trace. Do not restore the old catch-all deferral silently: it is the
defect this specification is intended to eliminate.
