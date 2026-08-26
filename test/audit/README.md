# Audit findings — CLOSED (2026-07-10)

A per-file agent sweep of the dependent Core / kernel / normalizer / elaborator,
plus codegen and parser, wrote one deliberately-RED test file per audited source
file. Every finding that survived adversarial verification has now been disposed
of, so this directory holds no tests. It is kept for the method, which was worth
more than any single finding.

## What the sweep produced

~80 red tests. Adversarial verification (one skeptic per test, tasked with
refuting it) kept 33, refuted 28, and found 19 invalid. Of the 33: 30 were fixed
red-green, 3 were consciously declined. Two were genuine TCB soundness holes (the
`Bounded` compact-literal / tower bridge in `unify_one`, and positivity checking
bypassed via `typealias`).

## Where the findings live now

Fixes were promoted into the ordinary gated suite next to the code they
constrain, not kept here:

  * `test/cure/core/bounded_lit_coverage_soundness_test.exs`
  * `test/cure/core/positivity_typealias_soundness_test.exs`
  * `test/cure/core/hole_and_debruijn_test.exs`
  * `test/cure/core/final_core_boundary_test.exs`
  * `test/cure/core/serialize_untrusted_input_test.exs`
  * `test/cure/core/builtin_op_bool_codomain_test.exs`
  * `test/cure/elab/imported_module_dup_test.exs`
  * `test/cure/elab/typeclass_dispatch_boundaries_test.exs`
  * `test/cure/elab/erasure_relevance_test.exs` (appended)
  * `test/cure/elab/type_shadowing_test.exs` (appended)
  * `test/cure/elab/guard_lint_test.exs`, `test/cure/elab/extern_test.exs` (appended)
  * `test/cure/elab/cross_module_names_test.exs` (rewritten — it asserted a state
    later proved incoherent)

The three declines each carry a permanent test pinning where the edge is, so the
behaviour stays deliberate and fails loudly rather than drifting:

  * out-of-range positive de Bruijn index evaluates as a rigid free variable —
    pinned by Antigen's `:var_neutral` coverage cell in
    `lib/antigen/generators/conv_pair.ex`;
  * higher-kinded dictionary former — `test/cure/elab/typeclass_dispatch_boundaries_test.exs`;
  * a lambda argument declared before the argument that fixes its domain —
    `test/cure/elab/lambda_argument_order_test.exs`.

## What the sweep taught

A red test proves nothing on its own: it is red because it asserts behaviour the
code does not have, which is equally consistent with "the code is wrong" and
"the claim is wrong". Both failure modes showed up here — a mis-authored control
that aborted before its real assertion, and a claim resting on a stale comment in
`lib/` rather than on live code. **Confirm a finding by executing an independent
probe against the real API before believing it.**

The findings also shared a theme worth carrying into new code: *fail-open
catch-alls*. An unrecognized node answering "nothing here" instead of "unknown,
be conservative". The convention to copy lives in `Cure.Core.Term.term?/1` and
`Cure.Core.Validator.children/1`, both of which fail closed.

## Running a probe without perturbing the build

`mix run` re-emits the 6 MB escript on every invocation (the `compile:` alias in
mix.exs), which makes concurrent probing unsafe and slow. Use the prebuilt beams:

    ERL_LIBS=_build/test/lib elixir path/to/probe.exs

No writes, ~0.4s startup. Compile first (`MIX_ENV=test mix compile`) or you read
stale beams.
