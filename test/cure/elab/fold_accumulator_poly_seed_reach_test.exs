defmodule Cure.Elab.FoldAccumulatorPolySeedReachTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # RESOLVED (2026-07-18). This reach pin — a polymorphic seed in `foldl`
  # accumulator position whose type parameters are determined only through the
  # fold's lambda — now elaborates, so the `@tag :skip` / `:reach` pin is retired
  # and this is a live regression guard. The deferred-argument machinery
  # (`bidir_app_slot` now postpones an arg that infers a type but does not yet
  # unify against a still-meta domain, and `resolve_deferred_slots` re-checks it
  # once a later sibling — here the lambda — solves the accumulator type) resolves
  # the mutually-determined `b`/`?k`/`?v` that the old single-pass, in-order path
  # could not. Kept verbatim (the exact from_list-over-Map probe) as the guard.
  #
  # Historical diagnosis retained below for the bisection record.
  #
  # REACH PIN (#23 value-surface parity) — a general elaborator inference gap,
  # NOT a soundness issue. Surfaced while parameterising `Std.Map` to `Map(k, v)`
  # so `Std.Set` could elaborate: `Std.Set.from_list`/`intersection`/`difference`
  # all seed a `foldl` with a polymorphic empty map, `foldl(list, new(), lambda)`.
  #
  # Symptom: a polymorphic function used as the ACCUMULATOR argument of a
  # higher-order fold, whose type parameters are determined only transitively by
  # the fold's lambda (through the accumulator type `b`), has its metavariables
  # committed BEFORE the lambda constrains `b` — leaving them unsolved:
  # `{:error, {:unsolved_metavariables, :new}}`.
  #
  # Boundary (see scratchpad/nullary.exs + foldacc.exs):
  #   * `fn empty() -> Map(t, Bool) = new()`            -> OK   (return-type flow
  #                                                              pins the seed)
  #   * `fn single(x: t) -> Map(t,Bool) = put(x,true,new())` -> OK (arg pins it)
  #   * `foldl(list, new(), lambda)` seed pinned by lambda  -> FAIL (this pin)
  # So the trigger is a polymorphic seed in accumulator position whose params are
  # constrained only by a later function-typed argument.
  #
  # VERIFIED ROOT CAUSE (instrumented `bidir_app_slot`/`resolve_deferred_slots`,
  # elaborator.ex:5161-5303). In `foldl(list, new(), lambda)`:
  #   1. arg `list` solves foldl's element param `a := t`.
  #   2. arg `new()` at domain `b` (a metavar): infers standalone, but
  #      `finish_global_app` rejects it at the `has_meta?` gate (its own implicit
  #      `{k}{v}` are unsolved and no expected type is threaded in infer mode) →
  #      the slot DEFERS it WITHOUT unifying `new()`'s codomain shape `Map(?k,?v)`
  #      into `b`, so `b` stays `{:meta,1}`.
  #   3. arg `lambda` at domain `a -> b -> b`: also DEFERS (its param domain path).
  #   4. `resolve_deferred_slots` is SINGLE-PASS, IN-ORDER, and re-checks each
  #      deferred arg via `elaborate_expr_checked` (which does NOT thread `mctx`)
  #      only once its domain is fully concrete. It processes `new()` first, finds
  #      `b` still `{:meta,1}`, and fails — the lambda (which would solve
  #      `b := Map(t, Bool)` from `put(elem, true, acc)`) never gets to run first.
  # `b`/`?k`/`?v` are MUTUALLY determined by new()'s shape + the lambda's body, and
  # no single in-order, non-threading pass makes either domain concrete before its
  # arg's turn.
  #
  # NO LONGER MOTIVATED BY Std.Set (2026-07-11). This gap was thought to be the
  # last thing blocking Std.Set's dependent capability, requiring an operator-level
  # architectural decision. It is not: Std.Set does not need the fold. Rewritten
  # with ordinary structural recursion over the element list (each `match` branch
  # checked against the declared return type, so `[] -> new()` is pinned by the
  # expected type — no polymorphic accumulator seeded through a fold), EVERY
  # Std.Set operation elaborates dependent against a parameterised `Map(k, v)`.
  # Proven + locked in `test/cure/stdlib/set_dependent_capability_test.exs`. So
  # this pin no longer gates any module; Std.Set is dependent-capable and merely
  # classic-coexistence-blocked (the classic checker cannot instantiate the
  # parameterised `Map(k,v)` across match branches — `E033`).
  #
  # This remains a GENUINE, general elaborator inference limitation worth pinning
  # (any `foldl(list, poly_seed(), lambda)` where the seed's params are determined
  # only through the lambda), so the test stays. FIX SKETCH (deliberate
  # spine-inference rework — NOT a safe additive tick edit; high regression risk
  # across all applications): make deferred resolution (a) unify a deferred
  # FUNCTION arg's instantiated codomain shape into its domain at defer time
  # (parallel to `solve_deferred_domain`'s constructor branch, which today only
  # handles ctors), AND (b) iterate to a fixpoint with mctx-threading re-checking
  # so a later arg can solve an earlier arg's domain. See
  # [[dep-pipeline-survey-2026-07-11]].
  test "polymorphic seed in foldl accumulator position is solved from the lambda" do
    src = """
    mod Probe
      opaque type Map(k, v)
      @extern(:maps, :new, 0)
      fn new() -> Map(k, v)
      @extern(:maps, :put, 3)
      fn put(key: k, value: v, map: Map(k, v)) -> Map(k, v)
      @extern(:lists, :foldl, 3)
      fn foldl(list: List(a), acc: b, f: a -> b -> b) -> b
      fn from_list(list: List(t)) -> Map(t, Bool) =
        foldl(list, new(), fn(elem) -> fn(acc) -> put(elem, true, acc))
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
