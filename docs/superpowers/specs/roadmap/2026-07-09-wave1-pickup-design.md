# Value-Surface Wave 1 — `pickup` — Design (task #23, Wave 1)

**Date:** 2026-07-09. First wave of the value-surface parity program (roadmap `2026-07-09-value-surface-roadmap-design.md`, hardened fcc768d). Teaches the dependent elaborator the `pickup` predicate-dispatch form. Chosen as Wave 1 because it is pure value surface with a direct existing Core target (no new primitive, no kernel change, no representation decision) — it de-risks the elaborator-clause + oracle harness the later waves reuse.

## 1. What pickup is + why it's nearly free

`pickup` is the predicate-dispatch counterpart to `match` (parser.ex:2073-2119). Surface:
```
pickup
  g1 -> b1
  g2 -> b2
  else -> e
```
Parser output: `{:pickup, meta, clauses}` where each clause is `{:pickup_clause, cmeta, [guard, body]}` or the mandatory terminator `{:pickup_else, emeta, [body]}`. **A THIRD terminal shape exists**: PICKUP §5.2 admits a trailing `true -> body` clause as an "alternative form" terminator — this parses to an ordinary `{:pickup_clause, cmeta, [{:literal, _, true}, body]}`, NOT a `{:pickup_else, ...}` (`pickup_terminator?/2`, parser.ex:2229-2237; exercised by `pickup_test.exs:57-65`, "trailing `true ->` is admitted as an alternative-form terminator"). A pickup block using this form has NO `{:pickup_else, ...}` node anywhere in its clause list. Classic codegen treats this shape as its own case, distinct from `pickup_else` (`codegen.ex:1465-1473`, "treat it as the else") — the desugaring below (§2) must do the same. The terminator (either shape) is enforced at PARSE time (`validate_pickup_clauses`, parser.ex:2116) — a `pickup` with no valid terminator is already a parse error, so "terminator mandatory" needs no elaborator work.

Classic semantics (the oracle, `codegen.ex:1454-1500` + `checker.ex:1349-1366`): a clause chain lowers to nested 2-arm `case Bool of True -> body ; False -> <rest>`, guards must be Bool (E079), all branch types must join (E080).

**The dependent pipeline already has this exact target.** `{:conditional, meta, [c, t, e]}` is fully elaborated in BOTH modes (elaborator.ex:466-473 infer, :1024-1028 checked) via `bool_case/5` (elaborator.ex:2646, a `:case` on the inductive Bool). The conditional clause already: checks the condition against Bool (elaborator.ex:467 — this IS the E079 rule), infers the then-branch, and checks the else-branch against the then-branch's type (elaborator.ex:470 — this IS the E080 join rule). Guarded `match` arms already desugar to the identical `{:conditional, [], [g, b, acc]}` shape: `fold_leaf_rows/1` builds it directly at elaborator.ex:3090-3097, and the sibling `mk_if/3` helper (elaborator.ex:2882, called at :2859/:2876) constructs the same shape for a different match-compilation path — two existing call sites, not one, both producing exactly the node `desugar_pickup` will emit.

So `pickup` is a **pure syntactic desugaring** to a right-nested `:conditional` chain — no new Core, no kernel change, no new typing rule; it reuses the conditional path's Bool-guard and branch-join checks verbatim.

**Known scoping gap (inert for Wave 1, ledgered):** `docs/PICKUP.md` §5.4 formally specifies that a guard `g_i` may introduce bindings that are then visible in its own right-hand side `e_i` ("the right-hand side is evaluated in the scope of `g_i`"), and classic `codegen.ex:1477-1478` threads compiler state from guard to body compilation specifically to honor this. The `:conditional` desugaring CANNOT express this: `elaborate_expr_typed`/`elaborate_expr_checked` elaborate the condition, then-branch, and else-branch against the SAME unextended `names`/`ctx`/`env` (elaborator.ex:466-470, :1024-1027) — no scope extension flows from the condition into the then-branch. This is currently harmless: the guard grammar is `parse_expr(state, 0)` (parser.ex:2153), an arbitrary expression, but the only Cure construct that introduces a scope-extending binding as a bare expression is `{:assignment, meta, [pattern, value]}` (a `let` without `in`, parser.ex:1344-1392), and the dependent elaborator has NO clause elaborating a bare `{:assignment, ...}` as a standalone expression — it is only handled inside block/let-sequencing (elaborator.ex:3633). So no guard shape reachable through the current dependent pipeline both type-checks as Bool and introduces a binding; the gap cannot be exercised today. If the dependent pipeline later gains standalone-assignment-as-expression support, this desugaring will silently under-scope such a guard — re-derive before relying on it.

## 2. The change

**Desugaring:** `pickup [g1->b1, g2->b2, ..., else->e]` becomes
```
{:conditional, [], [g1, b1,
  {:conditional, [], [g2, b2,
    ... e ...]}]}
```
i.e. `fold_right` over the non-terminal guard clauses with the terminator's body as the seed, each guard clause wrapping the accumulated else with `{:conditional, [], [guard, body, acc]}`. (The example above shows the `else`-terminated shape; see the full three-shape seed rule below — the terminator need not be a `pickup_else` node.)

**Where:** add a `{:pickup, _meta, clauses}` clause to the elaborator dispatchers that builds the nested conditional and delegates to the EXISTING conditional elaboration:
- `elaborate_expr_typed` (infer position, elaborator.ex near :466) — builds the chain, calls `elaborate_expr_typed` on it.
- `elaborate_expr_checked` (checked position, near :1024) — builds the chain, calls `elaborate_expr_checked` on it with the expected type.
- `elaborate_expr` (type-level position, :4735-4793) — **PINNED: do NOT add a type-level `:pickup` clause.** `elaborate_expr/3` has no clause for `:conditional` at all today — every arm is `:variable`/`:function_call`/`:record_update`/`:tuple`/`:literal`, and anything else (including `:conditional`) already falls through to the catch-all `{:error, {:unsupported_expression, other}}` at :4793. Since `pickup` desugars to `:conditional` (§2), and `:conditional` itself has zero type-position support in the dependent pipeline, a desugared `pickup` is transitively unsupported in type position with NO new code — the existing fallthrough already does the right thing. (Classic `checker.ex` has no separate type-level expression elaborator to consult either — confirmed by grep, no `elaborate_type`/type-expr function references `pickup` or `:conditional` — so there is no classic precedent to reconcile against.) This is stronger than "decide from the classic checker": it is a direct consequence of the dependent pipeline's existing `:conditional` coverage, independent of what classic ever did. No decision deferred to the executor.

A single shared private helper `desugar_pickup(clauses) :: {:conditional, ...} | expr | {:error, ...}` builds the chain, used by both value-position clauses (the bare `expr` case is the degenerate collapse below — the seed body returned unwrapped, not a special sentinel). It treats the LAST element of `clauses` as the seed and everything before it as wrappers, handling THREE shapes for the last element (matching classic codegen.ex:1461-1473 exactly):
- `{:pickup_else, _, [e]}` → seed = `e`.
- `{:pickup_clause, _, [{:literal, _, true}, e]}` (the trailing-`true` terminator form, §1) → seed = `e` (the guard is discarded — it is unconditionally true, so a wrapping conditional around it would be redundant; classic codegen does the same).
- anything else in last position → `{:error, {:pickup_missing_else, ...}}` (should be impossible post-parse; defensive).

Every non-last element MUST be `{:pickup_clause, _, [g, b]}` (parser guarantees this — a non-terminal `true`/`else` clause is only special in last position) and becomes a wrapper `{:conditional, [], [g, b, acc]}`. A single-clause pickup whose only clause is the seed (degenerate `pickup else -> e`, or its unlikely-but-parseable single-clause `pickup true -> e` sibling) desugars directly to the seed body with no conditional wrapper — this matches PICKUP §11's `pickup else -> e ≡ e` algebraic law and the printer's degenerate-collapse behavior (`pickup_test.exs:173-176`).

A `pickup` whose parse somehow lacks any valid terminator (should be impossible post-parse) returns `{:error, {:pickup_missing_else, ...}}` rather than crashing — defensive, ledgered as belt-and-suspenders.

**No kernel change. No emit change** (the desugared conditional lowers through the existing `bool_case`→`:case` emit path). Firewall stays green (elaborator-only, no classic reference).

## 3. Scope guard

- ONLY `pickup`. Do not touch conditional/match/bool_case internals.
- Diff confined to `lib/cure/elab/elaborator.ex` + new test file(s). `lib/cure/core/` EMPTY.
- The `pickup_clause`/`pickup_else` meta may carry positions used in error messages — thread them into the built conditional's meta if the conditional path surfaces them, but do NOT invent new diagnostics; a non-Bool guard or non-joining branches must surface the SAME error the conditional path already produces (verified against the oracle in §4).

## 4. Oracle + ratchet

**Behavioral oracle:** `test/cure/compiler/pickup_test.exs` (classic) pins the runtime selection/short-circuit semantics (§6.1-style tests: first-true wins, later guards unevaluated, trailing-`true` selection) and exercises E076/E077/E078 (parse-time terminator well-formedness) as triggered errors. It does NOT exercise W081/W082 as triggered warnings — the one diagnostics-catalogue test (lines 194-213) only asserts the codes are *registered and explainable* (`Errors.explain/1` returns text), not that compiling a pickup with an unreachable clause actually emits the warning. This is immaterial to Wave 1: §6 already excludes W081/W082 reproduction from scope, so the oracle's silence there matches the plan's own scope cut, not a gap in the plan. Wave 1's directed tests mirror the runtime-behavior pins (not the classic error CODES — the dependent path surfaces its own Bool-check/join errors; assert the ERROR HAPPENS on a non-Bool guard and on non-joining branches, and that a well-formed pickup evaluates to the correct branch, matching the classic runtime result). New test file `test/cure/elab/pickup_test.exs`:
- a 3-clause pickup with an `else` terminator selects each branch correctly at runtime (compile_and_load via the dependent pipeline, apply, compare to the expected value — mirror the classic pickup_test's runtime cases);
- a pickup using the trailing-`true ->` terminator form (§1's third clause shape, no `pickup_else` node) evaluates to the terminator's body when reached — exercises the `desugar_pickup` seed case that discards the guard (mirror `pickup_test.exs:137-148`, "trailing `true ->` clause is selected as the terminator");
- a pickup used in checked position (known expected type) elaborates;
- a non-Bool guard is rejected (error, any shape);
- non-joining branch types are rejected;
- (parser already covers missing-else; a directed parse-error assertion is optional, ledgered if included).

**Ratchet:** re-run the stdlib disposition script (roadmap §0). Wave 1 is expected to move NO module fully to KEEP by itself (every pickup-using std module also needs List/extern/lambda), but it MUST NOT regress the current KEEP set, and any module whose ONLY remaining blocker was pickup flips (per the gap matrix, none are pickup-only — so the expected delta is 0 modules, capability added). State the before/after count; a regression = STOP.

## 5. Gate

1. Red-first: each directed test written and shown failing (the reject cases fail as `:unsupported_expression` before the clause is added; the runtime-selection tests, both terminator shapes, fail to compile before).
2. Scoped `mix test test/cure/elab/pickup_test.exs test/cure/elab/` green; then full suite ONCE, 0 failures, arithmetic = baseline + new tests.
3. Firewall test green; disposition count not regressed.
4. Diff-scope: `lib/cure/core/` EMPTY; only elaborator.ex + the new test file touched.
5. Commit (ghost, explicit pathspecs): `feat(elab): pickup predicate-dispatch — desugar to nested conditional (value-surface Wave 1)`.

## 6. Out of scope

Everything else in the value-surface program (List, String, lambda-inference, extern, Map, tuples); any change to conditional/match/bool_case; W081/W082 pickup-specific WARNINGS (the classic redundant-clause/unreachable-else lints — if the dependent path doesn't reproduce them, that is acceptable degradation for Wave 1, ledgered as a possible follow-up, NOT built here).
