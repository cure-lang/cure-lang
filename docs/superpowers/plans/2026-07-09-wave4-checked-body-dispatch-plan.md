# Value-Surface Wave 4 — checked-mode body dispatch (`:list` + `:pickup`) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Add three whitelist clauses so `:list` and `:pickup` bodies route to CHECKED elaboration (`elaborate_expr_checked`), closing Finding A (bare-`[]` body / `[] -> []` arm → `{:unsolved_metavariables, :Nil}`) and the `:pickup`-body sibling (`Std.List.take`). Elaborator-only, no kernel change.

**Architecture:** `elaborate_body/6` (declarations.ex) and `elaborate_branch_body/5` (elaborator.ex) are per-node whitelists; non-whitelisted nodes fall to an infer-only catch-all that discards the expected type. Add `:list` to both and `:pickup` to `elaborate_body`, each delegating to the existing public `Elaborator.elaborate_expr_checked/5` (which already self-desugars `:list` and handles `:pickup` in checked position — so NO new desugar code).

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`); ExUnit.

## Global Constraints

- **Spec:** `docs/superpowers/specs/roadmap/2026-07-09-wave4-checked-body-dispatch-design.md` (hardened, commit `bbf05b5`). Read it FULLY first — esp. §1.2 (the pre-existing pinned test that MUST be flipped) and §3 (the `uncons`/`Tuple` blocker likely behind Finding A — `Std.List` may ADVANCE rather than flip; do not report "flipped" unless the disposition run shows it).
- **Two-pipeline steer:** dependent machinery is ONLY `lib/cure/elab/*` + `lib/cure/core/*`. `lib/cure/compiler/*` + `lib/cure/types/*` are the CLASSIC decoy — do not touch or consult.
- **Kernel-scope invariant (hard gate):** `lib/cure/core/*` stays EMPTY of changes. `git diff` under `core/` must be empty. If a `core/` change seems needed, STOP — the design broke.
- **Diff scope:** `lib/cure/elab/declarations.ex`, `lib/cure/elab/elaborator.ex`, the new test file `test/cure/elab/checked_body_dispatch_test.exs`, the §1.2 update to `test/cure/elab/list_test.exs` (ONE pinned assertion + stale moduledoc/comments), and a comment-only refresh in `test/cure/elab/pickup_test.exs` (see Anchors — a pre-existing comment there goes stale by this wave's own change). NO other file.
- **Line anchors drift** — re-verify EVERY clause head by identity (grep the function + the adjacent existing `:conditional`/`:tuple` clause) immediately before inserting.
- **Build lock FREE.** One `mix` at a time; scoped runs while iterating; full `mix test` exactly ONCE at the gate. No `iex -S mix`, no background mix.
- **Ghost commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, NO signature, NO trailers.
- **Explicit-pathspec staging ONLY:** `git add -- <path>`. NEVER `git add -A`/`.`/`-u`.
- **Tests immutable once green** — the ONE exception is the §1.2 `list_test.exs` pinned test, which this wave's own goal proves wrong (it asserted the bare-`[]` rejection was permanent). Every OTHER pre-existing test stays green untouched.

## Anchors (re-verify by identity before editing)

- `elaborate_body/6` whitelist — `declarations.ex`: clauses ~:287-399, infer-only catch-all ~:401-405 (`elaborate_expr_typed`, `return_core` discarded). `:conditional` clause (~:390) is the template — match its head arity/param order EXACTLY.
- `elaborate_branch_body/5` whitelist — `elaborator.ex`: clauses ~:3639-3685, catch-all ~:3687-3689. `:tuple` clause (~:3684) is the template.
- `elaborate_expr_checked/5` self-desugars `:list` (~:1092-1093) and handles `:pickup` (~:1084-1087 → checked conditional ~:1074). Confirm both exist — the "no new desugar code" claim rests on them.
- The pinned test to flip — `test/cure/elab/list_test.exs:30-32` + moduledoc :7-13 + comments :20-24, :100-102.
- A second stale comment this wave invalidates (found by grepping for "Finding A"/"elaborate_body whitelist" repo-wide) — `test/cure/elab/pickup_test.exs:71-78`'s test-explanation comment says a bare top-level `pickup` body is "always infer-mode"; after this wave it is checked-mode. Refresh this comment (no assertion changes — the test's behavior/expectations are unaffected, only the prose explaining *why* the nested-pickup case differs from a bare top-level one).

---

## Task 1: Add the three whitelist clauses + tests (incl. flipping the pinned ledger test)

**Deliverable:** `:list` and `:pickup` bodies elaborate in checked mode; the new antibodies + the flipped pinned test are green; no regression.

**Files:**
- Modify: `lib/cure/elab/declarations.ex` (`:list` + `:pickup` clauses in `elaborate_body/6`)
- Modify: `lib/cure/elab/elaborator.ex` (`:list` clause in `elaborate_branch_body/5`)
- Modify: `test/cure/elab/list_test.exs` (flip the §1.2 pinned assertion + refresh stale moduledoc/comments)
- Modify: `test/cure/elab/pickup_test.exs` (comment-only refresh, :71-78 — no assertion change)
- Test: `test/cure/elab/checked_body_dispatch_test.exs` (create)

- [ ] **Step 1: Write the new antibody tests (RED)** — create `test/cure/elab/checked_body_dispatch_test.exs`:

```elixir
defmodule Cure.Elab.CheckedBodyDispatchTest do
  @moduledoc """
  Wave 4: `:list` and `:pickup` function-body / match-arm-body nodes reach CHECKED
  elaboration (receive the declared return type), so a bare `[]` body / `[] -> []`
  arm / `:pickup`-with-`[]`-then-branch pins its element type from the goal instead
  of failing with `{:unsolved_metavariables, :Nil}`. Elaborator-only; closes the
  third-dispatch-layer gap ledgered since Wave 1.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a bare [] top-level body elaborates + runs" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD1", functions: [:e])
    assert apply(mod, :e, []) == []
  end

  test "a [] -> [] arm body elaborates + runs" do
    src =
      "mod M\n  fn f(xs: List(Int)) -> List(Int) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD2", functions: [:f])
    assert apply(mod, :f, [[]]) == []
    assert apply(mod, :f, [[1, 2, 3]]) == [2, 3]
  end

  test "a :pickup body with a bare-[] then-branch elaborates + runs (take shape)" do
    src =
      "mod M\n  fn g(n: Int) -> List(Int) =\n" <>
        "    pickup\n      n <= 0 -> []\n      else -> [n]\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD3", functions: [:g])
    assert apply(mod, :g, [0]) == []
    assert apply(mod, :g, [5]) == [5]
  end

  test "REGRESSION GUARD — head-bearing list body + inferrable pickup still work" do
    src =
      "mod M\n  fn h(x: Int, t: List(Int)) -> List(Int) = [x | t]\n" <>
        "  fn p(xs: List(Int)) -> List(Int) =\n" <>
        "    pickup\n      true -> xs\n      else -> xs\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD4", functions: [:h, :p])
    assert apply(mod, :h, [1, [2, 3]]) == [1, 2, 3]
    assert apply(mod, :p, [[9]]) == [9]
  end

  test "Std.List smoke — a real previously-blocked function (tail) elaborates + runs" do
    # Verbatim tail/2 from lib/std/list.cure (copy exactly as it stands; re-locate
    # by name, cite its line in a comment). Its [] -> [] arm was the blocker.
    src =
      @nat <>
        "  fn tail(xs: List(Nat)) -> List(Nat) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD5", functions: [:tail])
    assert apply(mod, :tail, [[]]) == []
    assert apply(mod, :tail, [[:Z, :Z]]) == [:Z]
  end
end
```

- [ ] **Step 2: Run — expect RED** (antibodies 1/2/3/5 fail `{:unsolved_metavariables, :Nil}`; the regression guard #4 already passes).

Run: `mix test test/cure/elab/checked_body_dispatch_test.exs`

- [ ] **Step 3: Add the `elaborate_body` clauses** (declarations.ex, alongside the `:conditional`/`:lambda` clauses ~:390-399, re-verified by identity). Match the existing `:conditional` clause head EXACTLY (arity/param order):

```elixir
  defp elaborate_body({:list, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  defp elaborate_body({:pickup, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
```

(If the real `:conditional` clause passes a differently-named/ordered arg to `elaborate_expr_checked`, copy that shape — do NOT invent the call; mirror the sibling.)

- [ ] **Step 4: Add the `elaborate_branch_body` clause** (elaborator.ex, alongside the `:tuple` clause ~:3684-3685, re-verified):

```elixir
  defp elaborate_branch_body({:list, _, _} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)
```

- [ ] **Step 5: Flip the pinned ledger test (§1.2)** — `test/cure/elab/list_test.exs:30-32`:

Change the assertion from `{:error, {:unsolved_metavariables, :Nil}}` to `{:ok, _}` (the bare-`[]` body now elaborates). Rename the test to reflect the new truth (e.g. `"a bare top-level [] body elaborates in checked mode (Wave 4)"`). Refresh the stale moduledoc (:7-13) and the inline comments (:20-24, :100-102) that describe the rejection as permanent / say "do NOT touch the elaborate_body whitelist" — those statements are now false. State in the commit body that this test encoded a since-superseded scope decision (not a bug), per the "test proven wrong by the wave's own goal" exception.

- [ ] **Step 6: Refresh the second stale comment (`pickup_test.exs`)** — `test/cure/elab/pickup_test.exs:71-78`'s comment on the "pickup nested as an `if`'s else-branch" test currently says a bare top-level `pickup` body is "always infer-mode; see the plan's Anchors section on elaborate_body/elaborate_branch_body". That is now false — a bare top-level `:pickup` body is checked-mode after Step 3. Update the comment to say the nested-pickup case and the (now also checked) bare top-level case both reach `elaborate_expr_checked`'s `:pickup` clause; the distinction this test still usefully exercises is that the nested pickup arrives via the *outer* `:conditional`'s checked branches (elaborator.ex:1074-1080) rather than via `elaborate_body`'s own `:pickup` clause. No assertion changes — this test's behavior is untouched, only the prose is stale.

- [ ] **Step 7: Run — expect GREEN**

Run: `mix test test/cure/elab/checked_body_dispatch_test.exs test/cure/elab/list_test.exs test/cure/elab/pickup_test.exs`
Expected: all pass (new antibodies green; the flipped pinned test green; the rest of list_test and all of pickup_test still green — pickup_test's edit is comment-only).

- [ ] **Step 8: Commit**

```bash
git -C <worktree> add -- lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex \
  test/cure/elab/checked_body_dispatch_test.exs test/cure/elab/list_test.exs \
  test/cure/elab/pickup_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): checked-mode body dispatch for :list and :pickup bodies (Finding A + sibling; value-surface Wave 4)" \
  -- lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex \
  test/cure/elab/checked_body_dispatch_test.exs test/cure/elab/list_test.exs \
  test/cure/elab/pickup_test.exs
```

---

## Task 2: Gate — firewall, core-scope, ratchet cascade map, oracle, full suite

**Deliverable:** the wave is proven additive and green, with the honest disposition/cascade map.

- [ ] **Step 1: Firewall + core-scope.** `mix test test/cure/dependent_pipeline_firewall_test.exs` green. `git -C <worktree> diff --stat` shows NO change under `lib/cure/core/`; full diff = declarations.ex, elaborator.ex, and the three test files (the new `checked_body_dispatch_test.exs`, plus the comment/assertion refreshes in `list_test.exs` and `pickup_test.exs`). If any `core/` file changed, STOP.

- [ ] **Step 2: Ratchet (the deliverable) — honest disposition map.** Re-run the stdlib disposition script. Record before/after value-surface KEEP. **Do NOT assume `Std.List` flips** — per spec §3 it likely ADVANCES to `uncons`/`split_first`'s `Tuple`-return-type gap (`{:unsupported_expression, _}` on the `:tuple` body, a pre-existing unrelated issue = the operator's unified-tuple initiative). Report `Std.List`'s ACTUAL post-wave status: flipped, or advanced-to-`uncons`-Tuple, or another blocker — named concretely. For every module that moved (flipped OR advanced), state its new status/blocker. A regression in the prior KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector/math) = STOP.

- [ ] **Step 3: Oracle replay.** `mix test test/oracle_replay_test.exs` — live `N/N`, no verdict flipped.

- [ ] **Step 4: Full suite ONCE.** Capture the LIVE baseline BEFORE Task 1 (or from the last green run). `mix test` — 0 failures, total = baseline + the 5 new antibodies (the flipped list_test test is a modify, not an add, so no net count change from it). Any unrelated pre-existing failure you did not cause → STOP and report.

- [ ] **Step 5: Report.** Commit SHA + red→green evidence (the 4 failing-then-passing antibodies + the flipped ledger test); the three clause insertions (with re-verified line numbers); firewall + core-scope result; the disposition/cascade map (Std.List's real status + any module that moved + its new blocker); oracle `N/N`; full-suite baseline→final. Honest generality statement: Finding A + the `:pickup` sibling are closed program-wide; `Std.List`'s flip (and the cascade) remains gated on the `uncons`/`Tuple` gap if the disposition run shows it advancing rather than flipping.

---

## Out of scope (do NOT build here)

- `:pickup` in `elaborate_branch_body` (no failing arm-body test demands it).
- `uncons`/`split_first`'s `Tuple`-typed `%[...]` bodies (the pre-existing `:tuple`/`Tuple` gap = unified-tuple initiative) — a separate wave.
- The dependents' own blockers (atom/string literals, map's `:get`, non_empty's index_mismatch).
- Any kernel change; any change to `elaborate_expr_checked`, `desugar_list`, pickup/conditional desugaring, or existing whitelist clauses.
