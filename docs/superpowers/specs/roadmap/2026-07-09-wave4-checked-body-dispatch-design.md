# Value-Surface Wave 4 — checked-mode body dispatch for `:list` and `:pickup` bodies (Finding A + sibling)

**Goal:** Route `:list` and `:pickup` function-body / match-arm-body nodes to CHECKED elaboration (so they receive the declared return type) instead of the infer-only catch-all. This closes "Finding A" (bare-`[]` body → `{:unsolved_metavariables, :Nil}`) and its sibling (a `:pickup` body whose then-branch is bare `[]`). This is expected — but NOT confirmed by this design (see §3) — to flip `Std.List` to KEEP and unblock its ~20-dependent cascade; source tracing during review found a further, unrelated `Std.List` gap (`uncons`/`split_first`'s `Tuple` return type, §3) sitting immediately downstream, so the flip must be verified by the executor's disposition run, not assumed. Elaborator-only; no kernel change.

**Status of the program:** Waves 1–3 (`pickup`, `List`, `@extern`) + the Std lowercase/classic-bridge all landed on `autopilot/kernel-parity-batch` (unmerged). `Std.List`'s remaining blockers found by static inspection up to the point elaboration currently halts are exactly the two dispatch clauses this wave adds — but elaboration halts at the FIRST failing function (§3), so this does not rule out a further blocker later in the file (one is now known: see §3).

---

## 0. The gap — the "third-dispatch-layer" whitelist (dependent-pipeline-verified)

A function body does not reach `elaborate_expr_checked`/`elaborate_expr_typed` directly. It is dispatched through a per-node-type WHITELIST; whitelisted nodes get CHECKED mode (receive the return/expected core type), non-whitelisted nodes fall to a generic INFER-ONLY catch-all that DISCARDS the expected type. There are two such whitelists:

### 0.1 `elaborate_body/6` (top-level function body) — `declarations.ex`
Whitelisted → checked: `:pattern_match` (:287), `:with_abs` (:295), `:rewrite_expr` (:300), `:function_call` (:304, ctor/`reflexive` → checked, else infer-retry-checked), `:tuple` (:346), `:hole` (:378), `:block` (:384), `:conditional` (:390), `:lambda` (:397). **Catch-all (:401-405)** → `Elaborator.elaborate_expr_typed/4`, infer-only, `return_core` discarded.
**Missing: `:list` and `:pickup`.** A `{:list,…}` or `{:pickup,…}` body falls to :401 → infer-only.

### 0.2 `elaborate_branch_body/5` (match-arm body) — `elaborator.ex`
Whitelisted → checked: `:rewrite_expr` (:3639), `:pattern_match` (:3644), `:with_abs` (:3650), `:function_call` (:3653, ctor infer-retry-checked), `:tuple` (:3684). **Catch-all (:3687-3689)** → `elaborate_expr_typed`, infer-only, `expected` discarded.
**Missing: `:list`.** A `[] -> []` arm body `{:list,[],[]}` falls to :3687 → infer-only. (The `expected` type IS available here — it's `branch_expected = refine_branch_goal(result_type_term, …)`, elaborator.ex:3412-3413/3429 — so the machinery is present; only the clause is missing.)

### 0.3 Why infer-only fails for an empty list
`[]` desugars to `Nil()` (a ctor call whose element-type parameter is a metavariable). With no expected type, that metavariable is never pinned → `{:unsolved_metavariables, :Nil}`. A head-bearing list `[h | t]` infers fine (`h` pins the element type); only bare `[]` (and a `:pickup`/`:conditional` whose first-elaborated branch is bare `[]`) fails.

### 0.4 The two concrete `Std.List` blockers
- **`:list` arm bodies** — `tail` (`[] -> []`, list.cure:72), `concat` (:95), `map` (:112), `filter` (:118), `zip_with` (:147,150), `take_rest` (:173), `drop_rest` (:185): each has a bare-`[]` arm body hitting §0.2's catch-all. (`filter`'s bare-`[]` arm at :118 was missed by the scout's original enumeration — same class, same fix, no additional clause needed.)
- **`:pickup` body — `take` (list.cure:165-168)**:
  ```
  fn take(list: List(t), n: Int) -> List(t) =
    pickup
      n <= 0 -> []
      else   -> take_rest(list, n)
  ```
  Its top-level body is `{:pickup,…}`, absent from §0.1's whitelist → catch-all infer-only. `pickup` desugars to a right-nested `:conditional` with the first clause as the then-branch; the infer-mode conditional (elaborator.ex:466-472) elaborates the then-branch (`[]`) FIRST with no expected type → `{:unsolved_metavariables, :Nil}`, before the else-branch is reached. (`drop` escapes only because its then-branch is a var, not `[]`.)

## 1. Design (decided) — add the missing whitelist clauses, route to checked

Three clauses, each routing to the existing public `Elaborator.elaborate_expr_checked/5`, symmetric with the existing `:block`/`:conditional`/`:tuple` clauses. `elaborate_expr_checked` ALREADY self-desugars `:list` (elaborator.ex:1092-1093, `desugar_list(node)` re-checked against `expected_core`) and ALREADY handles `:pickup` in checked position (elaborator.ex:1084-1087 → checked conditional at :1074, both branches checked against the goal). So NO new desugar code is needed — only the dispatch clauses.

1. **`elaborate_body` `:list` clause** (declarations.ex, alongside :384-399):
   `defp elaborate_body({:list, _, _} = expr, return_core, scope, ctx, env, _params), do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)`
2. **`elaborate_body` `:pickup` clause** (same location):
   `defp elaborate_body({:pickup, _, _} = expr, return_core, scope, ctx, env, _params), do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)`
   (Re-verify the exact `elaborate_body/6` head arity/param order against the existing `:conditional` clause — match it exactly.)
3. **`elaborate_branch_body` `:list` clause** (elaborator.ex, alongside :3684-3685):
   `defp elaborate_branch_body({:list, _, _} = expr, expected, names, ctx, env), do: elaborate_expr_checked(expr, expected, names, ctx, env)`

**Scope decision (red-test discipline):** add ONLY what a failing `Std.List` function demands: `:list` in both whitelists, `:pickup` in `elaborate_body`. Do NOT speculatively add `:pickup` to `elaborate_branch_body` — the scout found no failing `:pickup` arm body (`filter`/`nth`/`contains`/`find`/`any`/`all`/`count` have `:pickup` arm bodies but their then-branches are inferrable, so they already pass). If a future test demands it, it is the identical one-line addition; note this in the spec, do not build it now.

All line anchors drift — the executor MUST re-verify each clause head by identity (grep the function + the adjacent `:conditional`/`:tuple` clause) before inserting.

### 1.1 What must NOT change
- The kernel proper — `lib/cure/core/*` — stays EMPTY of changes. An empty list reaching checked mode is a normal ctor check the kernel already performs (`elaborate_ctor_app`/`_bidirectional` + `Kernel.check`, elaborator.ex:905-926).
- No change to `elaborate_expr_checked` itself, to `desugar_list/1`, or to the pickup/conditional desugaring — only the two dispatchers gain clauses.
- Do NOT remove or reorder existing whitelist clauses.

### 1.2 A pre-existing pinned test must be updated (not new scope — a consequence of this wave)
`test/cure/elab/list_test.exs:30-32` currently asserts the OLD, soon-to-be-wrong behavior:
```
test "a bare top-level [] body is infer-only-rejected (ledger guard, NOT a crash)" do
  src = "mod M\n  fn e() -> List(Int) = []\nend\n"
  assert {:error, {:unsolved_metavariables, :Nil}} = Program.elaborate(src)
end
```
This is the EXACT antibody-1 shape (§2, item 1) — this wave makes it succeed. Left as-is, this pinned test fails post-change and the §4 gate ("0 failures, total = live baseline + new tests") is unreachable. The executor MUST, as part of this change:
- Flip this test's assertion to `{:ok, _}` (per the "test is proven wrong by the wave's own goal" exception — the test encoded a since-superseded scope decision, not a bug; state this explicitly in the commit/diff).
- Update the module's `@moduledoc` (list_test.exs:7-13) and the inline comments at :20-24 and :100-102, which describe the rejection as permanent/pinned ("do NOT touch the elaborate_body whitelist") — these go stale the moment this wave lands.
This is the one pre-existing test this wave is expected to touch; every other pre-existing test must stay green untouched. This action item is also gated explicitly in §4 step 1.

## 2. Antibodies / tests

New test file `test/cure/elab/checked_body_dispatch_test.exs` (harness like `list_test.exs`: `Program.elaborate` → `Emit.compile_and_load` → `apply`). Behavioral:

1. **Bare `[]` top-level body elaborates + runs.** `fn e() -> List(Int) = []` → `{:ok, _}` (RED today: `{:unsolved_metavariables, :Nil}`), and `apply(e, []) == []`. (This is the exact form Wave 2 ledgered as out of scope — it now works.)
2. **`[] -> []` arm body elaborates + runs.** A `match` function with a `[] -> []` arm (and a `[h|t] -> …` arm) elaborates and, applied to `[]`, returns `[]`. RED today via the arm-body catch-all.
3. **`:pickup` body with a bare-`[]` then-branch elaborates + runs (the `take` shape).** `fn f(n: Int) -> List(Int) = pickup n <= 0 -> []; else -> [n]` (or the real `take` shape) elaborates and selects correctly: `f(0) == []`, `f(1) == [1]` (or the take semantics). RED today: `{:unsolved_metavariables, :Nil}`.
4. **Regression guard — head-bearing list bodies and inferrable pickups still work.** A `[h | t]` body and a `:pickup` whose then-branch is a var still elaborate + run (these already passed via infer-only; the new checked routing must not break them). This pins that adding the clauses does not regress the currently-passing cases.
5. **`Std.List` smoke — a real previously-blocked function.** Inline the VERBATIM body of a real `Std.List` function that was blocked (e.g. `tail` with its `[] -> []` arm, or `take`) into a test-local module and assert it elaborates + runs (`tail([1,2,3]) == [2,3]`, `tail([]) == []`). Copy the function text exactly from `lib/std/list.cure`.

Red-first: each shown failing before the change (antibodies 1-3,5 fail with `{:unsolved_metavariables, :Nil}`; antibody 4 passes both before and after — it's the regression guard).

## 3. Ratchet + firewall gate

- **Firewall:** `test/cure/dependent_pipeline_firewall_test.exs` MUST stay green (the change is elab-only, references no classic module).
- **Core untouched:** `git diff` shows NO change under `lib/cure/core/`. Diff limited to `lib/cure/elab/declarations.ex`, `lib/cure/elab/elaborator.ex`, the new test file, and the §1.2 update to `test/cure/elab/list_test.exs` (its one pinned assertion + stale moduledoc/comments) — no other file changes.
- **Ratchet — the headline:** re-run the stdlib disposition script. **`Std.List` is HOPED to flip to KEEP but this is NOT verified by this review and there is source-level reason to doubt it**: `uncons` (list.cure:229) and `split_first` (list.cure:235) declare return type `Tuple`, an identifier that is never declared anywhere as an inductive family (no `type Tuple = …` exists in the tree). `Tuple` resolves via `idx_to_core`/`resolve_index_name` (declarations.ex:886-897,1074-1105) to a bare `{:global, :Tuple}` — not the real Sigma family (`:Sigma`, core/inductive.ex:230). Their `%[h,t]`/`%[[],[]]` arm bodies hit the PRE-EXISTING, untouched `:tuple` branch-body clause (elaborator.ex:3684-3685); `elaborate_expr_checked`'s `:tuple` clause (1030-1053) only special-cases a Sigma-family match, so this falls to `elaborate_expr_checked_fallback` (1117-1131), which — finding no metavariable to reject up front — tries INFER mode on the `:tuple` node. `elaborate_expr_typed` has NO `:tuple` clause anywhere in the file (confirmed exhaustively) and hits the universal catch-all `{:error, {:unsupported_expression, _}}` (elaborator.ex:569). Because `Program.elaborate_declarations`'s `body_pass` (program.ex:760-767) is an `Enum.reduce_while` that halts at the FIRST function body to fail, and `uncons` sits at line 229 — strictly after every function this wave fixes (the last is `all`, list.cure:218-224) — landing this wave's clauses will let elaboration progress past the current blockers and immediately hit `uncons`'s (unrelated, pre-existing) `Tuple`/`:tuple`-infer gap. **The likely real outcome is that `Std.List` ADVANCES to a new blocker rather than flipping to KEEP.** Do not report "flipped to KEEP" as fact until the executor's disposition run actually shows it; if it does not flip, that is not a wave-4 regression — name `uncons`'s `Tuple` return-type gap as the concrete next blocker in the cascade map, the same way any other dependent's own blocker is named. With `Std.List` elaborating (if it does), its ~20 dependents (`app`/`crdt`/`gen`/`json`/`functor`/`iter`/`map`/`set`/`string`/`vector`/`test`/`pair`/`non_empty`/…) are no longer gated on it — each flips IF it has no OTHER blocker of its own. **State the actual before/after value-surface KEEP set and, for each dependent that did NOT flip, its own next blocker named concretely** (this is the deliverable that sequences the remaining waves). The scout's expectation is `Std.List` + any dependent whose sole blocker was `List`; be honest about the real cascade size — most dependents likely have their own value-form blockers (atom/string literals) and will advance rather than flip. A regression in the prior KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector/math) = STOP.
- **Oracle replay:** `mix test test/oracle_replay_test.exs` — live `N/N`, no verdict flipped (additive).

## 4. Gate

1. Red-first: every directed test (except the regression guard) shown failing before the change. Update the pinned `list_test.exs:30-32` test (§1.2) — flip its assertion to `{:ok, _}` and refresh its stale moduledoc/comments — as part of this same step, not a follow-up.
2. Scoped `mix test test/cure/elab/checked_body_dispatch_test.exs` green; then the full suite ONCE (build lock free), 0 failures, total = live baseline + new tests. Capture the LIVE baseline before the change — do NOT hardcode.
3. Firewall green; `core/` diff EMPTY; disposition reported (the cascade map); oracle replay live `N/N`.
4. Commit(s), ghost author (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no trailers/signature), explicit pathspecs. One coherent commit is fine (the three clauses + the new test file + the §1.2 `list_test.exs` update); or split body-whitelist / arm-whitelist. Each commit independently pre-existing-suite-green.

## 5. Out of scope (do NOT build here)

- `:pickup` in `elaborate_branch_body` (no failing arm-body test demands it — identical one-line addition when one does).
- Any OTHER infer-only value form (add per red test, per the standing discipline).
- The dependents' OWN blockers (atom literals → system/test; string literals+`<>` → io/string; `map`'s `:get` extern-metavar; `non_empty`'s index_mismatch) — separate waves, sequenced by this wave's cascade map.
- `Std.List`'s OWN next blocker if it doesn't fully flip: `uncons`/`split_first`'s `Tuple`-typed `%[...]` bodies (§3) — a pre-existing, unrelated `:tuple`/`Tuple` gap, not a `:list`/`:pickup` dispatch issue; a separate wave, sequenced by this wave's disposition-run findings.
- Any kernel change; any change to `elaborate_expr_checked`, `desugar_list`, pickup/conditional desugaring, or existing whitelist clauses.
