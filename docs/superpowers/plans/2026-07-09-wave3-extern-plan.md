# Value-Surface Wave 3 — `@extern` / FFI — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Let a bodyless `@extern(:mod, :fn, arity)` function declaration elaborate through the DEPENDENT pipeline (as a typed opaque FFI postulate) and emit a direct Erlang remote call. No kernel CODE change.

**Architecture:** Two changes plus one safety filter, all E/C-layer. (1) `declarations.ex`: when a function decl carries `meta[:extern]`, skip body elaboration and mark the def with an extern sentinel (the Π is already computed from the signature). (2) `emit.ex`: recognize the sentinel and emit a remote-call wrapper (`mod:fun(V0..Vn-1)`) with params synthesized from the arity, patched at the SINGLE choke point every emit entry (`compile_and_load/2`, `compile_forms/2`, `compile_forms/3`) already shares — `function_form/2` (called only from `module_forms/3`) — so one patch fixes all three; see Task 2 Step 4 for why the line-60 all-defs filter itself must NOT change. (3) `totality_closure.ex`: filter extern-marked globals out of `certify_type_level/1` so a type-level-reachable extern is never handed to `Kernel.check` (the spec §2.1-point-4 hole). The kernel (`lib/cure/core/*` except nothing) is untouched — the extern is an opaque neutral it already knows how to not-unfold.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + emit (`lib/cure/elab/emit.ex`); ExUnit.

## Global Constraints

- **Spec:** `docs/superpowers/specs/roadmap/2026-07-09-wave3-extern-design.md` (hardened, commit `4eb14dd`). Read it FULLY first — especially §2.1 (marker contract + the TotalityClosure consumer), §2.2 (emit param synthesis), §4 (Claim A/B trust framing). This plan implements it exactly.
- **Two-pipeline steer:** the dependent machinery is ONLY `lib/cure/elab/*` + `lib/cure/core/*` + `emit.ex`. `lib/cure/compiler/*` (`codegen.ex`) and `lib/cure/types/*` are the CLASSIC decoy — read `codegen.ex`'s `compile_extern_function` ONLY as the behavioral oracle for the target BEAM form; NEVER call it or import it.
- **Kernel-scope invariant (hard gate):** `lib/cure/core/{eval,normalise,conv,quote,kernel,term,erase,inductive,builtins}.ex` stay EMPTY of changes. `git diff` under `core/` must be empty. If you find yourself needing to edit any `core/` file, STOP and report — the design broke.
- **Diff scope:** `lib/cure/elab/declarations.ex`, `lib/cure/elab/emit.ex`, `lib/cure/elab/totality_closure.ex`, the new test file, and `lib/cure/elab/elaborator.ex` ONLY if marker plumbing forces it. NOT `lib/std/*.cure` (the std modules already carry their `@extern` decls; this wave makes them elaborate).
- **Line anchors drift** — this file has same-day churn. Re-verify every cited line by CLAUSE IDENTITY (grep the function/pattern) immediately before editing; the spec itself flags `elaborator.ex:569` and others as drift-prone.
- **Build lock is FREE** (#22/Wave-1/Wave-2 landed). Still: only ONE `mix` at a time (a past concurrent run panicked the kernel). Prefer scoped `mix test <file>`; full suite exactly ONCE at the gate. No `iex -S mix`, no background mix.
- **Ghost commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, NO signature, NO trailers.
- **Explicit-pathspec staging ONLY:** `git add -- <path>` / `git commit -m "..." -- <path>`. NEVER `git add -A`/`.`/`-u`.
- **Tests immutable once green**, behavioral not implementation-coupled. Strict red-green.

## Anchors verified against source (per hardened spec; re-verify by identity before editing)

- Parse: `@extern` decorator → `meta[:extern] = {mod,fun,arity}` (`parser.ex:4757-4774`, extract `:4781-4800`); bodyless `fn` → `body = []` (`parser.ex:2398-2402`).
- Dispatch: `Declarations.elaborate/2` → `register_signature` (succeeds, stores body `{:hole, "__pending__"}`, `declarations.ex:36-40`, `function_signature/2` `:76-101`) → `elaborate_function_body` (`declarations.ex:45-71`) → `single_body([])` fallthrough (`:264-265`) → `elaborate_body([])` catch-all (`:383-387`) → `Elaborator.elaborate_expr_typed([], …)` catch-all `{:unsupported_expression, other}` (`elaborator.ex:569`).
- Emit: body-less filter `emit.ex:55-63` (line 60 `is_nil(Map.get(d, :builtin_op))`); `/3` live path with `local_defs` `emit.ex:71-80`; `reject_holes` `emit.ex:104-116` (rejects `{:hole,_}` only); `function_form` `emit.ex:125-139` (reads `%{body: body}` + `Erase.erase`); `V<pos>` naming precedent `peel_params/4` `emit.ex:141-150` (peels a `{:lam,…}` chain — do NOT reuse for externs); `present_arity/2` `emit.ex:367-372`; call-site value lowering `emit.ex:354-365`.
- Classic oracle (READ-ONLY): `codegen.ex` `compile_extern_function` `:643-645`, wrapper form `:691-705`, `build_param_forms/3` `:698`.
- TotalityClosure: `certify_type_level/1` `totality_closure.ex:34-45` (the filter site); `type_level_fns/1` `:22-27`; `seed_globals/1` `:49-59`; `close/3` `:64-75`; `collect/1` `:79-92`. Invoked from `Program.check_ast_elixir_core` (`program.ex:137,:517,:633`). `Kernel.validate_certificate/2` `kernel.ex:369-385` → `check_def/2` `:308-330` (builtin_op clause `:319-320`, generic body clause `:322-329`).
- Kernel opaque-neutral handling (why no kernel change): `eval.ex:11-12,41,49`; `conv.ex:10-18,118,153`.

## Marker representation (DECIDED for this plan)

Replace the pending `{:hole, "__pending__"}` def body with the sentinel **`{:extern, {mod, fun, arity}}`**. Rationale: (1) it is NOT a `{:hole,_}`, so `reject_holes` passes it; (2) every consumer (emit routing, totality-closure filter) matches it by `match?({:extern, _}, body)` — a single-point marker, no overloaded field; (3) it explicitly does NOT reuse `builtin_op` (overloaded by 3 arithmetic-op consumers — spec §2.1). If the executor finds a def-struct constraint that makes a named field (`extern:`) cleaner, that is an acceptable substitution PROVIDED all four contract points (skip check, non-hole, emit-routable, totality-closure-filterable) hold and antibodies 2 + 7 pass.

---

## Task 1: Elaborator accepts a bodyless extern + TotalityClosure skips it

**Deliverable:** an `@extern` decl elaborates `{:ok, _}` with its declared Π retained, and a type-level-reachable extern does not crash `TotalityClosure`. (Runtime/emit is Task 2 — these tests assert elaboration only.)

**Files:**
- Modify: `lib/cure/elab/declarations.ex` (extern branch in `elaborate_function_body`)
- Modify: `lib/cure/elab/totality_closure.ex` (filter externs in `certify_type_level/1`)
- Test: `test/cure/elab/extern_test.exs` (create)

- [ ] **Step 1: Write the elaboration-acceptance test (RED) — antibody 1**

```elixir
defmodule Cure.Elab.ExternTest do
  @moduledoc """
  `@extern(:mod, :fn, arity)` FFI in the dependent pipeline (Wave 3). A bodyless
  extern is a typed opaque postulate: its declared Π is asserted (an FFI axiom,
  not kernel-proven — see spec §4 Claim B), it stays an opaque neutral in the
  kernel, and emit lowers it to a direct Erlang remote call. Kernel untouched.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}
  alias Cure.Core.Env

  test "a bodyless @extern declaration elaborates" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "the elaborated extern retains its declared arrow type (signature not discarded)" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    # The registered global exists and is a Pi (List(Int) -> Int), not a hole/error.
    # The behavioral contract: a def named `length` exists with a Pi type whose
    # codomain is Int. Pin at least that the def is present and not {:hole,_}.
    def_entry = extern_def!(env, :length)
    refute match?({:hole, _}, Map.get(def_entry, :body))
    assert Map.get(def_entry, :type) != nil
  end

  # `Cure.Core.Env.get_def/2` (verified: defined at `inductive.ex:1-140`'s
  # `defmodule Cure.Core.Env`, a SEPARATE module from `Cure.Core.Inductive`
  # at `:142-433` in the same file — `Inductive` has no `get_def/2`). This is
  # the accessor every other elab module (`declarations.ex`, `emit.ex`,
  # `totality_closure.ex`) already uses; re-verify by identity before relying
  # on it, per the plan's line-anchor-drift caveat.
  defp extern_def!(env, name), do: Env.get_def(env, name) || flunk("no def #{name}")
end
```

- [ ] **Step 2: Run — expect RED**

Run: `mix test test/cure/elab/extern_test.exs`
Expected: FAIL — `Program.elaborate` returns `{:error, {:unsupported_expression, []}}` (the extern's empty body hits `elaborator.ex:569`).

- [ ] **Step 3: Add the extern branch in `elaborate_function_body`**

In `declarations.ex`, `elaborate_function_body` (`:45-71`, re-verify by identity), add an EARLY branch — before the `single_body`/`elaborate_body` dispatch — that fires when the function's `meta[:extern]` is a `{mod, fun, arity}` triple:

```elixir
# Wave-3: a bodyless @extern is a typed FFI postulate — the signature IS the
# type; there is no term to elaborate/check. Mark the def with an extern
# sentinel (NOT a hole, so emit.reject_holes passes; NOT builtin_op, which is
# overloaded). emit lowers it to a remote call; TotalityClosure skips it.
case Keyword.get(meta, :extern) do
  {mod, fun, arity} when is_atom(mod) and is_atom(fun) and is_integer(arity) ->
    # Replace the pending placeholder body with the extern sentinel; do NOT call
    # elaborate_body / Kernel.check / Relevance.check (no term exists).
    {:ok, mark_extern_def(env, name, {mod, fun, arity})}
  _ ->
    # ... existing body-elaboration path unchanged ...
end
```

Implement `mark_extern_def/3` to set the already-registered def's body to `{:extern, {mod, fun, arity}}` (leaving its Π `type` intact). Use the real Env update function (discover it — likely `Env.add_def`/an update helper; the def was registered by `register_signature`, so this REPLACES its body). Do NOT create a second def. If `meta[:extern]` is present but NOT a clean 3-tuple (malformed decorator, spec §1.1), fall through to the normal path (out of scope; no std decl triggers it).

- [ ] **Step 4: Run antibody 1 — expect GREEN (elaboration)**

Run: `mix test test/cure/elab/extern_test.exs`
Expected: both tests PASS — the extern elaborates and its def is present, non-hole, Pi-typed.

- [ ] **Step 5: Write the TotalityClosure test (RED) — antibody 7**

A surface fixture where an extern IS type-level-reachable **is constructible** —
do not default to a mechanism-guard placeholder. `declarations.ex:63`'s own
comment documents the precedent this fixture mirrors: a computed (non-ctor)
index expression calling an ordinary global function, e.g. `plus` in
`Vec(a, plus(m,n))` (also exercised by the `plus(m, ...)`-shaped oracle
fixtures under `test/oracle/rewrite/`). `idx_to_core`'s function-call clause
(`declarations.ex:881-942`) lowers a non-family, non-ctor call to a bare
`{:global, atom}` app with NO existence check against `env`, and the two-pass
elaborator (`program.ex:700-737`) registers every function's Π **before** any
family/ctor is elaborated within the same `register_pass`, then marks every
extern body only in the later `body_pass` — which completes, for every
function, before `TotalityClosure.certify_type_level` ever runs
(`program.ex:136-137`). So: declare an extern that returns `Nat` (not `Int` —
the index position needs a `Nat`-typed expression to type-check), then declare
an indexed family whose constructor's result index calls that extern directly
(not inside another ctor), e.g. (verify exact surface syntax against
`dependent_construction_test.exs`'s `@vec` fixture and adjust):

```elixir
  alias Cure.Elab.TotalityClosure

  test "TotalityClosure does not certify an extern-marked global reached from a type-level index" do
    src =
      "mod M\n" <>
        "  type Nat = Z | S(Nat)\n" <>
        "  @extern(:erlang, :abs, 1)\n  fn extlen(x: Nat) -> Nat\n" <>
        "  type Boxed indices (n: Nat)\n" <>
        "    mk : Boxed(extlen(Z()))\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)

    # Reachability, not just absence-of-crash (falsifiability): :extlen must
    # actually be in the type-level closure, or this test would pass vacuously.
    assert MapSet.member?(TotalityClosure.type_level_fns(env), :extlen)

    # The mechanism itself: re-running certify_type_level must still succeed
    # (not {:error, {:totality_required, :extlen}}) — an extern has no body to
    # certify, so it must be skipped, never submitted to Kernel.validate_certificate.
    assert {:ok, _} = TotalityClosure.certify_type_level(env)
  end
```

(The sketch above is illustrative, not literal — the implementer must get the
concrete surface syntax and index-position expression to actually parse/elaborate,
verifying against `dependent_construction_test.exs`'s `indices (n: Nat)` /
`mk : Boxed(...)` shape, and MUST assert `:extlen ∈ type_level_fns(env)` — proving
real reachability — before asserting the filter's effect. If, after an honest
attempt at this exact recipe, no surface form of it actually parses/elaborates in
current Cure syntax, that failure (with the concrete parse/elaborate error) is
itself the evidence needed to fall back — and the fallback MUST be this
concretely-specified direct unit test, not an open-ended "discover something":
construct an `Env.t()` directly via `Env.add_def/5` (extern def, body
`{:extern, {:erlang,:abs,1}}`) plus `Inductive.declare/3` for a family whose
ctor `result_indices` contains `{:app, {:global, :extlen}, ...}` (mirroring
`seed_globals`'s `from_ctors` walk, `totality_closure.ex:53-56`), assert
`:extlen` ∈ `TotalityClosure.type_level_fns(env)` (reachability, RED before the
filter — `certify_type_level(env)` returns `{:error, {:totality_required, :extlen}}`
or crashes inside `Kernel.check_def`), then GREEN after Step 6's filter:
`certify_type_level(env) == {:ok, _}` AND `:extlen` was never passed to
`Kernel.validate_certificate` (assert via the returned env's `certified` set
NOT containing `:extlen`, since an extern is by design never certified).
Whichever fixture is used, it must proceed by first showing genuine RED
(the pre-filter crash/rejection), never a same-test tautology.

- [ ] **Step 6: Add the filter in `certify_type_level/1`**

In `totality_closure.ex`, `certify_type_level/1` (`:34-45`), skip extern-marked globals before submitting to `Kernel.validate_certificate/2`. Filter names whose def body is `{:extern, _}` out of the `type_level_fns(env)` list (or `:cont`-skip inside the `Enum.reduce_while`):

```elixir
# Wave-3: an @extern global has no Core body to certify (it is an asserted FFI
# postulate — spec §2.1 point 4). Certification is a category error for it, so
# skip it here rather than hand its sentinel body to Kernel.check.
```

Do the skip in `certify_type_level/1`, NOT `close/3` (a directly-seeded name never traverses `close/3`'s `get_def` branch — spec §2.1). Zero `core/` change.

- [ ] **Step 7: Run — expect GREEN**

Run: `mix test test/cure/elab/extern_test.exs`
Expected: all Task-1 tests pass.

- [ ] **Step 8: Commit (C1)**

```bash
git -C <worktree> add -- lib/cure/elab/declarations.ex lib/cure/elab/totality_closure.ex
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): accept bodyless @extern as typed FFI postulate; TotalityClosure skips it (value-surface Wave 3)" \
  -- lib/cure/elab/declarations.ex lib/cure/elab/totality_closure.ex
```

(Do NOT commit the test file yet — it goes green fully only after Task 2's emit lands, per §6 gate item 4. Keep the red-before-each-step demonstration as local runs.)

---

## Task 2: Native remote-call emit for externs

**Deliverable:** an `@extern` function compiles+loads and, applied, issues the real Erlang remote call.

**Files:**
- Modify: `lib/cure/elab/emit.ex` (extern recognition + remote-call wrapper + filter widen)
- Test: `test/cure/elab/extern_test.exs` (extend with runtime asserts)

- [ ] **Step 1: Add runtime asserts (RED) — antibodies 2, 3, 4**

```elixir
  test "an @extern typechecks AND ships — issues the real remote call" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern1", functions: [:length])
    assert apply(mod, :length, [[1, 2, 3]]) == 3
  end

  test "a 0-arity and a 2-arity extern both wire params correctly" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :max, 2)\n  fn imax(a: Int, b: Int) -> Int\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern2", functions: [:imax])
    assert apply(mod, :imax, [3, 7]) == 7

    src0 = "mod M\n  @extern(:erlang, :time, 0)\n  fn now() -> Int\nend\n"
    {:ok, env0} = Program.elaborate(src0)
    {:ok, mod0} = Emit.compile_and_load(env0, module: :"Cure.Extern0", functions: [:now])
    # :erlang.time/0 returns a {H,M,S} tuple; just assert it runs and returns a value.
    assert apply(mod0, :now, []) != nil
  end

  test "an extern mixed with a normal dependent function — whole module elaborates + emits" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\n" <>
        "  fn double(n: Int) -> Int = n + n\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern3", functions: [:length, :double])
    assert apply(mod, :length, [[1, 2]]) == 2
    assert apply(mod, :double, [21]) == 42
  end
```

- [ ] **Step 2: Run — expect RED** (elaboration succeeds from Task 1, but emit either rejects the sentinel body or mis-lowers it — `function_form`'s `Erase.erase({:extern,…})` / the body-less filter drops it).

Run: `mix test test/cure/elab/extern_test.exs`

- [ ] **Step 3: Add the extern recognizer + remote-call emitter**

In `emit.ex`, add a predicate and a wrapper builder near `function_form` (`:125-139`):

```elixir
  defp extern_def?(%{body: {:extern, {_m, _f, _a}}}), do: true
  defp extern_def?(_), do: false

  # Wave-3: emit a direct Erlang remote call, mirroring codegen.ex:691-705 (NOT
  # calling it). Params are synthesized from the arity — a bodyless extern has no
  # {:lam,…} chain to peel, so peel_params/4 would yield zero params for arity>0.
  defp extern_form(fn_atom, {mod, fun, arity}) do
    param_forms = for i <- 0..(arity - 1)//1, do: {:var, @line, :"V#{i}"}
    remote = {:call, @line, {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}, param_forms}
    {:function, @line, fn_atom, arity, [{:clause, @line, param_forms, [], [remote]}]}
  end
```

(Note `0..(arity-1)//1` yields `[]` when `arity == 0` — the 0-arity wrapper has an empty param list and calls `mod:fun()`, correct. Verify `@line` is the module attribute emit already uses for synthesized forms; reuse it.)

- [ ] **Step 4: Route externs at the single shared choke point (`function_form`/`module_forms`) — do NOT touch the line-60 filter**

Re-verified against source: `compile_and_load/2` (`:36-44`), `compile_forms/2` (`:54-63`, the "all-defs" entry), and `compile_forms/3` (`:71-80`) are NOT three independent emit paths needing parallel routing — `compile_forms/2` computes `names` then delegates to `compile_forms/3`, and BOTH `compile_forms/3` and `compile_and_load/2` call `module_forms(env, module, names)` (`:84-93`), which does `Enum.map(names, &function_form(env, &1))` (`:85`). **`function_form/2` (`:125-139`) is the one and only place every entry point routes through.** Patch it (or its single call site in `module_forms/3`) ONCE: dispatch `extern_def?(Env.get_def(env, name))` before calling `Erase.erase`/`peel_params`/`lower`, and emit `extern_form(name, mfa)` instead. This single patch transitively fixes `compile_and_load/2`, `compile_forms/2`, and `compile_forms/3` — exactly the entry points antibodies 2/3/4 (via `compile_and_load/2`) exercise, so the fix is fully covered by tests without any dedicated `compile_forms/2` antibody.

Do NOT "widen" the line-60 filter (`is_nil(Map.get(d, :builtin_op))`, `emit.ex:60`). Re-verify before editing: an extern-marked def carries NO `builtin_op` key (only `Env.register_builtin_op/3` sets one, and the extern branch never calls it), so line 60's filter **already includes** extern defs in `compile_forms/2`'s `names` — it was never excluding them. Widening it to additionally *skip* extern names (one of the two options an earlier draft of this plan offered) would make `compile_forms/2` silently DROP every extern from the emitted module — contradicting this task's own "never dropped" contract — and nothing in this plan's test suite would catch it, since no antibody calls `compile_forms/2` (confirmed: its only callers in `lib/`+`test/` are its own definition; the real pipeline, `lib/cure/compiler.ex:353`, calls `compile_forms/3` with explicit `local_defs`). Leave line 60 exactly as-is; it continues to protect only true nil-body `builtin_op` defs, an orthogonal case.

Confirm `reject_holes` (`:104-116`) passes the sentinel (it rejects only `{:hole,_}`; `{:extern,_}` is fine) — if `reject_holes` walks def bodies more broadly, add an `{:extern,_}` allowance.

- [ ] **Step 5: Run — expect GREEN**

Run: `mix test test/cure/elab/extern_test.exs`
Expected: all pass — length→3, imax→7, now runs, mixed module both functions run.

- [ ] **Step 6: Commit (C2) — with the test file**

```bash
git -C <worktree> add -- lib/cure/elab/emit.ex test/cure/elab/extern_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): native remote-call emit for @extern FFI (value-surface Wave 3)" \
  -- lib/cure/elab/emit.ex test/cure/elab/extern_test.exs
```

---

## Task 3: Gate — firewall, core-scope, ratchet, oracle, full suite

**Deliverable:** the wave is proven additive and green, with the per-module ratchet map that sequences the following waves.

- [ ] **Step 1: Firewall + classic oracle (antibodies 5, 6).** Run `mix test test/cure/dependent_pipeline_firewall_test.exs` (green — extern emit references no classic module). Confirm the classic extern codegen tests still pass untouched (`mix test test/cure/compiler/codegen_test.exs` or whichever holds `compile_extern_function` coverage) — they are the behavioral oracle; the dependent `mod:fun(...)` result matches the classic-lowered form. Do NOT edit them.

- [ ] **Step 2: Core-scope.** `git -C <worktree> diff --stat` must show NO change under `lib/cure/core/`. The full diff = `declarations.ex`, `totality_closure.ex`, `emit.ex`, the test file (and `elaborator.ex` only if marker plumbing forced it). If any `core/` file changed, STOP — the "kernel untouched" invariant broke.

- [ ] **Step 3: Ratchet (the per-module deliverable).** Re-run the stdlib disposition script (roadmap §0). Record KEEP before/after. **Expected flips: `Std.Math`, `Std.Map`** (plausibly `Std.Pair`/`Std.Gen`). For EACH of the 9 extern modules (list, io, map, math, string, system, test, gen, pair — verify against `lib/std/*.cure`), state whether it flipped and, if not, the NEXT blocker named concretely (atom literals / string literals+`<>` / `:bad_motive` uppercase-type-var / bare-`[]` Finding A). The scout's predictions are STATIC — your run is authoritative; report honestly where a predicted flip did not happen and why. A regression in the prior KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector) = STOP.

- [ ] **Step 4: Oracle replay.** `mix test test/oracle_replay_test.exs` — report the live `N/N`; NO verdict may flip (extern is additive).

- [ ] **Step 5: Full suite ONCE.** Capture the LIVE baseline on this branch BEFORE Task 1 (or read it from the last green run) — do NOT hardcode a remembered count. Run `mix test` — 0 failures, total = baseline + new extern tests. Any unrelated pre-existing failure you did not cause → STOP and report, do not fix out of scope.

- [ ] **Step 6: Final report.** Per-commit SHA + red→green evidence; the marker representation chosen; the per-module ratchet map (before/after KEEP, which flipped, next blocker for each that didn't); firewall + core-scope result; oracle `N/N`; full-suite baseline→final; and an honest generality + trust statement (what `@extern` now does, and the §4 Claim B caveat that the FFI type is an asserted axiom — a wrong-but-runnable signature is silent unsoundness, by design).

Each of C1/C2 must be independently pre-existing-suite-green (the #22 Part-A precedent) — the NEW extern tests go green only after C2, so C1 must not break the pre-existing suite and the test file commits with C2.

---

## Out of scope (do NOT build here)

- Atom literals (next wave — system/test), string literals + `<>` (String wave — io/string), uppercase-type-var auto-lowercase+warn (the reclassified "lambda" wave — list), Finding A bare-`[]` body (`elaborate_body` whitelist increment — list).
- `@extern` with a non-trivial body, clause guards, effect typing, or dependent refinement of the FFI signature (the Π is an asserted postulate — the whole design).
- Any change to the kernel proper, or to `pickup`/`conditional`/`match`/`list`/`sigma`/`nat` emit internals, or to `declarations.ex`'s real-body dispatch whitelist.
- Adding externs to `@auto_prelude`.
