# Prim → Delta-Globals (task #15, K2 wave) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Retire the `{:prim, op, args}` Core node (and its `{:nprim}` neutral) in favor of registry-keyed builtin-op GLOBALS with literal acceleration in the certified-δ engine — surface behavior, oracle verdicts, classic-pipeline folding, and emitted runtime code all invariant — spec `docs/superpowers/specs/kernel/2026-07-09-prim-delta-globals-design.md` (hardened `8de233b`).

**Architecture:** Three phases (spec §1.7, risk R6): Phase 1 seeds the builtin-op def-kind + compute hook with `{:prim}` fully live (coexistence); Phase 2 flips every producer + retargets GuardLint/emit/Reduce; Phase 3 strips the node, flips `no_prim_node → :reject`, retargets Antigen, flips enumerated pins. K4 (absurd) is CLOSED-AS-LANDED — bookkeeping only, no code.

**Tech Stack:** Elixir, `Cure.Core.{Kernel,Eval,Normalise,Env(inductive.ex),Builtins,Validator}`, `Cure.Elab.{Elaborator,GuardLint,Emit}`, `Cure.Types.{CoreBridge,Reduce}` (carve-out), Antigen.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. Never the parent checkout.
- Two-pipeline steer: kernel = `lib/cure/core/*`, dependent elaborator = `lib/cure/elab/*`; `lib/cure/types/*`/`lib/cure/compiler/*` are decoys EXCEPT the spec §1.4 carve-out: `lib/cure/types/core_bridge.ex` + `lib/cure/types/reduce.ex` ONLY (Core-grammar consumers, D2 §8 precedent, pre-authorized). Final types/ diff = exactly those two files; compiler/ empty.
- Strict red-green; tests behavioral, immutable once green; pin flips ONLY where enumerated, each with a one-line justification (C-3 discipline); spec-§1.4-pinned classic tests (`reduce_test.exs` assertions) NEVER change.
- ONE `mix` command at a time, ever. Full suites once per phase boundary where the phase says so; final gates alone in Task 4. NO `mix cure.oracle` — replay only; divergence = STOP.
- Ghost commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO trailers, explicit pathspec. Commit per task (Phase 2 splits into 2 commits, CONSUMERS-FIRST — see Task 2 Step 8; R6 is a per-commit invariant).
- Record `git rev-parse HEAD` at Task 1 Step 0 as `<pre-15-commit>`.
- STOP-and-report = spec §4.7's per-risk list verbatim (R1 registry pin fails; R2 any ReduceTest/EqualityTest assertion change; R3 congruence retarget loses judgement strength; R4 builtin-op def reaches `Eval.eval` bodyless; R5 unenumerated error-shape flip; R6 a phase boundary leaves validator/kernel/emit disagreeing; R7 saturated/unsaturated lowering changes any existing program's runtime behavior) + any surface program newly rejected by type-directed dispatch (spec predicts ZERO) + replay divergence + any pre-existing test failing (except the known one-off Antigen-seed flake, re-run once alone).
- Line anchors are from the 2026-07-09 scout/spec; re-locate by quoted code.

## File Structure

- Phase 1: `lib/cure/core/inductive.ex` (Env builtin-op marker), `lib/cure/core/builtins.ex` (op seeding), `lib/cure/core/eval.ex` (fold made shared/public), `lib/cure/core/normalise.ex` (compute hook), `lib/cure/core/kernel.ex` (check_def/validate_certificate builtin-op guard — the R4 tail); Test: `test/cure/core/builtin_op_test.exs` (NEW).
- Phase 2: `lib/cure/elab/elaborator.ex` (build_binop + literal chain), `lib/cure/elab/guard_lint.ex`, `lib/cure/elab/emit.ex`, `lib/cure/types/core_bridge.ex`, `lib/cure/types/reduce.ex`, `lib/antigen/generators/surface_expr.ex`; Test: additions to builtin_op_test (or a new `test/cure/elab/binop_lowering_test.exs` — Task 2 Step 1's call) + existing suites as gates.
- Phase 3: strip across core (kernel/eval/value/normalise/conv/quote/term/serialize/validator) + elab walkers (elaborator/subst/unify/resolution/erase) + guard_lint prim clauses + emit prim clauses; validator ratchet; Antigen retargets (`primitive.ex`, `malformed.ex`, `conv_pair.ex`, `serialization.ex`, `dep_match.ex`, `totality.ex`, `equality.ex`, `shrink.ex`, `coverage.ex`, `totality_closure_assay.ex`) + op-def seeding into `sig_menu.ex`'s v1 env and `totality.ex`'s local env + NEW antibody `test/antigen/builtin_op_coherence_test.exs`; enumerated pin flips (full accounting table in Task 3 Step 4); `test/fixtures/core_conformance.txt`; docs drift + K4 ledger line.

---

### Task 1 (Phase 1): builtin-op def-kind + compute hook (coexistence — `{:prim}` untouched)

**Files:** Modify `lib/cure/core/inductive.ex`, `lib/cure/core/builtins.ex`, `lib/cure/core/eval.ex`, `lib/cure/core/normalise.ex`, `lib/cure/core/kernel.ex` (R4 guard). Test: `test/cure/core/builtin_op_test.exs` (NEW).

**Interfaces produced:** `Env.get_def(env, :int_add)` → `%{…, builtin_op: :add}`; `Builtins.seed/2` also seeds the 23 op defs (11 int binary + 10 float binary + int_neg/float_neg — see the table); `Eval.fold/2` public (`@doc false`; keeps its existing `{:ok, value} | :stuck` return contract, eval.ex:100-141); `Normalise` folds saturated literal builtin-op spines under `delta: :certified`; `Kernel.check_def`/`validate_certificate` accept a builtin-op def WITHOUT touching its nil body (the kernel guard in Step 3 — closes the R4 crash path spec §1.2's ordering does not cover).

- [ ] **Step 0:** `git rev-parse HEAD` → `<pre-15-commit>`. Read inductive.ex's Env section (defstruct :12, add_def :33-52, get_def :55, certify/certified? :68-86), builtins.ex in full, eval.ex:38-145, normalise.ex:190-250, kernel.ex:302-370 (check_def/validate_certificate — the R4-guard insertion points).
- [ ] **Step 1 (red):** write `test/cure/core/builtin_op_test.exs`:

```elixir
defmodule Cure.Core.BuiltinOpTest do
  @moduledoc """
  Task #15 / K2 wave (spec 2026-07-09-prim-delta-globals): primitive arithmetic
  as registry-keyed builtin-op GLOBALS with literal acceleration in the
  certified-δ engine (Lean reduce_nat / Idris Builtin-op analog). §G.1 rules
  preserved: partial ops stay neutral; open spines stay stuck (congruence).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "int_add types as an ordinary global Pi" do
    assert {:ok, {:vpi, _, _}} = Kernel.infer(ctx(), {:global, :int_add})
  end

  # NB Normalise.nf/3 returns a reified TERM, not a value (normalise.ex:36-44;
  # precedent: stuck_elim_delta_test.exs:56, sig_menu_test.exs:24).
  test "saturated literal spine folds under certified delta: 3 + 5 => 8" do
    t = Normalise.nf(ctx(), app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:int_lit, 8} = t
  end

  test "comparison folds to the inductive Bool ctor" do
    t = Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 1}, {:int_lit, 2}), delta: :certified)
    assert {:ctor, :True, []} = t
  end

  test "G.1 rule 1: div/rem by literal zero stays neutral (never crashes)" do
    for g <- [:int_div, :int_rem] do
      t = Normalise.nf(ctx(), app2(g, {:int_lit, 7}, {:int_lit, 0}), delta: :certified)
      assert app2(g, {:int_lit, 7}, {:int_lit, 0}) == t
    end
  end

  test "open spine stays stuck; conversion is spine congruence" do
    # under a binder: int_add x 1 vs int_add x 1 convertible; vs int_add x 2 not.
    # Conv.conv?/5 is conv?(t1, t2, value_env, depth, sig) — conv.ex:47-51,
    # precedent stuck_elim_delta_test.exs:72.
    ctx1 = Context.extend(ctx(), {:vint_type})
    t1 = app2(:int_add, {:var, 0}, {:int_lit, 1})
    t2 = app2(:int_add, {:var, 0}, {:int_lit, 2})
    assert {:ok, {:vint_type}} = Kernel.infer(ctx1, t1)
    assert t1 == Normalise.nf(ctx1, t1, delta: :certified)
    venv = Context.env(ctx1)
    refute Conv.conv?(t1, t2, venv, 1, env())
    assert Conv.conv?(t1, t1, venv, 1, env())
  end

  test "R1 pin: a user-registered int_add with its OWN body is never builtin-folded" do
    # Register int_add as an ORDINARY def (constant-42 body) in a NON-seeded env:
    # the builtin marker comes only from Builtins.seed, so this def has none.
    # Env.certify/2 accepts it (closed lam body — inductive.ex:68-82).
    ty = {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}
    body = {:lam, {:int_type}, {:lam, {:int_type}, {:int_lit, 42}}}
    env = Env.empty() |> Env.add_def(:int_add, ty, body) |> Env.certify(:int_add)
    ctx = Context.empty(env)
    t = Normalise.nf(ctx, app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:int_lit, 42} = t
  end

  test "R4 guard: check_def/validate_certificate accept a builtin-op def without touching its nil body" do
    # Spec §1.2's ordering protects the normalise path only. check_def
    # (kernel.ex:310-323) matches %{type:, body:} and would call
    # check(ctx, nil, _) → infer has NO nil clause → crash. Reachable via
    # TotalityClosure.certify_type_level once builtin-op spines appear in TYPE
    # positions (post-Phase-2 dependent-index arithmetic). Behavioral pin: both
    # entries succeed on a seeded op.
    assert :ok = Kernel.check_def(env(), :int_add)
    assert {:ok, env2} = Kernel.validate_certificate(env(), :int_add)
    assert Env.certified?(env2, :int_add)
  end
end
```

(Call shapes above are verified against the current source: `Normalise.nf/3` — Context + term + opts, returns a term; `Conv.conv?/5`; `Context.extend/2` takes a type VALUE; `Context.env/1` builds the value env. ASSERTIONS immutable, plumbing adjustable only if the source moves. If #10's global-collision protection makes the R1 construction impossible as written, pin the protection's actual behavior instead — the invariant is "never builtin-folded", report the adaptation.)
- [ ] **Step 2 (verify red):** run scoped. Red/pin split is EXPECTED as follows: tests 1-3, the infer line of test 5, and the R4-guard test FAIL pre-impl — all as `:unknown_global`/no-folding (`int_add` is not seeded yet; the R4 test's `check_def` crash mode only becomes reachable AFTER seeding, which is exactly why the guard lands in the same step as the seeds); the div-zero test and the R1 pin PASS pre-impl (unknown-global spines are already stuck; an ordinary certified def already unfolds by its body) — they are regression pins the implementation must KEEP green, not reds. Record which is which.
- [ ] **Step 3 (implement):**
  - `inductive.ex` Env: `add_def/5` keeps its shape; add `register_builtin_op(env, name, op_key)` that `Map.update!`s the existing def to add `builtin_op: op_key`, and `builtin_op(env_or_nil, name)` returning the key or nil (get_def-based; a `nil` env returns `nil` — `Context.signature/1` can be nil and GuardLint calls this in Phase 2, so nil-tolerance is defined HERE, not patched later). Defs seeded by Builtins carry the marker; user defs never do.
  - `builtins.ex`: add the op table + seeding (after the inductive seeds, so Bool exists for comparison codomains):

```elixir
  @int, @float, @bool as module attrs or inline:
  # {name, op_key, domain, codomain}
  @ops [
    {:int_add, :add, :int, :int}, {:int_sub, :sub, :int, :int},
    {:int_mul, :mul, :int, :int}, {:int_div, :div, :int, :int},
    {:int_rem, :rem, :int, :int},
    {:int_lt, :lt, :int, :bool}, {:int_le, :le, :int, :bool},
    {:int_gt, :gt, :int, :bool}, {:int_ge, :ge, :int, :bool},
    {:int_eq, :eq, :int, :bool}, {:int_ne, :ne, :int, :bool},
    {:float_add, :add, :float, :float}, {:float_sub, :sub, :float, :float},
    {:float_mul, :mul, :float, :float}, {:float_div, :div, :float, :float},
    {:float_lt, :lt, :float, :bool}, {:float_le, :le, :float, :bool},
    {:float_gt, :gt, :float, :bool}, {:float_ge, :ge, :float, :bool},
    {:float_eq, :eq, :float, :bool}, {:float_ne, :ne, :float, :bool}
  ]
  @unops [{:int_neg, :neg, :int}, {:float_neg, :neg, :float}]
```

  Structure the op seeding as a public `Builtins.seed_ops/1` (or `/2` with exclude) that `seed/2` calls — Task 3 Step 1 reuses it to give the Antigen generator envs the op defs. Seed each as `Env.add_def(env, name, pi_of(domain, codomain), nil)` + `Env.register_builtin_op(env, name, op_key)`. R1 mechanism, precisely: the seed runs FIRST (`Program` builds env0 from `Builtins.seed`, program.ex:134) and a user module's own `fn int_add` lands later via `Env.add_def` — whose `Map.put` REPLACES the whole def record with a fresh `%{name, type, body, quantities}` map carrying NO `builtin_op` key — so the marker is dropped and the marker-keyed hook/emit/lint all treat it as an ordinary def. (`maybe_seed`'s exclude set is `declared_type_names` — TYPE names only — so it never covers fn names; do NOT lean on it for R1. The overwrite semantics + marker-keyed consumers ARE the guarantee — and they hold for IMPORTED same-named defs too: `merge_env(seeded, imported)` merges imported defs OVER the seed, program.ex:671-680. Pin it with the R1 test.) Type terms: `{:int_type}`/`{:float_type}`; the Bool codomain resolves through the registry — `{:data, Inductive.builtin(env, :bool), [], []}` (registry-keyed like `Kernel.bool_type_value/1`, not the bare `:Bool` atom), which is why op seeding runs AFTER the inductive seeds. NOTE `int_rem`: Int-only (matches infer_prim :1048); there is NO `float_rem`. Arity check: binary ops 2, neg 1. Seeding does NOT call `Env.certify` (the hook's marker dispatch never consults `certified?` — spec §1.2).
  - `kernel.ex` R4 guard (closes the crash path spec §1.2's ordering does NOT cover): `check_def/2` and `validate_certificate/2` gain a leading builtin-op branch — a def whose record carries `builtin_op` type-checks its DECLARED TYPE only (`infer_sort` on the type term) and is certified by fiat (`{:ok, Env.certify(env, name)}` in validate_certificate; `:ok` in check_def), never touching the nil body. Without this, `check_def`'s `%{type:, body:}` match calls `check(ctx, nil, _)` → `infer` has no nil clause → FunctionClauseError, reachable via `TotalityClosure.certify_type_level` (totality_closure.ex:35-45) once Phase 2 puts builtin-op spines in type positions. Lean/Idris-aligned (primitive ops are total by fiat in both), TCB blanket applies. Red test: the R4-guard test above.
  - `eval.ex`: `defp fold` → `@doc false def fold` (same table, byte-identical clauses, same `{:ok, value} | :stuck` returns; Eval's own prim clause keeps calling it via `prim/2`).
  - `normalise.ex` `unfold_certified_head`: at the `{:nglobal, name}` arm, dispatch FIRST on the builtin marker (spec §1.2's load-bearing ordering — a bodyless def must never reach the generic `Eval.eval(body, [])` path):

```elixir
      {:nglobal, name} ->
        case Env.get_def(sig, name) do
          %{builtin_op: op} when not is_nil(op) ->
            builtin_op_fold(op, args, sig, opts)

          _ ->
            <the existing with-block, unchanged>
        end
```

```elixir
  # Literal acceleration for builtin-op globals (spec 2026-07-09 §1.2; Lean
  # reduce_nat / Idris Builtin-op analog). Fold ONLY a saturated spine whose
  # arguments all whnf to literals — via the SAME audited table Eval uses
  # (§G.1: div/rem by literal zero returns :stuck and the spine stays neutral).
  # Anything else (open args, wrong arity/overapplication) stays stuck: never
  # unsound, at worst a missed unfold.
  defp builtin_op_fold(op, args, sig, opts) do
    arity = if op == :neg, do: 1, else: 2

    with true <- length(args) == arity,
         vals = Enum.map(args, &whnf_value(&1, sig, opts)),
         true <- Enum.all?(vals, &(match?({:vint, _}, &1) or match?({:vfloat, _}, &1))) do
      Eval.fold(op, vals)
    else
      _ -> :stuck
    end
  end
```

  (Verified call shapes: `spine/2` accumulates the `{:napp, …}` spine's args, which are already VALUES (value.ex:25), so `whnf_value(&1, sig, opts)` — value-first, normalise.ex:51-65 — only forces residual certified-global redexes among them. `Eval.fold(op, vals)` is the 2-arg convention `prim/2` uses (eval.ex:93-98) and ALREADY returns `{:ok, value} | :stuck` — exactly the contract `unfold_certified_head`'s callers consume (`whnf_value`'s `{:ok, reduced} | :stuck` case at normalise.ex:59-62, same shape the `:ncase` arm returns) — so the fold result passes through UNWRAPPED; do not re-wrap it.)
- [ ] **Step 4 (green + phase boundary):** scoped file 7/7 → `mix test test/cure/core/` → `mix test test/cure/elab/` (every `Program.elaborate` env now carries 23 extra defs — verified no test pins the exact def set, but this is the cheap boundary check) → `mix test test/antigen/` (spec §4.2: FULL Antigen green at EACH phase boundary) — one at a time, all green (coexistence: every prim test untouched and passing).
- [ ] **Step 5: Commit** `feat(kernel): builtin-op def-kind + literal-acceleration delta hook (K2 phase 1; {:prim} coexists)` — pathspec the 5 lib files (inductive/builtins/eval/normalise/kernel) + test.

---

### Task 2 (Phase 2): flip every producer; retarget GuardLint, emit, core_bridge/Reduce

**Files:** `lib/cure/elab/elaborator.ex`, `lib/cure/elab/guard_lint.ex`, `lib/cure/elab/emit.ex`, `lib/cure/types/core_bridge.ex`, `lib/cure/types/reduce.ex`, `lib/antigen/generators/surface_expr.ex`.

- [ ] **Step 0 (the corpus survey — spec §1.3/§1.4 obligations, read-only):** (a) verify by grep that `==`/`!=` on non-int/float/bool operands appears in NO test/oracle surface program (spec sampled 4 oracle `==` uses, all int-guard; make it exhaustive over `test/oracle/**/*.cure` + `test/**/*.exs` surface fixtures + `examples/`); (b) verify zero live float-typed dependent-index arithmetic reaches core_bridge (grep classic-pipeline tests for float refinement indices). Any counterexample → STOP (spec §4.7).
- [ ] **Step 1 (red):** add to `builtin_op_test.exs` (new describe, or a small elab-side file `test/cure/elab/binop_lowering_test.exs`): elaborating `fn f(x: Int) -> Int = x + 1` yields Core containing `{:app, {:app, {:global, :int_add}, …}` and NO `{:prim,…}`; a float version yields `float_add`; `x == 1` in an Int guard lowers to `int_eq`. Run: red (still prims).
- [ ] **Step 2 (elaborator):** `build_binop` (elaborator.ex:635-655; `l_type` is genuinely available — the single call site :505 passes the inferred left-operand type + `Context.signature(ctx)`): the `:==`/`:!=` clauses' else-branches and the arithmetic catch-all switch on `primitive_scrut_kind(l_type, sig)` (:2601-2608; currently discarded by the catch-all — spec §1.3). In the `:==`/`:!=` clauses: `:bool` keeps `app2(:eq/:ne,…)` (unchanged), `:int` → `int_eq`/`int_ne`, `:float` → `float_eq`/`float_ne`, other → error. In the arithmetic/order catch-all: `:int` → int map, `:float` → float map, anything else (incl. `:bool` — no Bool arithmetic) → `{:error, {:unsupported_operand_type, op_sym}}` (flows through the caller's `other -> other` else-branch at :510; enumerated R5 churn — today these die as kernel `{:prim_type, op}`). Maps are explicit literals (`%{add: :int_add, …}`, NO dynamic atom construction); the float map has NO `rem` entry (no `float_rem` seeded — `rem` on Float becomes the same `:unsupported_operand_type` error, enumerated churn; today it dies as kernel `{:prim_type, :rem}`). Literal-pattern chain (elaborator.ex:2657-2666): `{:prim, :eq, [scrut_term, lit_core(v, prim)]}` → dispatch on the `prim` kind ALREADY in scope in `literal_chain/8`: `:int` → `app2(:int_eq, …)`, `:float` → `app2(:float_eq, …)` (float literal patterns EXIST — `literal_of?`/`lit_core` :2630-2640), `:bool` → `app2(:eq, …)` (the Std.Bool def — a Bool literal + catch-all chain reaches here when `bool_exhaustive?` fails). `prim_op/1` stays for now (dead after this task, stripped in Phase 3).
- [ ] **Step 3 (GuardLint):** add spine-recognizing clauses ABOVE the prim ones (both live this phase):

```elixir
  # Builtin-op global spine (K2, spec 2026-07-09 §1.6): registry-keyed via the
  # def record — a user def named int_add carries no marker and falls to the
  # sound uninterpreted fallback.
  defp bool_form({:app, {:app, {:global, g}, a}, b}, ctx, st) do
    case Env.builtin_op(Context.signature(ctx), g) do
      op when is_map_key(@cmp, op) -> (the existing comparison body over a/b)
      _ -> :error
    end
  end
```

  RED for this step: `guard_lint_test.exs`'s "elaboration integration (§6)" describe (:101+) drives `Program.elaborate/1` — once Step 2 lands, its guards arrive as SPINES and the `:proven`-expecting recovery rows go red at elaborate-time (untranslatable → not proven → non-exhaustive); run it scoped between Steps 2 and 3 to observe. NB these tests also `Emit.compile_and_load` the result, so they go fully green only once Step 4's emit lowering ALSO lands — Step 3 clears the elaborate-time failure only. (The hand-built-Core unit describe (:21-99) keeps driving the prim clauses — green until Phase 3.) Add the `int_form` twins for `:add`/`:sub`/`:mul` (mul keeps the literal-multiplicand linearity guard). Only INT-typed forms translate (int_form's var clause already gates on `{:vint_type}` via `Context.lookup`, guard_lint.ex:110-115 — a float_* spine's operands fail it → `:error` → the sound uninterpreted fallback; note `Env.builtin_op` returns the SAME op key for int_* and float_* twins, so the operand-type gate is what keeps float ops out). `Context.signature/1` returns `Env.t() | nil` (context.ex:32-33) — `Env.builtin_op/2` is already nil-tolerant (defined so in T1), so the lint stays total; add `alias Cure.Core.Env` (GuardLint currently aliases only Context).
- [ ] **Step 4 (emit):** per spec §1.5, keyed via `Env.builtin_op/2` (the ONE accessor Step T1 added — not `Inductive.builtin/2`, which is the family registry): (a) saturated inline — in `lower({:app,…})`'s dispatch (emit.ex:205-215), when `spine/2` yields head `{:global, g}` with `Env.builtin_op(env, g)` = op and exactly-arity args, emit `{:op, @line, erl_binop(op), …}`/unop; (b) bare reference — a branch BEFORE the generic body of `lower(env, {:global, name}, _ctx)` (emit.ex:270-275): builtin-op global as a value → local `{:fun, @line, {:clauses, [...]}}` wrapper computing the op (the generic path is wrong twice over: `present_arity` reads `quantities` (nil for op defs → 0, emit.ex:277-282) and no top-level function exists to reference); (c) PARTIAL spine — 0 < n < arity args must NOT reach `lower_app_spine`'s generic `{:global, name}` branch (present_arity 0 would emit a call to a nonexistent `int_add()`): route it as wrapper-from-(b) + curried `{:call, …}` applications, same as the closure branch. Red rows in Step 1's file cover (a) behaviorally via the existing e2e gates; for (b)/(c) add one CORE-LEVEL row (surface Cure cannot name `int_add`/`+` as a value, so the wrapper is reachable only from hand-built Core): register a HOF def whose body passes `{:global, :int_add}` (bare, and 1-arg partial) into an apply, `Emit.compile_and_load` + `apply` it — crib the harness from `first_class_function_test.exs` — asserting the arithmetic result. Red pre-retarget (the generic path emits a call to a nonexistent `int_add/0` → compile error). ALSO: `Emit.compile_forms/2` (the ALL-defs entry, emit.ex:56-60, `names = Map.keys(defs)`) must skip builtin-op defs — bodyless, nothing to emit (`function_form` would crash on nil); the live pipeline uses `/3` with `local_defs` (compiler.ex:352-353) so this is defensive, but the /2 entry is public. Keep the `{:prim,…}` lowering clauses (both live until Phase 3).
- [ ] **Step 5 (carve-out):** `core_bridge.ex` — `to_core` binary_op/unary_op clauses produce builtin-op spines with SHAPE dispatch (either converted operand `{:float_lit,_}` → float_*, else int_*; spec §1.4); STOP producing `and/or/not` prims (those clauses return `:error` → `structural_congruence` + surface `fold_bool_binop` keep Bool folding, the recorded precedent). `from_core` — DEDICATED reverse clauses for builtin-op-headed spines (reverse map to `{:binary_op, [operator: :+], …}` etc.) placed BEFORE the generic `{:app,…}` unwind clause (spec §1.4's mis-render trap; the CONCRETE pins are `reduce_test.exs:80-89`'s unbound-variable rows — `assert {:binary_op, _, [{:variable, _, "n"}, _]}` — the only rows whose spine stays STUCK and must read back as a binary_op, not a `function_call "int_add"`); delete the prim reverse clauses in Phase 3, keep this phase. `reduce.ex` `kernel_normalize_via_core` (:97-99): replace `Eval.eval([]) |> Quote.reify()` with `Normalise.nf(Context.empty(seeded_env()), core, delta: :certified)` — `nf/3` takes a `Context.t()` (build one with `Context.empty/1` over the seeded env) and RETURNS the reified term itself (normalise.ex:36-44), so no separate `Quote.reify`; feed it straight to `from_core`. `seeded_env/0` = a private helper returning `Builtins.seed(Env.empty())` — recompute per call (seeding is cheap map-building; a compile-time module attribute would work but adds a Builtins compile-order coupling, and `persistent_term` is banned). Free surface variables arrive as uncertified `{:global,…}` heads (to_core :51) → stuck → read back → `from_core`'s `{:global, name}` clause, unchanged behavior. This switch MUST land in the same commit as the `to_core` producer flip (spines don't fold under bare `Eval.eval([])` — ReduceTest would break in between).
- [ ] **Step 6 (Antigen lockstep):** `surface_expr.ex` :44 `encode/2` emits the builtin-op spine. NB it differentially pins `CoreBridge.to_core` (the Normalizer assay family — its own moduledoc), NOT build_binop as spec §3's "lockstep with build_binop" loosely says: mirror to_core's SHAPE dispatch from Step 5 (operand `{:float_lit,_}` → float_*, else int_* — moot today, the catalog is Int-only, but the rule must match the code it pins), and land it in commit 2b WITH the to_core flip. Its `and`/`or` `@ops` rows follow whatever to_core's and/or clauses become (:error → the rows either re-pin the surface fold path or drop with justification — iterate against the normalizer assay).
- [ ] **Step 7 (gates):** scoped red file green → `mix test test/cure/elab/` → `mix test test/cure/types/` (ReduceTest/EqualityTest assertions UNCHANGED — R2 STOP otherwise) → `mix test test/cure/e2e/frp_beam_test.exs` + `mix test test/cure/compiler/dependent_surface_codegen_test.exs` (runtime ABI) → `mix test test/antigen/` → `mix test test/oracle_replay_test.exs` (guard clusters sensitive) — one at a time. Expected pin flips HERE (enumerate + justify each): `bool_connective_lowering_test.exs:38-51` (the three "Int/Float ==/!= stays a native :eq/:ne prim" rows — the deliberate anti-pin, flips to int_eq/float_eq/int_ne spines); `test/antigen/assays/normalizer_test.exs` expected-Core rows (`{:prim, :add, …}` at :19/:24/:34/:44/:58 — differential pins on core_bridge's translation, flip to int_add spines WITH the to_core flip). Verified NON-flips: `emit_test.exs` contains no `{:prim,` rows (grep-verified — saturated inline keeps op-level output identical, nothing to flip); `literal_pattern_test.exs`/`guard_test.exs` mention prim in moduledoc PROSE only (behavioral assertions — stay green; update the two doc comments, no pin flip); `guard_lint_test.exs:17`-style direct-prim constructions stay green while the prim clauses live — they flip in Phase 3. Anything else red = STOP.
- [ ] **Step 8: Commit(s):** split CONSUMERS-FIRST so each commit is R6-clean (spec §4.7 R6 is per-COMMIT: no commit may leave validator/kernel/emit disagreeing — a producers-first commit would emit spines that emit/GuardLint/from_core can't yet handle). Pathspecs are whole files, so `core_bridge.ex` (which mixes from_core recognition and to_core production) goes WHOLLY in 2b — never split one file across the two commits: commit 2a `feat(emit+lint): recognize builtin-op spines (GuardLint, emit inline/wrapper) (K2 phase 2a)` — purely ADDITIVE recognition, pathspec guard_lint.ex + emit.ex ONLY (lib-only; every Phase-2 test file goes in 2b, since the new test files mix rows that need 2b's producers); commit 2b `feat(elab+bridge): lower arithmetic/comparison to builtin-op globals; from_core reverses; Reduce via kernel normalization (K2 phase 2b)` — pathspec elaborator.ex + core_bridge.ex + reduce.ex + surface_expr.ex + all Phase-2 test files (new + flipped) (core_bridge's from_core reverses land here WITH its to_core flip — same-commit is what keeps ReduceTest green at the 2b boundary). Both from the same green post-Step-7 tree.

---

### Task 3 (Phase 3): strip `{:prim}`/`{:nprim}`, ratchet, Antigen retargets, pin flips

**Files:** strip list per spec §2 (kernel.ex :69/:998/:1037-1105 — but KEEP `bool_type_value/1`; eval.ex :47 prim clause + `prim/2` — `fold` STAYS, Normalise uses it; value.ex :56; normalise.ex :171-172; conv.ex :123/:161-162; quote.ex :95-96; term.ex :62/:106/:176/:220/:258; serialize.ex :33/:152; validator.ex children :128; elaborator :2053/:3939 + now-dead `prim_op/1`; subst.ex :69/:106; unify.ex :258/:385; resolution.ex :37; erase.ex :139; guard_lint prim clauses; emit :188-194 prim clauses; core_bridge from_core prim reverse clauses); `lib/cure/core/validator.ex` ratchet; Antigen files per spec §3 + `lib/antigen/generators/sig_menu.ex` (v1 env gains the op defs) + `lib/antigen/generators/totality.ex` env; NEW `test/antigen/builtin_op_coherence_test.exs`; `test/fixtures/core_conformance.txt`; enumerated test-pin flips (Step 4 table); docs (grammar spec §J drift + audit pointer + K4 ledger line + parity-ledger #15 row).

- [ ] **Step 1 (Antigen retargets FIRST, node still live):** PRECONDITION — the generator ENVS must carry the op defs or every retargeted spine dies `:unknown_global`: `SigMenu.env_of(:v1)` is HAND-BUILT (sig_menu.ex:37+, no `Builtins.seed` call) and `Generators.Totality` builds `Env.empty() |> add_def…` (totality.ex:699) — extend both with the builtin-op defs (expose a `Builtins.seed_ops/1` from T1 or call the seeding helper) BEFORE retargeting; without this, malformed's two retargeted seeds collapse into one `:unknown_global` class and the R5 enumeration is wrong. Then: `primitive.ex` full retarget to builtin-op spines (fold reachability, stuck paths, div-zero rules — the generator's property tests are the oracle, iterate); `malformed.ex` :53/:56 (unknown-op → an UNREGISTERED global spine `{:app,…{:global,:nosuchop}…}` erroring `:unknown_global` (kernel.ex:95 — exists today); wrong-operand → int_add on a ctor, erroring as the app-argument check failure (`check`-against-`{:vint_type}` mismatch — exists today) — new tags enumerated per R5); `conv_pair.ex` :50 nprim rows → builtin-spine napp congruence rows (pins spec §1.8/R3; conv?'s napp congruence needs no def record, sig-independent); `serialization.ex` :23/:95-97 grammar rows re-spell as spines; `dep_match.ex` :105 computed-index row re-spells (needs :int_add in the v1 env — the precondition); `totality.ex` :342 (needs :int_eq in ITS env — the precondition); `equality.ex` :150-152; `shrink.ex` :172 child slots; `coverage.ex` :92 former class (prim class retires or re-keys to builtin-op spines — check what the coverage gate pins); `totality_closure_assay.ex` :93 sanity (op names as terminal call-graph nodes). NEW ANTIBODY (spec §3/§4.2 requires it as an Antigen-resident file, distinct from the T1 ExUnit suite): `test/antigen/builtin_op_coherence_test.exs` in the `builtin_bool_drift_test.exs` style — literal folds per §G.1 incl. the zero-divisor stuck rule, open-spine congruence, and the R1 user-`int_add`-not-folded pin. Run `mix test test/antigen/` — green with the retargets while both representations exist.
- [ ] **Step 2 (strip):** FIRST write the reds for this removal: the term_test/value_test negative grammar rows defined in Step 4's incidental bucket (`refute Term.term?({:prim, …})` / `refute Value.neutral?({:nprim, …})`) — red against the still-live clauses. Then remove every listed clause (removal-only; re-locate by quoted code). Keep: `Eval.fold`, the validator `no_prim_node` PREDICATE (:194), emit's erl_binop/erl_unop tables (the inline uses them), AND `Kernel.bool_type_value/1` (public, the elaborator's literal/`:case` lowering uses it — it sits between the `infer_prim` clauses being stripped at :1057-1067, do not sweep it up). `Term.term?` drops `{:prim,…}` — the grammar shrink.
- [ ] **Step 3 (ratchet + docs, red-first):** add the `validator_test.exs` rows asserting `no_prim_node: :reject` in wave0 + release FIRST (red against the current `:warn`), then flip: wave0 `no_prim_node: :warn → :reject` with the Phase-C-style comment; ADD `|> Map.put(:no_prim_node, :reject)` to `@release_config` (validator.ex:90-95 — currently missing, the drift); fix `final-core-grammar-design.md` §J's `:off` claim + add the audit pointer (spec §6.6: pointer, not rewrite); parity-ledger: #15 row done + K4 closed-as-landed line.
- [ ] **Step 4 (pin flips — the COMPLETE accounting; every `{:prim,`/`:nprim` test occurrence is in exactly one bucket, NOTHING flipped silently):**
  - **Grammar/kernel pins that FLIP here:** `int_prim_test.exs`/`float_prim_test.exs` (rewrite as builtin-op suites — same §G.1 behaviors, spine spelling: fold/stuck/zero-divisor/defeq/typing; typing negatives become app-argument errors per R5; the two files are also the ONLY `:nprim` matches in test/); `bool_prim_test.exs`, `prim_bool_eval_test.exs`, `prim_bool_inductive_test.exs`, `bool_connective_defeq_test.exs:81-93` (residual-prim + prim-comparison rows — terms leave the grammar; re-spell comparisons as spines, replace the `{:unknown_prim, :and/:or/:not}` rows with `:unknown_global`-spine equivalents or drop with justification); `test/antigen/builtin_bool_drift_test.exs`, `builtin_bool_migration_test.exs`, `sig_menu_test.exs:23-24` (eval/infer prim rows → spine spellings); `guard_lint_test.exs:17` (`p/3` prim constructor → spine builder); `validator_test.exs:90` + ratchet rows (+ the "only retired primitives reject in Wave 0" meta-pin gains `no_prim_node`); `serialize_test.exs:34-35/:57/:62` grammar+typing rows → spine spellings + the negative-decode row for `(prim …)` (mirror D2's precedent); conformance fixture `test/fixtures/core_conformance.txt:12-17/:27-29` `(prim …)` rows → spine spellings (accept) / stay-reject equivalents; `test/antigen/generators/primitive_test.exs` and `test/antigen/assays/totality_closure_assay_test.exs:91` (the `{:prim, :eq, [{:global, :buried}, …]}` family-index row pinning the assay's globals walker — re-spells as an int_eq spine) — accounting note: these two flip DURING Step 1 with their lib retargets (the Step-1 Antigen gate requires it); they are listed here so the sweep finds them accounted.
  - **Elab-walker re-spells (constructions only, assertions unchanged in spirit):** `miller_unify_test.exs:119-120` (mabs walker), `unify_meta_completeness_test.exs:60-61` (escapes? walker), `program_codegen_gate_test.exs:13` + `erase_test.exs:86-87` (has_hole? walker) — re-spell `{:prim, :add, …}` as int_add spines; the generic `{:app,…}` walker clauses take over, same verdicts.
  - **Incidental — NO flip (ctor NAMED `:prim` in the SF/FRP fixtures, not the node):** `match_test.exs:44`, `term_test.exs:53`, `value_test.exs:31`, `serialize_test.exs:39` (branch tuple `{:prim, 2, …}` — ctor name), plus every `prim :`/`:prim`-as-ctor hit in slice1_run/ctor_app/indexed_declarations/erasure_*/inductive_wf/dependent_codegen — untouched. (In exchange, ADD negative grammar rows `refute Term.term?({:prim, :add, […]})` / `refute Value.neutral?({:nprim, …})` to term_test/value_test — written immediately BEFORE Step 2's strip, red against the still-live clauses, going green WITH the strip: the red for this removal step.)
  - **Incidental — doc-prose only:** `literal_pattern_test.exs:7`, `guard_test.exs:9` moduledoc mentions — update the prose, zero assertion changes.
  - **Stays green, out of scope:** `module_encoder_test.exs:64` — the Lean encoder (lib/cure/lean/, not in the strip list) still rejects the raw tuple; the row keeps passing. Note it in the report; optionally re-tag its comment.
  - Final sweep: grep `{:prim,` + `:nprim` over `test/` must map every remaining hit to a bucket above; a new unaccounted hit = STOP and enumerate before flipping.
- [ ] **Step 5 (gates):** `mix test test/cure/core/` → `mix test test/cure/elab/` → `mix test test/antigen/` → `mix test test/cure/types/` — green, one at a time.
- [ ] **Step 6: Commit** `refactor(kernel)!: strip {:prim}/{:nprim} from Core — builtin-op globals are canonical (K2 phase 3; no_prim_node :reject; K4 closed)` — explicit pathspecs (lib + tests + fixtures + docs).

---

### Task 4: full gate + final verification

- [ ] **Step 1 (alone, in order):** 1. `mix test test/antigen/` (count re-derived vs 499 + retargets). 2. `mix test` — 0 failures; delta vs 3265 fully enumerated (new builtin_op/binop tests + retargeted/rewritten files ± dropped rows). 3. `mix test test/oracle_replay_test.exs` — zero divergence.
- [ ] **Step 2:** from `<pre-15-commit>`: grammar greps — zero `{:prim,`/`{:nprim` constructors under `lib/cure/core/`, `lib/cure/elab/`, `lib/antigen/`, AND `lib/cure/types/core_bridge.ex` (validator predicate + erl tables excepted); `git diff --stat -- lib/cure/types/` = exactly core_bridge.ex + reduce.ex; `lib/cure/compiler/` empty; ghost authors only; the R1 pin green; K4/drift docs landed.
- [ ] **Step 3:** report per the report-back spec; update memory (kernel-primitive-endgame → CLASS CLOSED) per its instructions.

## Self-review notes (spec-coverage map)

- §1.1 registry keying → T1 Step 3 (marker only via seed) + R1 pin + GuardLint/emit registry lookups (all via `Env.builtin_op/2`, the single accessor). §1.2 hook+ordering → T1 Step 3 (dispatch-first shape, bodyless never reaches Eval.eval) + the T1 kernel R4 guard (check_def/validate_certificate — the nil-body consumer path spec §1.2's ordering argument does not itself cover; plan extends the closure, spec text untouched). §1.3 monomorphic set + type-directed dispatch + corpus survey → T1 table, T2 Steps 0/2. §1.4 carve-out (to_core shape dispatch, from_core ordered reverses, Reduce via kernel normalization, ReduceTest pin) → T2 Step 5. §1.5 emit → T2 Step 4 (saturated inline + bare wrapper + PARTIAL-spine curry + compile_forms/2 skip). §1.6 GuardLint → T2 Step 3 + Phase-3 strip. §1.7 phases → task structure; both-live invariants stated per phase; commit granularity consumers-first (T2 Step 8) so R6 holds per commit. §1.8 congruence → conv_pair retarget (T3 Step 1) + open-spine test (T1). §1.9 error churn → T3 Steps 1/4 enumerations. §3's new antibody → T3 Step 1 (`builtin_op_coherence_test.exs`). §4.1 red-green/immutable/enumerated-flips → Global Constraints + per-step red notes; §4.2 Antigen per-phase → T2 Step 7 / T3 Steps 1+5 / T4 Step 1; §4.3 full suite + delta → T4 Step 1; §4.4 replay-only oracle → T2 Step 7 + T4 Step 1; §4.5 greps incl. core_bridge → T4 Step 2. §4.6 K4+drift → T3 Step 3. §4.7 STOP list → Global Constraints (verbatim). §0 decision record → untouched (spec-resident).
- §6 acceptance criteria homes: 6.1 (zero constructors + reject + docs) → T3 Steps 2-4 + T4 Step 2 greps; 6.2 (behavior invariant: replay/Reduce/emit/first-class) → T2 Steps 4-5/7 + T4 Step 1; 6.3 (GuardLint registry-keyed + guard fixtures + drop_guard) → T2 Step 3 + T2/T4 gates; 6.4 (R1 pin) → T1 test + T3 antibody; 6.5 (full suites, per-phase ghost commits, K4 ledger) → T1/2/3 commits + T3 Step 3 + T4; 6.6 (audit pointer, not rewrite) → T3 Step 3.
- Latitude: the op→name literal maps' spelling; Antigen retarget shapes (iterate against immutable property tests); pin-flip justification one-liners; gate recounts. All report-required. (API call shapes are NOT latitude — they are verified against source in this plan.)
- Known in-task decision points with STOP fallbacks: #10-collision interaction with the R1 pin construction; coverage.ex former-class retirement shape; the exact seeding-helper shape for the Antigen envs (`Builtins.seed_ops/1` vs reuse of `seed/2`).

---

## Amendment A1 deltas (2026-07-09, adjudicated mid-execution — spec §1-A, commit 72994f4; APPEND-ONLY)

Task 2 Step 0's corpus survey found the predicted-zero counterexample (`ctor_guard_test.exs` Nat-`==` guards); adjudication adopted structural-equality GLOBALS. These deltas amend the tasks below WITHOUT rewriting them; where a delta touches a numbered step, the delta governs.

- **Op set is 25, not 23.** Task 1's Builtins table gains two polymorphic structural ops seeded by the SAME `seed_ops/1` (marker atoms `:struct_eq`/`:struct_ne`, distinct from `:eq`/`:ne`):
  `struct_eq, struct_ne : {:pi, {:type, 0}, {:pi, {:var, 0}, {:pi, {:var, 1}, Bool}}}` — explicit ω-present type argument, arity 3 (registry-keyed like the other 23; R1 protection identical). Every "23" in Tasks 1/3/4 accounting reads 25.
- **Compute hook (normalise.ex `builtin_op_fold`):** `:struct_eq`/`:struct_ne` take arity 3 and delegate to `Eval.fold(:eq/:ne, [l, r])` over spine args 2 and 3 (the type arg is NOT consulted and NOT whnf'd for literalness). Folds iff both value args whnf to vint/vfloat (late-instantiated polymorphic operands, same as today's prim); NEUTRAL otherwise — ADT equality stays kernel-neutral (R8c: computing on non-int/float = STOP). Conv: generic global-spine congruence, nothing to add.
- **Task 2 Step 2 (elaborator): `build_binop` `:==`/`:!=` dispatch is 4-way, not 3-way-with-error:** `:bool` → `app2(:eq/:ne)` (unchanged); `:int` → `int_eq`/`int_ne`; `:float` → `float_eq`/`float_ne`; `:error` → `struct_eq`/`struct_ne` applied to the READBACK (quote) of `l_type` plus `l`, `r` — NOT an error. Signature latitude: thread `ctx` (or the pre-quoted type) into `build_binop` (D1 reify precedent). The arithmetic/order catch-all's dispatch (`:int`/`:float`/other→`{:error, {:unsupported_operand_type, op_sym}}`) is UNCHANGED from the original Step 2 (survey-confirmed no non-numeric arithmetic exists). R8b: a meta-containing/under-determined `l_type` readback at any live call site = STOP.
- **Task 2 Step 3 (GuardLint):** `struct_eq`/`struct_ne` spines get NO recognizer clause — they ALWAYS fall to the sound uninterpreted-atom fallback (never-over-prove). Enumerated honestly: potentially weaker than today only for an int-valued operand whose TYPE was neutral at elaboration — corpus has none (int-typed operands route to `int_eq`, translated).
- **Task 2 Step 4 (emit):** registry-keyed struct clauses — saturated 3-arg spine → BEAM `==`/`/=` over spine args 2 and 3 (type argument DROPPED); bare/partial → curried fun wrapper per the existing decision-5 mechanism with innermost body `L == R` (the type param is accepted and ignored). Runtime bit-identical for every existing program (R7/R8a).
- **Tests (Task 2 red additions, assertions immutable once green):** `builtin_op_test.exs` (or the elab-side red file) gains: (i) struct_eq on two int literals folds to `True` under certified δ (polymorphic instantiation); (ii) struct_eq on ctor args stays NEUTRAL (the spine survives nf); (iii) R1-style pin: a user def named `struct_eq` with its own body is never builtin-folded. Elab red rows: `h == Z()` on a Nat operand lowers to a `struct_eq` spine headed by the quoted Nat type (NOT an error, NOT a prim).
- **Load-bearing UNCHANGED pins (R8a):** `ctor_guard_test.exs` 4/4 green byte-identical assertions — listed in Task 3 Step 4's accounting as an UNCHANGED pin, NOT a flip; `guard_lint_test.exs` §6 recovery rows likewise must keep their verdicts under the struct lowering.
- **Task 3/4 accounting updates:** op count 25 everywhere (Antigen env seeding via `Builtins.seed_ops/1` now carries 25 defs); the Task 4 delta arithmetic includes the A1 test additions; the grammar greps are unchanged (struct ops are ordinary globals). `ctor_guard_test.exs` is added to the "stays green, no flip" bucket of Task 3 Step 4.
- **New STOP conditions (R8, spec §4.7):** (a) any currently-green test changes behavior under the struct lowering (esp. `ctor_guard_test`, `guard_lint_test`); (b) meta-containing `l_type` readback at a live `build_binop` site; (c) `struct_eq` fold computing on non-int/float values. Decision 3's zero-newly-rejected prediction is RESTORED with A1 and remains a STOP condition.
