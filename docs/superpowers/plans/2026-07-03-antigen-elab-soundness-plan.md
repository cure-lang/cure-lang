# Antigen V3 — Elaborator Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** a new `elab/soundness` Antigen assay that closes the elaborator-soundness gap — for a well-typed surface program, every core definition the untrusted elaborator emits must independently type-check under the trusted kernel.

**Architecture:** A new `run` clause + `run/2` injection seam in `Antigen.Assays.Elab` walks `env.defs` from `Program.elaborate/1` and re-checks each def with the kernel (`infer` + `Conv`, with a `check` fallback for constructor bodies the kernel only checks). A fixed-catalog generator (`ElabComplete.soundness_challenges/0`) re-tags the completeness catalog, wired through the runner's `assay_module/1`.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** every commit uses `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` / `Cure.Elab.*` (TCB) edits.** The kernel + elaborator are reached read-only, the kernel only through the assay's `@real_kernel` map.
- **No new dependency, no `:meck`.** The `run/2` op-map (including `elaborate`) is the only injection path.
- **StreamData quarantine:** `lib/antigen/assays/elab.ex` and `lib/antigen/generators/elab_complete.ex` are inside the quarantined glob — the assay must contain NO `StreamData` literal (unchanged from today; the catalog generator is deterministic anyway).
- **One build/test run at any moment.** Never launch concurrent suites (a past concurrent full-suite run caused a kernel panic).
- **Tests are immutable** once written: reach green by changing assay/generator code, never by weakening/skipping/deleting a test (sole exception: a test proven to encode wrong behavior, argued explicitly first).
- **Run mix from the worktree root** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`.
- **Fuel floor** for any normalization in the assay is the committed `500_000` (matches `Antigen.Assays.Reflexivity`/`Term`).

## Reconciliations with the spec (resolved deviations, for the reviewer)

1. **§2 step-2 constructor exception → error-driven, not a structural recognizer.** Instead of a `ctor_needs_checking_mode?/2` that walks binders + calls `Inductive.param_count`, the assay calls `k.infer` and, on `{:error, {:ctor_requires_checking_mode, _}}`, falls back to `k.check(ctx, core, eval(ty))`. This mirrors the kernel's *own* condition (single source of truth — cannot drift from `Kernel.infer/2`) and automatically covers **any** non-inferable former, which §7.1 explicitly permits ("any other former found non-inferable during implementation"). Same observable behavior: param-bearing constructor bodies are checked, not mis-inferred; a genuine kernel rejection is still `{:core_ill_typed}`.
2. **§3.3 wiring → fixed catalog, not `default_gen`.** The existing elab family (`elab/completeness` etc.) is **not** in `Mix.Tasks.Antigen.default_gen/0`; it runs off the deterministic `ElabComplete.completeness_challenges/0` catalog via a dedicated test. `ElabComplete` exposes no `StreamData gen()`. V3 follows that established pattern: a new `soundness_challenges/0` catalog + `assay_module("elab/soundness")` wiring + a dedicated runner test. `default_gen` is left untouched (adding a lone fixed-catalog entry there would be inconsistent and require wrapping the catalog as a `Gen`).

## File structure

- **Modify** `lib/antigen/assays/elab.ex` — add the `elab/soundness` `run/1`+`run/2` clauses, `@real_kernel`, `@assay_fuel`, and the per-def decision procedure (private helpers). Existing clauses untouched.
- **Modify** `lib/antigen/generators/elab_complete.ex` — add `soundness_challenges/0` (re-tag the completeness catalog with `assay: "elab/soundness"`).
- **Modify** `lib/antigen/runner.ex` — add `assay_module("elab/soundness") -> Antigen.Assays.Elab`.
- **New** `test/antigen/assays/elab_soundness_test.exs` — the assay unit tests (Tasks 1–4).
- **Modify** `test/antigen/elab_completeness_test.exs` OR the new file — runner-wiring test (Task 5). (Plan uses the new file to keep V3 self-contained.)

## Interfaces (locked signatures)

- `Cure.Elab.Program.elaborate(src :: String.t()) :: {:ok, Env.t()} | {:error, term()}` (may raise).
- `Cure.Core.Env` (defined in `lib/cure/core/inductive.ex`): `empty/0`, `add_def(env, name, type_term, body_term) :: Env.t()` (arity-4; arity-5 adds quantities), `certify(env, name) :: Env.t()`, `get_def(env, name)`, `%Env{defs: %{name => %{type: Term, body: Term}}}`.
- `Cure.Core.Builtins.seed(env, exclude :: MapSet.t()) :: Env.t()` (2nd arg defaults to `MapSet.new()`) — seeds `Bool`/`Nat` inductive families, skipping any family whose name is in `exclude`. **Not** `[atom]` — passing a plain list crashes `MapSet.member?/2` with `FunctionClauseError` (verified: `MapSet.member?([], :x)` raises). Test helpers must call `Builtins.seed(Env.empty())` (bare, using the default) or `Builtins.seed(Env.empty(), MapSet.new())` — never `Builtins.seed(Env.empty(), [])`.
- `Cure.Core.Context.empty(env :: Env.t()) :: Context.t()`; `Context.length(ctx) :: non_neg_integer()`.
- `Cure.Core.Kernel.infer(ctx, term) :: {:ok, value} | {:error, term()}`; a parameter-bearing `{:ctor, name, args}` returns `{:error, {:ctor_requires_checking_mode, family}}`.
- `Cure.Core.Kernel.check(ctx, term, expected_value) :: :ok | {:error, term()}`.
- `Cure.Core.Eval.eval(term, value_env :: list()) :: value` (top-level: `Eval.eval(ty, [])`).
- `Cure.Core.Conv.conv_values?(v1, v2, depth :: non_neg_integer(), sig :: Env.t()) :: boolean()`.
- `Cure.Core.Normalise.with_fuel(fuel, (-> result)) :: result | :fuel_exhausted`.
- `Cure.Elab.Erase.has_hole?(term) :: boolean()`.
- `Antigen.Generators.ElabComplete.completeness_challenges() :: [Challenge.t()]` (each `%{kind: :elab_program, assay: "elab/completeness", payload: %{id, src}, label: :well_typed}`).

---

### Task 1: `elab/soundness` assay — seam + decision procedure (infer→Conv, hole-skip, reject/crash)

**Files:**
- Modify: `lib/antigen/assays/elab.ex`
- Test: `test/antigen/assays/elab_soundness_test.exs` (create)

**Interfaces:**
- Produces: `Antigen.Assays.Elab.run/1` and `run/2` for `assay: "elab/soundness"`.
- Consumes: `Program.elaborate/1`, `Kernel.infer/2`, `Conv.conv_values?/4`, `Eval.eval/2`, `Context.empty/1`, `Erase.has_hole?/1`, `Env`.

This task implements the full happy path + infer→Conv mismatch + reject + crash + hole-skip. The constructor `check`-fallback (Task 2) and fuel-wrap (Task 3) are added incrementally; Task 1's tests deliberately use **non-constructor, terminating** bodies so they neither need the fallback nor risk a hang.

- [ ] **Step 1: Write the failing tests**

Create `test/antigen/assays/elab_soundness_test.exs`:

```elixir
defmodule Antigen.Assays.ElabSoundnessTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Elab, Challenge}
  alias Cure.Core.{Env, Builtins}

  @bool {:data, :Bool, [], []}
  @nat {:data, :Nat, [], []}

  defp prog(src), do: Challenge.new(kind: :elab_program, assay: "elab/soundness",
                       label: :well_typed, payload: %{id: 1, src: src}, seed: 1)

  # A seeded env (Bool/Nat families present) so infer/eval resolve @bool/@nat.
  # NOTE: `Builtins.seed/2`'s 2nd arg is a MapSet (families to SKIP seeding),
  # not a list — `seed(Env.empty(), [])` crashes `MapSet.member?/2` with
  # FunctionClauseError (verified). Call the 1-arity form (uses the `MapSet.new()`
  # default) so every test below actually reaches the assay instead of crashing
  # in the fixture.
  defp seeded, do: Builtins.seed(Env.empty())

  # An op-map identical to @real_kernel EXCEPT `elaborate`, which returns a
  # synthetic env — the only way to feed the decision procedure a chosen env.defs.
  defp kernel_with_env(env) do
    %{elaborate: fn _src -> {:ok, env} end,
      infer: &Cure.Core.Kernel.infer/2, check: &Cure.Core.Kernel.check/3,
      conv: &Cure.Core.Conv.conv_values?/4, eval: &Cure.Core.Eval.eval/2}
  end

  test "baseline: a genuinely well-typed program re-checks sound (:ok)" do
    # id : Nat -> Nat = fn x -> x ; emitted core body {:lam,Nat,{:var,0}} infers cleanly.
    assert Elab.run(prog("mod P\nfn id(x: Nat) -> Nat = x\nend")) == :ok
  end

  test "type_annotation_wrong: body checkable but at a different type" do
    # def `bad`: body is Bool->Bool identity, DECLARED Nat->Nat. infer=vpi Bool Bool,
    # eval(declared)=vpi Nat Nat -> not convertible -> type_annotation_wrong.
    env = seeded()
          |> Env.add_def(:bad, {:pi, @nat, @nat}, {:lam, @bool, {:var, 0}})
    assert {:violation, {:type_annotation_wrong, :bad, _}} =
             Elab.run(prog("ignored"), kernel_with_env(env))
  end

  test "reject is NOT a V3 infection (belongs to elab/completeness)" do
    # A program the elaborator rejects -> {:error,_} from elaborate -> :ok here.
    assert Elab.run(prog("mod P\nfn oops(x: Nat) -> Nat = nonexistent_fn(x)\nend")) == :ok
  end

  test "elaborator crash is an infection" do
    k = %{elaborate: fn _ -> raise "boom" end, infer: &Cure.Core.Kernel.infer/2,
          check: &Cure.Core.Kernel.check/3, conv: &Cure.Core.Conv.conv_values?/4,
          eval: &Cure.Core.Eval.eval/2}
    assert {:violation, {:elaborator_raised, 1, _}} = Elab.run(prog("x"), k)
  end

  test "hole-bearing def is skipped, not infected" do
    # body has a hole; kernel would accept, but we skip it -> whole run :ok.
    env = seeded() |> Env.add_def(:h, {:pi, @nat, @nat}, {:lam, @nat, {:hole, :g}})
    assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
  end

  test "run/2 with the real op-map is byte-identical to run/1" do
    c = prog("mod P\nfn id(x: Nat) -> Nat = x\nend")
    assert Elab.run(c) == Elab.run(c, Elab.__real_kernel__())
  end
end
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: FAIL — no `run` clause for `assay: "elab/soundness"` (falls through / FunctionClauseError), and `Elab.__real_kernel__/0` undefined.

- [ ] **Step 3: Implement the assay clause + decision procedure**

In `lib/antigen/assays/elab.ex`, add the aliases and the new clauses (leave all existing clauses untouched). At the top, near the existing `alias`:

```elixir
alias Cure.Core.{Kernel, Conv, Eval, Context, Env}
alias Cure.Elab.Erase

@assay_fuel 500_000
@real_kernel %{
  elaborate: &Cure.Elab.Program.elaborate/1,
  infer: &Kernel.infer/2,
  check: &Kernel.check/3,
  conv: &Conv.conv_values?/4,
  eval: &Eval.eval/2
}
@doc false
def __real_kernel__, do: @real_kernel
```

Add the new `run` clauses (place with the other `run` clauses):

```elixir
def run(%Challenge{kind: :elab_program, assay: "elab/soundness"} = c),
  do: run(c, @real_kernel)

def run(%Challenge{kind: :elab_program, assay: "elab/soundness", payload: p}, k) do
  case safe_elaborate(k, p.src) do
    {:ok, env} -> check_all_defs(env, k)
    {:error, _} -> :ok                                   # reject -> elab/completeness' job
    {:raise, e} -> {:violation, {:elaborator_raised, p.id, e}}
  end
end
```

Add the private helpers (crash-normalizing wrapper mirrors the existing `elaborate/1`, but over the injected op):

```elixir
defp safe_elaborate(k, src) do
  case k.elaborate.(src) do
    {:ok, env} -> {:ok, env}
    {:error, e} -> {:error, e}
    other -> {:error, {:unexpected, other}}
  end
rescue
  ex -> {:raise, Exception.message(ex)}
catch
  kind, reason -> {:raise, {kind, reason}}
end

# Fold env.defs in a fixed key order; first infection wins (deterministic).
defp check_all_defs(env, k) do
  ctx = Context.empty(env)

  env.defs
  |> Enum.sort_by(fn {name, _} -> name end)
  |> Enum.find_value(:ok, fn {name, %{type: ty, body: body}} ->
    if Erase.has_hole?(body) do
      nil                                                # skip incomplete def
    else
      case check_one(k, ctx, name, ty, body) do
        :ok -> nil
        {:violation, _} = v -> v
      end
    end
  end)
end

# Task 1 form: infer -> Conv. (Task 2 adds the ctor check-fallback; Task 3 the fuel wrap.)
defp check_one(k, ctx, name, ty, body) do
  case k.infer.(ctx, body) do
    {:error, e} ->
      {:violation, {:core_ill_typed, name, e}}

    {:ok, inferred} ->
      ty_v = k.eval.(ty, [])
      if k.conv.(inferred, ty_v, Context.length(ctx), Context.signature(ctx)) do
        :ok
      else
        {:violation, {:type_annotation_wrong, name, %{inferred: inferred, declared: ty}}}
      end
  end
end
```

> Note: `Context.signature(ctx)` returns the `%Env{}` for δ-unfolding (mirrors how `Antigen.Assays.Term` obtains its `sig`). If `Context` exposes the env under a different accessor, use that (`Context.env/1`); the red-green run will surface the exact name.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: PASS (6 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/elab.ex test/antigen/assays/elab_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab/soundness assay — kernel re-checks emitted core (infer+Conv)"
```

---

### Task 2: Constructor `check`-fallback (parameter-bearing constructor bodies)

**Files:**
- Modify: `lib/antigen/assays/elab.ex`
- Test: `test/antigen/assays/elab_soundness_test.exs` (append)

**Interfaces:**
- Consumes: `Kernel.check/3`, `Kernel.infer/2`'s `{:error, {:ctor_requires_checking_mode, _}}` signal.

- [ ] **Step 1: Write the failing tests** — a well-typed parameter-bearing constructor body must NOT false-positive (Task 1's infer-only path would misreport it), and a mismatched one must still infect.

Append to `test/antigen/assays/elab_soundness_test.exs`:

```elixir
describe "constructor bodies (checking-mode fallback)" do
  # `Option(T)` is parameter-bearing; `Some(v)` bodies are inferable only in
  # checking mode. Kernel.infer returns {:error, {:ctor_requires_checking_mode, _}}.
  # Build the family + a sound and an unsound def directly in a seeded env.
  defp option_env do
    # A minimal parameter-bearing family F(a: Type) with ctor Mk(x: a) : F(a).
    #
    # Two details are load-bearing, verified against Kernel.check's `{:ctor,...}`
    # clause (which re-derives `actual = {:vdata, family, actual_params ++
    # actual_indices}` from `result_params`/`result_indices` and Conv-compares it
    # to the expected `{:vdata,...}}`):
    #   1. `declare/3`'s 3rd arg is `[ctor()]` (a LIST) — `declare(fam, ctor)`
    #      (bare map) makes `Enum.reduce` inside `declare/3` iterate the ctor
    #      MAP's `{key, value}` pairs instead of the ctor itself, crashing with
    #      MatchError on `%{name: cname} = c`.
    #   2. `result_params` must be `[{:var, 1}]` (mirrors Kernel's own
    #      `check_uniform_params/5` formula `{:var, num_args + (num_params - 1 -
    #      p)}` for Mk's 1 arg / F's 1 param), NOT `[]`. With `[]`, `check/3`
    #      re-derives `actual = {:vdata, :F, []}` (param dropped) instead of
    #      `{:vdata, :F, [Nat]}`, so `Conv.conv_values?`'s spine-length check
    #      fails `conv_spine?` even for the intentionally-SOUND `ok_mk` case
    #      below (0-length actual spine vs 1-length expected) — the "sound"
    #      test would falsely report a `{:core_ill_typed, ...}}` violation
    #      instead of `:ok`.
    fam = Cure.Core.Inductive.family(:F, [{:a, {:type, 0}}], [], 0)
    ctor = Cure.Core.Inductive.ctor(:Mk, [{:x, {:var, 0}}], [], [:present], [{:var, 1}])
    seeded() |> Cure.Core.Inductive.declare(fam, [ctor])
  end

  test "sound parameter-bearing constructor body re-checks :ok (uses check, not infer)" do
    # def ok_mk : F(Nat) = Mk(Z)   — well typed; infer alone would misreport it.
    env = option_env()
          |> Env.add_def(:ok_mk, {:data, :F, [@nat], []}, {:ctor, :Mk, [{:ctor, :Z, []}]})
    assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
  end

  test "mismatched constructor body still infects" do
    # def bad_mk : F(Bool) = Mk(Z)  — Z:Nat, but F(Bool) expects x:Bool -> reject.
    env = option_env()
          |> Env.add_def(:bad_mk, {:data, :F, [@bool], []}, {:ctor, :Mk, [{:ctor, :Z, []}]})
    assert {:violation, {:core_ill_typed, :bad_mk, _}} =
             Elab.run(prog("ignored"), kernel_with_env(env))
  end
end
```

- [ ] **Step 2: Run to verify the sound-ctor test fails**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: FAIL on "sound parameter-bearing constructor body" — Task 1's `check_one` calls only `infer`, which returns `{:error, {:ctor_requires_checking_mode, :F}}`, so a well-typed `Mk(Z)` is misreported as `{:core_ill_typed, :ok_mk, …}`. (The mismatched test may already pass — that is fine; the sound test is the red driver.)

- [ ] **Step 3: Implement the fallback**

In `lib/antigen/assays/elab.ex`, replace `check_one/5`'s `{:error, e}` arm so the checking-mode signal routes to `check`:

```elixir
defp check_one(k, ctx, name, ty, body) do
  case k.infer.(ctx, body) do
    {:error, {:ctor_requires_checking_mode, _}} ->
      # Introduction form the kernel only checks (parameter-bearing ctor, etc.):
      # check against the declared type. `check` re-derives the constructor's
      # actual family/args and Conv-compares internally, so a wrong annotation
      # is still caught.
      case k.check.(ctx, body, k.eval.(ty, [])) do
        :ok -> :ok
        {:error, e} -> {:violation, {:core_ill_typed, name, e}}
      end

    {:error, e} ->
      {:violation, {:core_ill_typed, name, e}}

    {:ok, inferred} ->
      ty_v = k.eval.(ty, [])
      if k.conv.(inferred, ty_v, Context.length(ctx), Context.signature(ctx)) do
        :ok
      else
        {:violation, {:type_annotation_wrong, name, %{inferred: inferred, declared: ty}}}
      end
  end
end
```

- [ ] **Step 4: Run to verify pass**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: PASS (all Task 1 + Task 2 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/elab.ex test/antigen/assays/elab_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab/soundness — check-fallback for checking-mode-only core (ctors)"
```

---

### Task 3: Fuel-bound every per-def check (`:fuel_exhausted` infection, no hang)

**Files:**
- Modify: `lib/antigen/assays/elab.ex`
- Test: `test/antigen/assays/elab_soundness_test.exs` (append)

**Interfaces:**
- Consumes: `Normalise.with_fuel/2`, `Env.certify/2`.

- [ ] **Step 1: Write the failing test** — an emitted def whose body δ-unfolds without converging must report `{:fuel_exhausted, name}` in bounded time, not hang.

Append:

```elixir
describe "fuel bound" do
  # A certified, non-normalizing global (`loop`'s body is a bare self-reference
  # `{:global, :loop}` — NOT an application). We certify it directly (bypassing
  # the totality checker that would normally block it) — the assay must NOT
  # assume elaboration prevents a non-normalizing emitted def.
  #
  # `loop`'s OWN check_one pass is deliberately clean (infer only ever reads a
  # global's DECLARED type — `infer(ctx,{:global,:loop})` = eval(@nat) = Nat,
  # matching its own declared `@nat`, no δ needed — so `:loop` itself is not
  # what infects). A second def, `probe`, is what forces δ: its declared type
  # is `Eq(Nat, loop, Z)` (an endpoint IS `loop`), and its body is `refl(Z)`.
  # Checking `probe` compares `inferred = Eq(Nat, Z, Z)` against `declared =
  # Eq(Nat, loop, Z)`; the middle endpoints (`Z` vs `loop`) are not both
  # neutral, so Conv falls to the general path, which `Normalise.whnf_value`s
  # BOTH sides — forcing the `{:nglobal, :loop}` neutral to δ-unfold.
  #
  # Verified by hand-tracing `Normalise.unfold_certified_head`: unfolding a
  # BARE self-reference (`Eval.eval({:global, :loop}, []) == {:vneutral,
  # {:nglobal, :loop}}}` — i.e. δ reproduces the IDENTICAL neutral each step,
  # no spine growth) makes every iteration O(1) (`spend_fuel` decrements once,
  # `spine` traverses a constant-depth term), so total work across the fuel
  # budget is O(fuel), not O(fuel²) — this is why the body is a bare global
  # reference and not a self-application: `{:app, {:global, :loop}, {:ctor,
  # :Z, []}}` would (a) make `loop`'s OWN check_one infer fail structurally
  # with `:not_a_function` BEFORE any δ (its declared type `@nat` isn't a Π,
  # so applying it is ill-typed — this never reaches δ/fuel at all, the
  # original bug in this test), and (b) even redirected through `probe`,
  # would re-grow the neutral's `:napp` spine by one layer per δ-step, making
  # `spine/2`'s per-step traversal O(step), i.e. O(fuel²) total — likely
  # multiple minutes at fuel = 500_000, blowing the 30s `Task.await` budget.
  test "non-normalizing emitted def reports :fuel_exhausted, does not hang" do
    env =
      seeded()
      |> Env.add_def(:loop, @nat, {:global, :loop})
      |> Env.certify(:loop)
      |> Env.add_def(:probe, {:eq, @nat, {:global, :loop}, {:ctor, :Z, []}},
                      {:refl, {:ctor, :Z, []}})

    task = Task.async(fn -> Elab.run(prog("ignored"), kernel_with_env(env)) end)
    assert {:violation, {:fuel_exhausted, :probe}} = Task.await(task, 30_000)
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: FAIL — without the fuel wrap, `Conv.conv_values?` δ-unfolds `loop` under unbounded fuel while comparing `probe`'s inferred vs. declared type, and the test times out at 30s (Task.await raises).

- [ ] **Step 3: Implement the fuel wrap**

In `check_all_defs/2`, wrap the per-def `check_one` call:

```elixir
      case Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> check_one(k, ctx, name, ty, body) end) do
        :ok -> nil
        :fuel_exhausted -> {:violation, {:fuel_exhausted, name}}
        {:violation, _} = v -> v
      end
```

(Replace the previous unwrapped `case check_one(...)` block. `with_fuel` returns `check_one`'s value, or `:fuel_exhausted` if the reduction loop throws.)

- [ ] **Step 4: Run to verify pass**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: PASS (all tests; the fuel test returns within seconds).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/elab.ex test/antigen/assays/elab_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab/soundness — fuel-bound per-def checks; :fuel_exhausted class"
```

---

### Task 4: Generator `soundness_challenges/0` + runner wiring

**Files:**
- Modify: `lib/antigen/generators/elab_complete.ex`
- Modify: `lib/antigen/runner.ex`
- Test: `test/antigen/assays/elab_soundness_test.exs` (append)

**Interfaces:**
- Produces: `ElabComplete.soundness_challenges() :: [Challenge.t()]`; `assay_module("elab/soundness")`.
- Consumes: `ElabComplete.completeness_challenges/0`, `Runner.replay_one/1`.

- [ ] **Step 1: Write the failing tests**

Append:

```elixir
describe "generator + runner wiring" do
  alias Antigen.Generators.ElabComplete
  alias Antigen.Runner

  test "soundness_challenges re-tags the completeness catalog" do
    cs = ElabComplete.soundness_challenges()
    assert cs != []
    assert Enum.all?(cs, fn c -> c.kind == :elab_program and c.assay == "elab/soundness" end)
    # same programs as completeness (same ids), only the assay tag differs
    assert Enum.map(cs, & &1.payload.id) ==
             Enum.map(ElabComplete.completeness_challenges(), & &1.payload.id)
  end

  test "runner dispatches elab/soundness to the Elab assay (replay_one)" do
    [c | _] = ElabComplete.soundness_challenges()
    # every catalog program is construction-guaranteed well-typed -> sound
    assert Runner.replay_one(c) == :ok
  end

  test "the whole soundness catalog re-checks clean under the real kernel" do
    assert Enum.all?(ElabComplete.soundness_challenges(), fn c ->
             Runner.replay_one(c) == :ok
           end)
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: FAIL — `ElabComplete.soundness_challenges/0` undefined; `assay_module("elab/soundness")` has no clause (FunctionClauseError in `replay_one`).

- [ ] **Step 3: Implement the generator + wiring**

In `lib/antigen/generators/elab_complete.ex`, add (next to `completeness_challenges/0`):

```elixir
@spec soundness_challenges() :: [Challenge.t()]
def soundness_challenges do
  Enum.map(completeness_challenges(), fn c -> %{c | assay: "elab/soundness"} end)
end
```

In `lib/antigen/runner.ex`, add a clause alongside the other `elab/*` entries (after `assay_module("elab/erasure")`):

```elixir
defp assay_module("elab/soundness"), do: Antigen.Assays.Elab
```

- [ ] **Step 4: Run to verify pass**

Run: `MIX_ENV=test mix test test/antigen/assays/elab_soundness_test.exs`
Expected: PASS (all tests). If a catalog program legitimately fails soundness, that is a REAL infection, not a test bug — STOP and report it (do not weaken the test); it is exactly what V3 exists to find.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/elab_complete.ex lib/antigen/runner.ex test/antigen/assays/elab_soundness_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): elab/soundness catalog generator + runner dispatch wiring"
```

---

### Task 5: Full-suite verification + regression

**Files:** none (verification only).

- [ ] **Step 1: Run the full suite once** (single authorized run — no concurrent builds)

Run: `MIX_ENV=test mix test`
Expected: all pass; count = prior baseline + the new `elab_soundness_test.exs` rows. The existing `test/antigen/elab_completeness_test.exs` and `test/antigen/architecture_test.exs` stay green (the assay adds no `StreamData` literal; existing `elab/*` clauses untouched).

- [ ] **Step 2: Confirm the StreamData quarantine**

Run: `MIX_ENV=test mix test test/antigen/architecture_test.exs`
Expected: PASS.

- [ ] **Step 3: Smoke the campaign path is unbroken**

Run: `MIX_ENV=test mix antigen --count 200`
Expected: completes; `default_gen` unchanged so behavior matches pre-V3 (V3 runs via the catalog, not the random campaign — by design, per Reconciliation #2).

- [ ] **Step 4: Revert any test-run seed side-effect**

Run: `git status --short`; if `test/antigen/seeds.sexp` shows modified, `git checkout -- test/antigen/seeds.sexp`. Confirm the tree is clean.

- [ ] **Step 5: No commit** (verification task; results go in the completion report).

---

## Self-review

**Spec coverage:** §2 decision procedure (infer→Conv, ctor check-fallback, fuel, hole-skip) → Tasks 1–3; §3.1 assay clause + §3.2 `run/2` seam (incl. `elaborate`) → Task 1; §3.3 generator + wiring → Task 4 (reconciled to the fixed-catalog pattern); §5 tests #1–#9 distributed: #1 baseline (T1), #2 ill-typed core (T1), #3 ctor controls (T2), #4 reject (T1), #5 crash (T1), #6 hole-skip (T1), #7 fuel (T3), #8 runner wiring (T4), #9 determinism/regression (T1 `__real_kernel__` test + T5 full suite). §6 invariants pinned across tasks; §8 non-goals respected (no elaborator fix, no default_gen change, no new generator logic).

**Placeholder scan:** none — every step has concrete code/commands/expected output. The one remaining "verify during red-green" note (`Context.signature/1` vs `Context.env/1` for the δ-unfolding `sig` argument) is an explicit, bounded implementer check with a named fallback, not an open-ended TODO — and has been confirmed correct as written: `Context.signature/1` exists exactly as documented in Interfaces (`lib/cure/core/context.ex`), so the fallback path is not expected to trigger. The fuel-test body shape is no longer a "verify during red-green" placeholder — Task 3's construction (`loop`/`probe` two-def shape) is fully concrete and hand-verified against `Kernel.infer`, `Eval.eval`, `Normalise.unfold_certified_head`, and `Conv.conv_val?` (see the test's inline commentary), including the O(fuel) vs. O(fuel²) performance argument for why the body is a bare self-reference rather than a self-application.

**Type consistency:** `run/2` op-map keys `elaborate/infer/check/conv/eval` identical in `@real_kernel`, `kernel_with_env/1`, and the crash test across Tasks 1–4. Infection tags `{:core_ill_typed, name, e}`, `{:type_annotation_wrong, name, %{inferred, declared}}`, `{:elaborator_raised, id, e}`, `{:fuel_exhausted, name}` consistent between spec §2/§3, the code, and the tests. `soundness_challenges/0` produced in Task 4, consumed by its own tests.

**TDD discipline:** every task writes red tests first, runs them red (with the exact expected failure), implements minimally, runs green, commits. Task 2's red driver is the *sound* ctor test (the mismatch may pass early — flagged). Task 3's red driver is a timeout/hang guarded by `Task.await`. No test is weakened to reach green; a real catalog infection in Task 4 is an explicit STOP-and-report.
