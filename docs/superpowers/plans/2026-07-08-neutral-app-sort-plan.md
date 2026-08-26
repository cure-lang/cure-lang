# Neutral-Application Sort Inference (Sigma D1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the D1 kernel enabler — `check_motive_wf` accepts neutral type-valued applications (`b(first(p))`-shaped motives) via a reify+infer clause, plus the §2.4 defensive `{:pair,…}` infer clause — spec `docs/superpowers/specs/tooling/2026-07-08-neutral-app-sort-design.md` (hardened `fb68e84`).

**Architecture:** Exactly two new clauses in `lib/cure/core/kernel.ex` (TCB — blanket-approved as Agda/Lean-aligned, FULL verification gate mandatory): an `infer_type_value_sort` clause that reifies the neutral application signature-aware and accepts only if the kernel's own term-level `infer/2` yields `{:vtype, l}`, and a one-line defensive `infer(_, {:pair,_,_})` rejection. **[AMENDED 2026-07-09, spec §7]** Plus Task 1b, the E-layer enabler execution uncovered: type-position implicit insertion in the return-type lowering (`lib/cure/elab/declarations.ex` + one public wrapper in `elaborator.ex`) — without it the elaborator hands the kernel an under-applied motive and the probe can never elaborate. Plus: unit tests, an Antigen antibody (a property-based `DepMatch` accepting variant + fixed accept/reject pins + a Malformed reject seed — see Task 2's gap note), and a new `sg` differential-oracle cluster.

**Tech Stack:** Elixir, `Cure.Core.{Kernel,Quote,Context,Eval}`, ExUnit, Antigen, `mix cure.oracle` + idris2.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. **Never read or edit files under the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/…` — an earlier agent did and produced confidently wrong facts (spec §0's stale-scout warning).**
- **TCB scope:** `lib/cure/core/kernel.ex` gains exactly the two spec'd clauses; NOTHING else under `lib/cure/core/` changes. **[AMENDED 2026-07-09, spec §7]** `lib/cure/elab/*` changes are authorized for Task 1b ONLY and confined to: `lib/cure/elab/declarations.ex` (`function_signature` ctx threading + `idx_to_core` delegation branch + `implicit_global?` helper) and `lib/cure/elab/elaborator.ex` (one narrow public wrapper). Still NO changes to `lib/cure/types/*`, `lib/cure/compiler/*` (non-dependent decoy pipeline).
- Strict red-green TDD; tests behavioral and immutable once green. ONE mix command at a time, ever (past concurrent run caused a kernel panic). Full gates run ONCE, alone, in Task 4.
- Git: commit per task; EVERY commit `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO trailers; explicit-pathspec staging only.
- **`mix cure.oracle` may be run exactly once, in Task 3, with the cluster argument `sg` only** (`mix cure.oracle sg`) — it regenerates only `test/oracle/sg/verdicts.json` (spec §3.4, review-verified). Never run it bare or with another cluster. If it unexpectedly modifies any OTHER cluster's verdicts.json (`git status` check after), `git checkout -- test/oracle/<other>/verdicts.json` and STOP-and-report.
- Prereq: `~/Develop/Idris2/build/exec/idris2` must exist (the oracle shells out to it). If missing → STOP-and-report (do not skip the oracle task).
- STOP-and-report: any oracle divergence on sg01 (either direction); any existing test failing at any point; any need to touch a third place in kernel.ex; any need to touch an elab file beyond the two named in Task 1b; the accept-probe still rejecting after Task 1b lands (kernel-only rejection after Task 1 is EXPECTED — spec §7.1).

## File Structure

- `lib/cure/core/kernel.ex` — the two clauses (Task 1).
- `lib/cure/elab/declarations.ex` — Task 1b [spec §7]: `function_signature` builds+threads a ctx into return-type lowering; `idx_to_core/5` delegation branch; `implicit_global?/2` helper.
- `lib/cure/elab/elaborator.ex` — Task 1b [spec §7]: one narrow public wrapper `elaborate_implicit_global_app/5`.
- `test/cure/elab/dependent_eliminator_test.exs` — NEW: surface probes + hand-built-Core negatives (Tasks 1 + 1b; single combined commit at end of 1b — see Task 1 Step 7).
- `lib/antigen/generators/dep_match.ex` — one new `case_challenge/0` accepting arm, `neutral_app_motive_case/0` (Task 2).
- `lib/antigen/generators/malformed.ex` — one new reject seed in `malformation/0` (Task 2).
- `test/antigen/neutral_app_motive_test.exs` — NEW: accept/reject antibody pins through the real kernel (Task 2).
- `test/oracle/sg/sg01_dependent_second.{cure,idr}` + generated `verdicts.json` — NEW (Task 3).

---

### Task 1: the two kernel clauses, with staged red evidence

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer_type_value_sort` clauses at ~606-665; `infer/2` clauses region)
- Test: `test/cure/elab/dependent_eliminator_test.exs` (new)

- [ ] **Step 0: Pre-flight (read-only)**

1. `Quote` is already in `kernel.ex`'s alias list (`kernel.ex:19`: `alias Cure.Core.{Certificate, Context, Conv, Env, Eval, Inductive, Normalise, Quote, Term, Universe}` — settled by review, re-verify with `grep "alias Cure.Core" lib/cure/core/kernel.ex` in case a prior task edits it). Use the bare `Quote.reify/3` call in the new clause (no fully-qualified fallback needed, no new alias line — keeps the diff to the two clauses).
2. Confirm `Quote.reify/3`'s public signature `reify(value, depth \\ 0, sig \\ nil)` (`lib/cure/core/quote.ex:40`) and that `{:vneutral, n}` dispatches to the private `reify_neutral/3` (quote.ex:76).
3. Confirm `infer/2` has no `{:pair,_,_}` clause (grep `def infer` clause heads).
4. Record the current `HEAD` commit hash (`git rev-parse HEAD`) as `<pre-batch-commit>` — Task 4's final-verification diffs need a stable reference point *before* Task 1's commit; note it down now rather than reconstructing it later from `git log`.

- [ ] **Step 1: Write the failing tests**

```elixir
defmodule Cure.Elab.DependentEliminatorTest do
  @moduledoc """
  Spec 2026-07-08-neutral-app-sort (Sigma D1): motives applying a type-family
  head — `b(first(p))` — sort via reify+infer (kernel.ex napp clause); adversarial
  motives reject cleanly (defensive {:pair,…} infer clause). Surface probes drive
  Program.elaborate; the §2.4 crash probe hand-builds Core against Kernel.infer.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Program

  @probe """
  mod P
    type Nat = Z | S(Nat)
    type MySigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> MySigma(a, b)
    fn first({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> a = match p
      mk_pair(x, y) -> x
    fn second({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> b(first(p)) = match p
      mk_pair(x, y) -> y
    fn run_second() -> Nat = second(mk_pair(Z(), S(Z())))
  end
  """

  # RED THROUGH TASK 1 (expected — spec §7.1): the implicit-param probe needs
  # Task 1b's type-position implicit insertion; kernel-only it still rejects
  # :bad_motive on the under-applied motive. Goes green at Task 1b Step 4.
  test "D1 probe: dependent second projection elaborates (b(first(p)) motive)" do
    assert {:ok, _env} = Program.elaborate(@probe)
  end

  # Kernel-enabler pin (green at Task 1 Step 6, BEFORE Task 1b): the identical
  # probe with EXPLICIT type params lowers `b(first(a, b, p))` to a full spine,
  # so it isolates the napp kernel clause from the Task 1b elaborator fix —
  # executor-verified accepted with the two clauses alone (spec §7.1).
  @explicit_probe """
  mod P
    type Nat = Z | S(Nat)
    type MySigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> MySigma(a, b)
    fn first(a: Type, b: (a) -> Type, p: MySigma(a, b)) -> a = match p
      mk_pair(x, y) -> x
    fn second(a: Type, b: (a) -> Type, p: MySigma(a, b)) -> b(first(a, b, p)) = match p
      mk_pair(x, y) -> y
  end
  """

  test "kernel-enabler pin: explicit-param dependent second projection elaborates" do
    assert {:ok, _env} = Program.elaborate(@explicit_probe)
  end

  test "D1 probe: second(mk_pair(x, y)) reduces/runs correctly on BEAM (spec §4 item 2)" do
    # Monomorphic instance: a := Nat, b := (constant) Nat, x = Z(), y = S(Z()) — b's
    # implicit is solved from the pair literal (b(x) =?= typeof(y) = Nat), the same
    # higher-order/Miller-pattern inference already landed and exercised by
    # `test/oracle/dep/dep07_higher_order_family.cure`'s `the2`. Also pins the
    # `first(mk_pair(x,y)) -> x` ι-reduction inside branch checking (spec §4 item 2).
    {:ok, env} = Program.elaborate(@probe)
    # `functions:` must list every def actually called, not just the entry point —
    # `run_second` calls `second`, which calls `first` — confirmed against
    # `test/cure/elab/first_class_function_test.exs`'s multi-name `functions:` lists
    # (e.g. `[:ap, :inc, :g]`); `module_forms/3` (emit.ex:80-89) emits forms only
    # for the exact names given, no transitive-callee closure.
    {:ok, mod} =
      Cure.Elab.Emit.compile_and_load(env,
        module: :"Cure.DependentEliminatorProbe",
        functions: [:run_second, :second, :first]
      )
    # Runtime ctor encoding verified against test/cure/elab/auto_generalize_test.exs
    # and conditional_test.exs: nullary ctors compile to bare atoms (Z -> :Z),
    # ctors with args to tagged tuples (S(Z()) -> {:S, :Z}).
    assert apply(mod, :run_second, []) == {:S, :Z}
  end

  test "negative: non-type-valued head in type position still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({a: Type}, {b: (a) -> Type}, {g: (a) -> Nat}, p: MySigma(a, b)) -> g(first(p)) = match p
        mk_pair(x, y) -> y
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  test "negative: ill-typed argument to the type-family head still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type Other = Mk
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({b: (Other) -> Type}, p: MySigma(Nat, ?)) -> b(Z()) = Z()
    end
    """

    # The exact surface framing may need adjustment (see latitude note); the
    # requirement is: a type-position application whose argument does not match
    # the head's domain is rejected, not accepted.
    assert {:error, _} = Program.elaborate(src)
  end

  # §2.4 crash probe: hand-built Core, driven straight at Kernel.infer. The
  # non-function variant applies the motive's own Nat-typed binder (dies at
  # ensure_pi). The PAIR variant MUST use a FUNCTION-typed head (spec §7.6,
  # executor-verified): only then does infer get past ensure_pi and reach the
  # pair argument — check against the non-Σ domain falls through to infer on a
  # bare {:pair,…}, the exact §2.4 crash site. A Nat-typed head applied to a
  # pair never reaches the pair and proves nothing about the defensive clause.
  describe "§2.4 adversarial motives reject cleanly (never crash)" do
    defp nat_env do
      {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
      env
    end

    defp bad_motive_case(motive) do
      {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}
    end

    test "motive applying a non-function head rejects :bad_motive" do
      ctx = Context.empty(nat_env())
      nat = {:data, :Nat, [], []}
      motive = {:lam, nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
      assert {:error, :bad_motive} = Kernel.infer(ctx, bad_motive_case(motive))
    end

    test "motive applying a function-typed head to a pair literal rejects :bad_motive (no FunctionClauseError)" do
      env = nat_env()
      nat = {:data, :Nat, [], []}
      # ctx binder: b : (Nat) -> Type (same construction as the Task 2 accept
      # pin). Under the motive's own lam binder, b reads as {:var, 1}.
      ctx = Context.extend(Context.empty(env), Eval.eval({:pi, nat, {:type, 0}}, []))
      motive = {:lam, nat, {:app, {:var, 1}, {:pair, {:ctor, :Z, []}, {:ctor, :Z, []}}}}
      assert {:error, :bad_motive} = Kernel.infer(ctx, bad_motive_case(motive))
    end
  end
end
```

Latitude (report every use): the two surface negatives pin *rejection*, not a specific tag — if a fixture fails to parse/elaborate for an incidental surface reason (e.g. the `?`-placeholder or implicit framing in the third test), adjust the FIXTURE to the nearest expressible form that still applies a wrong-domain / non-type head in type position; if no such surface form exists, replace that test with a hand-built-Core equivalent in the §2.4 describe block and note it. The probe test and both §2.4 tests are NOT adjustable. If the ctor atom for the hand-built cases is namespaced (`:"P.Z"`), resolve it the way `test/cure/elab/named_implicit_tail_test.exs`'s `ctor_atom/2` helper does. The runtime-execution test's `run_second() -> Nat = second(mk_pair(Z(), S(Z())))` wrapper relies on `b`'s implicit being solved from the pair literal (Miller-pattern inference, landed and precedented by `test/oracle/dep/dep07_higher_order_family.cure`'s `the2`) — if this exact call needs an explicit type annotation or different argument shape to elaborate, adjust the wrapper (not the assertion on the returned runtime value) to the nearest form that still calls `second` on a genuine `mk_pair` instance; this test is NOT droppable (spec §4 item 2 / §6 criterion 1 require it) even if its exact surface needs adjustment.

**Review-found gap:** spec §4 explicitly requires a distinct test — "`second(mk_pair(x, y))` reduces/runs correctly (BEAM execution of a monomorphic instance...)" — separate from mere elaboration success, and §6 acceptance criterion 1 says the probe must "elaborate AND RUN." The original plan draft only asserted `Program.elaborate(@probe)` succeeds, never compiling/running it — this is now fixed by the `@probe`'s added `run_second` wrapper and the new test above, using the `Cure.Elab.Emit.compile_and_load/2` + `apply/3` pattern (verified precedent: `test/cure/elab/bool_connective_codegen_test.exs`).

- [ ] **Step 2: Run — capture the pre-change baseline**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs`
Expected TODAY (7 tests): the D1 probe FAILS (`{:error, :bad_motive}` where `{:ok, _}` expected); the runtime-execution test ALSO FAILS (it pattern-matches `{:ok, env} = Program.elaborate(@probe)`, which today returns `{:error, :bad_motive}` — a `MatchError`, not a runtime-value mismatch); the explicit-param kernel pin FAILS (`:bad_motive` — the napp clause doesn't exist yet); both surface negatives PASS (already reject); **both §2.4 tests PASS** (the napp value hits the fallthrough → `:bad_motive` — the crash path does not exist yet; the pair variant's function-typed head changes nothing at baseline because motive-wf never reifies+infers without the napp clause). 4 pass / 3 fail. Record all seven outcomes.

- [ ] **Step 3: Add ONLY the `infer_type_value_sort` napp clause**

Insert after the `{:vneutral, {:nvar, level}}` clause (~kernel.ex:613-620), exactly as spec §2:

```elixir
  # A neutral APPLICATION is a valid type iff the kernel's own term-level
  # judgement says so: reify the spine back to a term (signature-aware, so a
  # {:vdata,…} argument keeps its param/index split — quote.ex split_data_args)
  # and infer it. infer/2's {:app, f, a} rule resolves the head's type (ctx var
  # or signature global), CHECKS each argument against the instantiated Pi
  # domain, and returns the codomain — full validation, nothing trusted from
  # the (untrusted) elaborator that assembled the motive. Accept only a
  # {:vtype, l} result: `b(first(p))` with `b : (a) -> Type` sorts at l; a
  # non-type codomain stays :not_a_type_value.
  defp infer_type_value_sort(ctx, {:vneutral, {:napp, _, _} = neutral}) do
    term = Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))

    case infer(ctx, term) do
      {:ok, {:vtype, level}} -> {:ok, level}
      _ -> {:error, :not_a_type_value}
    end
  end
```

(`Quote` is aliased per Step 0.1 — use the bare call as written above.)

- [ ] **Step 4: Run — capture the mid-point crash (the §2.4 necessity proof)**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs`
Expected NOW **[AMENDED 2026-07-09 — the original prediction that the probe passes here was WRONG; spec §7.1]**: the D1 probe and runtime-execution tests STILL FAIL with `:bad_motive` — the elaborator hands the kernel an under-applied motive (`first` applied to 1 of 3 binders); they go green only at Task 1b. The explicit-param kernel pin NOW PASSES (its full-spine motive sorts via the new clause — this is Task 1's honest green). The non-function-head §2.4 test still passes (`ensure_pi` on a Nat head fails inside `infer` → `:not_a_type_value` → `:bad_motive`). **The pair-literal §2.4 test (function-typed head, per the corrected Step 1 code) CRASHES with `FunctionClauseError` (no `infer/2` clause for `{:pair,…}`)**. Capture the exact exception — this is the red evidence that the defensive clause is load-bearing, not decorative.

- [ ] **Step 5: Add the defensive `infer` clause**

Next to `infer/2`'s `{:fst,_}`/`{:snd,_}` clauses:

```elixir
  # Pairs are check-only (see check/3 against {:vsigma,…}); an infer position can
  # only be reached by an adversarial reified motive (spec 2026-07-08-neutral-app-
  # sort §2.4) — reject explicitly instead of crashing on a missing clause.
  def infer(_ctx, {:pair, _, _}), do: {:error, :pair_not_inferable}
```

- [ ] **Step 6: Run to verify the kernel-provable set green**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs` — expected **5 of 7 pass**: explicit-param pin + both surface negatives + both §2.4 tests green; the implicit-param probe and runtime tests remain RED with `:bad_motive` (spec §7.1 — they are Task 1b's red baseline, captured here). Anything else failing, or the two reds failing with a DIFFERENT tag, = STOP.
Then (one at a time): `mix test test/cure/core/` — expected all pass (273+); no elab-wide run yet (two in-file reds are expected until Task 1b).

- [ ] **Step 7: NO commit yet — proceed to Task 1b**

**[AMENDED 2026-07-09]** The kernel clauses and the test file commit TOGETHER at the end of Task 1b (its Step 5): the probe/runtime tests live in the same file and are red until the elaborator fix lands, and committing a red test file violates red-green discipline. The staged evidence from Steps 2/4/6 must be preserved verbatim for the combined commit's report.

---

### Task 1b: type-position implicit insertion (spec §7 amendment, 2026-07-09)

**Why:** with both kernel clauses in, the implicit-param probe still rejects because `function_signature` lowers the return annotation via `idx_to_core`, whose global-application fallthrough builds a bare explicit-args spine — no implicit insertion (spec §7.1, verified `declarations.ex:915-916`). The motive reaching the kernel is `{:app, {:var,2}, {:app, {:global,:first}, {:var,0}}}` — `first` applied to 1 of 3 binders. This task makes type-position lower the SAME spine term position does. E-layer only (untrusted; kernel re-checks everything).

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (one public wrapper next to `elaborate_implicit_app_bidirectional/6`, ~line 4116)
- Modify: `lib/cure/elab/declarations.ex` (`function_signature` ~92-116; `idx_to_core` clauses ~860-1001; `map_idx_to_core`)
- Test: `test/cure/elab/dependent_eliminator_test.exs` (no new tests — the probe + runtime tests written in Task 1 ARE this task's red, captured red at Task 1 Step 6)

**Interfaces:**
- Consumes: `elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx, expected \\ nil)` (private, elaborator.ex:4116) → `{:ok, term, result_type} | {:error, _}`; `build_context(env, telescope)` (declarations.ex, body-pass precedent at :78); `Env.get_def(env, atom)` → `%{type: _, quantities: _} | nil`; quantities atoms are `:erased`/`:present` (solve_arg heads, elaborator.ex:4046-4051).
- Produces: `Cure.Elab.Elaborator.elaborate_implicit_global_app(env, name, arg_asts, names, ctx)` (new public, thin delegate); `idx_to_core/5` (ctx as 5th arg, default `nil`).

**Registration-pass fact (orchestrator-verified, spec §7.4 discharged):** `register_signature` (declarations.ex:36-40) runs `Env.add_def(env, sig.name, sig.pi, {:hole, "__pending__"}, sig.quantities)` in declaration order (program.ex `register_pass`/`register_pass_lean`), so when `second`'s signature lowers, `Env.get_def(env, :first)` already returns its `%{type, quantities}`. `function_signature` runs again in the body pass with the same type environment — the delegation consults type+quantities only, so both passes compute the same `return_core`.

- [ ] **Step 1: Confirm the red (no mix run needed — carried from Task 1 Step 6)**

The probe and runtime tests fail with `:bad_motive`. If Task 1 Step 6 was not run immediately before this task, re-run `mix test test/cure/elab/dependent_eliminator_test.exs` once to re-capture: 5/7, the two reds `:bad_motive`.

- [ ] **Step 2: Add the public wrapper in `elaborator.ex`**

Next to `elaborate_implicit_app_bidirectional/6` (~4116):

```elixir
  @doc """
  Type-position entry for implicit insertion (spec 2026-07-08 §7): elaborate an
  application of a global that carries implicit (erased) parameters, from its
  SURFACE argument ASTs, in the caller's typing context. Used by the
  return-type lowering in `Cure.Elab.Declarations` — term position reaches the
  same machinery via `elaborate_named_call`. The kernel re-checks the assembled
  signature, so nothing unsound rests on this path.
  """
  def elaborate_implicit_global_app(env, name, arg_asts, names, ctx) do
    elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx)
  end
```

- [ ] **Step 3: Thread a ctx through the return-type lowering in `declarations.ex`**

3a. `function_signature` — build the context and pass it (ONLY here; every other `idx_to_core` caller is untouched and gets `nil` via the default):

```elixir
    with {:ok, telescope, quantities, scope} <- elaborate_param_telescope(params, env),
         ctx = build_context(env, telescope),
         {:ok, return_core} <- idx_to_core(return_expr, scope, nil, env, ctx) do
```

3b. Give `idx_to_core` a 5th parameter with a default header (Elixir multi-clause default), converting every existing clause head to 5 args:

```elixir
  defp idx_to_core(ast, scope, fam, env, ctx \\ nil)
```

- The two `{:variable, …}` clauses and the fallback clause: add `_ctx`, bodies unchanged.
- The `{:sigma_type, …}`, `{:pi_type, …}`, and `{:attribute_access, …}` clauses: add `_ctx`, bodies unchanged — their sub-lowerings keep calling the 4-arg form (ctx `nil`): crossing a binder-introducing form NULLs the ctx (spec §7.3 item 4 — the scope gains binders the kernel context lacks; a stale ctx would mis-frame de Bruijn). `arrow_to_pi` likewise stays 4-arg.
- The `{:function_call, …}` clause: thread ctx into the argument lowering and add the delegation branch BEFORE args are lowered (the delegate elaborates surface ASTs itself):

```elixir
  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env, ctx) do
    if Keyword.get(fmeta, :function_type) do
      arrow_to_pi(args, scope, fam, env)
    else
      name = Keyword.fetch!(fmeta, :name)
      atom = String.to_atom(name)

      # Type-position implicit insertion (spec §7): a term-level global whose
      # signature carries erased (implicit) parameters cannot lower as a bare
      # explicit-args spine — the kernel would see an under-applied application
      # (the `b(first(p))` motive gap). With a typing context threaded in
      # (return-type lowering only), delegate the whole application to the
      # term-position machinery. A local binder of the same name shadows the
      # global (mirrors the applied-bound-var cond branch below), and families/
      # ctors never carry def quantities, so this misses them by construction.
      if ctx != nil and Enum.find_index(scope, &(&1 == name)) == nil and
           implicit_global?(env, atom) do
        with {:ok, term, _result_type} <-
               Cure.Elab.Elaborator.elaborate_implicit_global_app(env, atom, args, scope, ctx) do
          {:ok, term}
        end
      else
        with {:ok, core_args} <- map_idx_to_core(args, scope, fam, env, ctx) do
          # …existing cond (qualified / bound-var / family / ctor / bare spine)
          # byte-for-byte unchanged…
        end
      end
    end
  end
```

3c. `map_idx_to_core` gains the same defaulted 5th param and threads it to `idx_to_core/5` — this is what routes the ctx to NESTED argument positions, the probe's actual shape (`b(first(p))`: head `b` is a bound var, the implicit-carrying global `first` is one level down; spec §7.3 item 3).

3d. The helper:

```elixir
  # A term-level global whose registered signature carries at least one erased
  # (implicit) parameter — the only shape the bare-spine lowering mis-handles.
  # Families and constructors are not defs, so they return false here. Mirrors
  # the precedent `implicit_def?/2` (elaborator.ex:1278-1283) exactly, including
  # its `is_list(q)` guard: `Env.add_def/4` (the 4-arg form used by some Antigen
  # synthetic environments, e.g. `lib/antigen/generators/closure_env.ex`) defaults
  # quantities to `nil`, and `:erased in nil` raises (`nil` is not Enumerable) —
  # the guard is required for the same reason it is in the precedent function.
  defp implicit_global?(env, atom) do
    case Env.get_def(env, atom) do
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end
```

(Verified: `Env.get_def/2` (`lib/cure/core/inductive.ex:54-55` — `Cure.Core.Env` is defined there, NOT in a separate `env.ex`; no such file exists in this worktree) returns `nil` on a miss, never raises — the `_ ->` clause above covers both the miss and the `nil`-quantities case.)

- [ ] **Step 4: Run to verify all green**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs` — expected **7 tests, 0 failures** (the probe elaborates; `run_second()` returns `{:S, :Z}`).
Then (one at a time): `mix test test/cure/elab/` — expected all pass (~440+, includes the new 7; any pre-existing elab test failing = STOP, this is the blast-radius gate for the threading change); `mix test test/cure/core/` — expected all pass.

- [ ] **Step 5: Combined commit (Task 1 + Task 1b)**

```bash
git add -- lib/cure/core/kernel.ex lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex test/cure/elab/dependent_eliminator_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(kernel+elab): dependent second projection — napp motive sort via reify+infer + type-position implicit insertion (Sigma D1)" \
  -- lib/cure/core/kernel.ex lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex test/cure/elab/dependent_eliminator_test.exs
```

---

### Task 2: Antigen antibody

**Gap found in review (spec §3 item 2, "Precedent to model both seeds on"):** the spec's explicit instruction for the ACCEPTING seed is to "add a D1 accepting variant [to `DepMatch`] (or as a sibling generator) rather than inventing new scaffolding" — precisely so item (iii)'s claim ("the existing conv/nf idempotence and substitution-law families exercise the new value shape via the enlarged accept set") is actually true. Verified against the worktree: `Antigen.Generators.DepMatch`'s `case_challenge/0` (`lib/antigen/generators/dep_match.ex:73-135`) currently has NO arm producing a neutral-application (`b(x)`-shaped) motive — every dependent-motive arm is `:data`-headed (`Vec m`, `Equivalent Nat m m`, `Ty`/`Sq`/`Tg` families) or the bare-nvar `tyvar_motive_case`. Without a new arm, `test/antigen/generators/dep_match_test.exs`'s existing property test (samples 500 challenges, calls `Kernel.infer` fresh on each via `SigMenu.rebuild_context`, and checks the claimed type + `Normalise.nf` non-exhaustion) NEVER exercises the new napp clause under property-based sampling — only Step 3's two fixed pins would, and those don't drive subject-reduction/normalization at all, just the error tag. So item (iii)'s gate obligation is unmet unless this is added. Step 1 below adds it; Steps 2-3 (the fixed pins) remain as a separate, complementary deterministic regression anchor at the exact `check_motive_wf` boundary — the two serve different purposes and neither substitutes for the other.

**Files:**
- Modify: `lib/antigen/generators/dep_match.ex` (one new `case_challenge/0` arm — Step 1)
- Modify: `lib/antigen/generators/malformed.ex` (one entry in the `malformation/0` frequency list, next to the existing `case_bad_motive` entries at ~line 65-67 — Step 4)
- Test: `test/antigen/neutral_app_motive_test.exs` (new — Steps 2-3)

- [ ] **Step 1: Add a D1-accepting variant to `DepMatch`**

Add a new arm to `case_challenge/0`'s `Gen.frequency` list (`lib/antigen/generators/dep_match.ex`), mirroring `closed_index/1`'s "closed `Vec Z` forces the `vcons` branch `:impossible`" trick so only ONE branch needs a real inhabitant, but with a neutral-application motive `λm.λv:Vec(m). b(m)` instead of a constant/`:data`-headed one — `b` is a fresh context variable of type `(Nat) -> Type`, and a second context witness `w : b(Z)` supplies the one inhabitant the reachable (`vnil`) branch needs:

```elixir
      {2, neutral_app_motive_case()}
```

```elixir
  # D1 neutral-application motive: λm. λv:Vec(m). b(m) — the NEW napp shape
  # (b is a free context variable of type (Nat) -> Type; b(m) reifies to
  # {:app, <b>, <m>} and must sort via the new infer_type_value_sort clause).
  # Closed to Vec(Z) so the vcons branch is :impossible (unify S k ~ Z fails,
  # mirroring closed_index/1) — only vnil needs a real inhabitant, supplied by
  # context witness w : b(Z).
  #
  # ctx (list position = final var index, per rebuild_context's reversed-fold):
  #   0 = xs : Vec(Z)         (scrutinee)
  #   1 = w  : b(Z)           (witness; its own type references b as {:var,0},
  #                             the only var already bound at that point)
  #   2 = b  : (Nat) -> Type
  defp neutral_app_motive_case do
    b_ty = {:pi, @nat, {:type, 0}}
    w_ty = {:app, {:var, 0}, @z}
    # under the motive's 2 own binders (m, v), ambient var k reads as {:var, 2+k}:
    # b is ambient index 2 -> {:var, 4}; m is the motive's own outer binder -> {:var, 1}.
    motive_napp = {:lam, @nat, {:lam, vec({:var, 0}), {:app, {:var, 4}, {:var, 1}}}}
    term = mk_case({:var, 0}, motive_napp, [{:vnil, 0, {:var, 1}}, {:vcons, 3, @z}])
    Gen.return({[vec(@z), w_ty, b_ty], term, {:app, {:var, 2}, @z}})
  end
```

This shape is derived by hand from `DepMatch`'s established conventions (list-position-equals-final-var-index, confirmed against `var_index_extra`'s reference pattern; the closed-index `:impossible`-branch trick, confirmed against `closed_index/1`) — but per this review's falsifiability rule (read-only, no `mix`/`iex`), it has not been executed. The correctness oracle is `dep_match_test.exs`'s EXISTING generic property test, unchanged: run `mix test test/antigen/generators/dep_match_test.exs` after adding the arm. If any index is off, `Kernel.infer` will either error or return a type that doesn't match the claimed type, and the test flunks with the exact term/error printed — iterate the ARM (not the test, which is immutable pre-existing behavioral coverage) until green. This is the strict TDD red-green loop applied to a property-based generator: "red" here is "the new arm isn't sampled/covered yet"; "green" is "the existing property test passes with the arm present," which itself constitutes the discharge of spec item (iii)'s obligation.

Also confirm the existing `dep_match_test.exs` "sample includes ..." `Enum.any?` assertions (pinned shapes) still pass — they check for EXISTING shapes' continued presence at existing frequencies in a 500-sample draw; adding one more weighted arm at low weight (2, matching the existing `var_index` weights) does not remove any existing shape from the frequency list, so this is expected to remain safe, analogous to the Malformed frequency-list addition in Step 4 below.

- [ ] **Step 2: Write the failing antibody test**

```elixir
defmodule Antigen.NeutralAppMotiveTest do
  @moduledoc """
  D1 antibody (spec 2026-07-08-neutral-app-sort §3.2): the kernel accepts a
  motive applying a type-family head (the enlarged accept set) and still rejects
  non-type-valued heads — pinned through the REAL kernel, no shims.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Program

  defp nat_env do
    {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
    env
  end

  # ctx: [ b : (Nat) -> Type ]  (level 0)
  defp ctx_with_type_family(env) do
    pi = Eval.eval({:pi, {:data, :Nat, [], []}, {:type, 0}}, [])
    Context.extend(Context.empty(env), pi)
  end

  test "accept pin: a motive applying a type-family variable sorts (case infers)" do
    ctx = ctx_with_type_family(nat_env())
    nat = {:data, :Nat, [], []}
    # b is de Bruijn var 1 UNDER the motive's own binder (v : Nat is var 0).
    motive = {:lam, nat, {:app, {:var, 1}, {:var, 0}}}

    # Branch bodies must inhabit b(idx) — impossible to write closed, so use a
    # scrutinee-free acceptance probe: check_motive_wf alone gates the motive;
    # drive it via infer on a case whose branches are themselves neutral-typed.
    # Simplest fully-checkable form: branches returning `b(...)`-typed values do
    # not exist closed, so pin acceptance at the motive-wf boundary by asserting
    # the case does NOT fail with :bad_motive (it must fail LATER, in branch
    # checking, with a branch-related error — proving motive-wf passed).
    kase = {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}

    assert {:error, err} = Kernel.infer(ctx, kase)
    refute err == :bad_motive, "motive-wf should now accept the neutral-app motive; got :bad_motive"
  end

  test "reject pin: a motive applying a NON-function head still fails :bad_motive" do
    ctx = Context.empty(nat_env())
    nat = {:data, :Nat, [], []}
    motive = {:lam, nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
    kase = {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx, kase)
  end
end
```

(The accept pin's discrimination logic — "fails, but NOT with `:bad_motive`" — is deliberate: a fully inhabitable neutral-app case needs a `b`-instance value, which is what the Task 1 surface probe covers end-to-end; this pin isolates the motive-wf boundary itself. If ctor atoms are namespaced, use the `ctor_atom` resolution pattern. If branch-body checking rejects with something surprising, record the actual tag in the assertion message — the pin is `!= :bad_motive`.)

- [ ] **Step 3: Run to verify the red**

Run: `mix test test/antigen/generators/dep_match_test.exs test/antigen/neutral_app_motive_test.exs`
Expected: with Task 1 landed, all may already pass — the fixed-pin antibody pins the landed behavior (red-before-Task-1 is impossible since Task 1 precedes; the "red" evidence for the fixed pins is the generator step below), and the new `DepMatch` arm's "red" evidence is the iterate-until-green loop described in Step 1 (run this same command after any arm adjustment). If the accept pin fails WITH `:bad_motive`, or `dep_match_test.exs` flunks on the new arm's term, Task 1 is broken or the new arm's shape is wrong — STOP for the former, iterate the arm for the latter.

- [ ] **Step 4: Add the Malformed generator seed**

In `lib/antigen/generators/malformed.ex`'s `malformation/0` frequency list, next to the existing `case_bad_motive` entries (~65-67):

```elixir
      {1,
       tagged(
         case_bad_motive({:lam, @nat, {:app, {:var, 0}, @z}}),
         "case motive applies a non-function (Nat-typed) head — napp reject path"
       )},
```

- [ ] **Step 5: Run the Antigen suite (scoped, then whole)**

Run: `mix test test/antigen/` — expected: all pass (490 + 2 new = 492; the `DepMatch` arm feeds its existing 2 tests, no count change; the Malformed seed feeds existing `"term/rejection"` assays — if either frequency-list addition changes any seeded-run expectations pinned elsewhere, that is a STOP, not an edit).

- [ ] **Step 6: Commit**

```bash
git add -- lib/antigen/generators/dep_match.ex lib/antigen/generators/malformed.ex test/antigen/neutral_app_motive_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(antigen): neutral-app motive antibody — DepMatch accept variant + fixed pins + malformed napp reject seed" \
  -- lib/antigen/generators/dep_match.ex lib/antigen/generators/malformed.ex test/antigen/neutral_app_motive_test.exs
```

---

### Task 3: differential-oracle `sg` cluster

**Files:**
- Create: `test/oracle/sg/sg01_dependent_second.cure`, `test/oracle/sg/sg01_dependent_second.idr`
- Generated: `test/oracle/sg/verdicts.json` (by the oracle run — never hand-written)

- [ ] **Step 1: Author the pair**

`sg01_dependent_second.cure` — mirror the framing of `test/oracle/dpair/dpp01_poly_nested.cure` (the closest existing analog: a dependent-pair/Sigma probe with a GADT `indices (...)` family), not `guard01_simple.cure` — content = the Task 1 probe module. **No `start`/entry def is required or conventional**: `Oracle.cure_verdict/1` calls `Program.elaborate/1` directly and `idris_verdict/2` runs `idris2 --check` (both verified in `lib/cure/oracle.ex`) — neither executes the program, so a typecheck-only fixture is normal. Confirmed by precedent: `test/oracle/dpair/dpp01_poly_nested.{cure,idr}` and `test/oracle/dep/dep07_higher_order_family.{cure,idr}` have no `start` in either file and are committed `same`/`same` pairs. (`guard01_simple` has a `start` only because it happens to also double as a runnable demo — that's incidental to its cluster, not a house-format requirement.)

`sg01_dependent_second.idr`:

```idris
%default total

data MySigma : (a : Type) -> (b : a -> Type) -> Type where
  MkPair : (x : a) -> b x -> MySigma a b

first : MySigma a b -> a
first (MkPair x y) = x

second : (p : MySigma a b) -> b (first p)
second (MkPair x y) = y
```

- [ ] **Step 2: Run the oracle for this cluster ONLY, alone**

Run: `mix cure.oracle sg`
Expected: sg01 → cure `accept`, idris `accept`, relation `same`, written to `test/oracle/sg/verdicts.json`. Then `git status` — confirm NO other cluster's verdicts.json changed (if one did: `git checkout -- <it>` and STOP-and-report). Any divergence on sg01 (either direction) = STOP-and-report per the oracle contract — do not mark `cure_stricter`, do not edit fixtures to force agreement.

- [ ] **Step 3: Replay green**

Run: `mix test test/oracle_replay_test.exs`
Expected: all pass, including the new sg row.

- [ ] **Step 4: Commit**

```bash
git add -- test/oracle/sg/sg01_dependent_second.cure test/oracle/sg/sg01_dependent_second.idr test/oracle/sg/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): sg cluster — dependent second projection typechecks (same/same)" \
  -- test/oracle/sg/sg01_dependent_second.cure test/oracle/sg/sg01_dependent_second.idr test/oracle/sg/verdicts.json
```

---

### Task 4: full gate + final verification

- [ ] **Step 1: Full gates (ONE at a time, alone, in this order)**

1. `mix test test/antigen/` — expected: 492, 0 failures.
2. `mix test` — expected: ~3249 (3238 baseline + 7 Task-1/1b unit tests [includes the review-added runtime-execution test and the amendment-added explicit-param kernel pin] + 2 Task-2 antibody tests + 2 Task-3 oracle-replay tests — `test/oracle_replay_test.exs` generates its `describe`/`test` pair PER CLUSTER via a compile-time `for cluster <- Cure.Oracle.clusters() do ... end` loop, so the new `sg` cluster adds exactly 2 tests to this file's count, not zero; recount all four terms from actual red-step outputs), 0 failures. One known non-reproducible Antigen-seed flake: exactly one Antigen seed failure → re-run once alone; if unreproduced, note honestly. Anything else = STOP.

- [ ] **Step 2: Final verification**

Use `<pre-batch-commit>` recorded in Task 1 Step 0.4 (the `HEAD` hash before any of this plan's commits) as the base of every diff below — do not use `<task1-commit>~1`, which requires re-deriving the same value less directly.

- `git diff <pre-batch-commit> HEAD -- lib/cure/core/` shows ONLY the two kernel.ex clauses (+ their comments) — nothing else under core.
- `git diff --stat <pre-batch-commit> HEAD -- lib/cure/elab/` — **[AMENDED 2026-07-09, spec §7.7]** exactly two files: `declarations.ex` (ctx threading + delegation + helper) and `elaborator.ex` (the one public wrapper). Anything else under elab = STOP.
- `git diff --stat <pre-batch-commit> HEAD -- lib/cure/types/ lib/cure/compiler/` — empty (decoy pipeline untouched).
- `git log --format='%an %ae' <pre-batch-commit>..HEAD` — only `Made In Heaven madeinheaven@madeinheaven.com`.

---

## Self-review notes (spec-coverage map)

- §2 clause → Task 1 Step 3 (verbatim, signature-aware reify per hardened §2.2). §2.4 defensive clause + demonstrable necessity → Task 1 Steps 4-5 (mid-point crash captured). §3.1 red-green → Task 1 Steps 2/4/6. §3.2 antibody → Task 2: the ACCEPTING seed is the new `DepMatch` variant (Step 1, per spec's explicit "add a D1 accepting variant there" precedent — a review-found gap in the original plan draft, now fixed) plus fixed accept/reject pins (Steps 2-3) as a complementary deterministic anchor; the REJECTING seed is the Malformed frequency-list addition (Step 4, precedent `Malformed.case_bad_motive/1` per spec). §3.3 full suites → Tasks 2/4. §3.4 oracle → Task 3 (single-cluster discipline + divergence STOP; fixture template is `dpair`, not `guard`, per review — no `start` def needed). §4's five spec-mandated behaviors → Task 1's six unit tests (probe elaborates + probe runs on BEAM [review-added, was missing] + 2 surface negatives + 2 hand-built §2.4). §6.5 diff criterion → Task 4 Step 2 (using `<pre-batch-commit>` recorded in Task 1 Step 0.4).
- Latitude is confined to: surface framing of the two adjustable negatives, ctor-atom namespacing, the exact de Bruijn indices in the new `DepMatch` arm (iterate against `dep_match_test.exs` until green, per Task 2 Step 1), and recount of gate totals — all report-required.
- D2 (Sigma retirement) is the chained follow-up; its scout inventory must be re-swept in-worktree (spec §5 note).
- **Amendment log (2026-07-09, spec §7):** execution STOPped at Task 1 Step 6 — kernel clauses correct, implicit-param probe still `:bad_motive` (elaborator return-type lowering has no implicit insertion, `declarations.ex:915-916`). Adjudicated per the standing align-with-real-languages directive: Task 1b added (E-layer type-position implicit insertion, spec §7.3 design); Task 1's §2.4 pair test corrected to a function-typed head (the executor proved the Nat-head version never reaches the crash, spec §7.6); explicit-param kernel pin added so Task 1 keeps an honest kernel-only green; Task 1/1b commit combined (red-test-file discipline); gate count 3248→3249; Task 4 elab diff expectation updated.
