# Z3 Guard-Coverage Lint Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the untrusted Z3 guard-coverage lint (trichotomy drops the catch-all; non-exhaustive stays an error; shadowed guards warn) at the `guard_chain` site, plus the stale `bool_elim` vocabulary cleanup — spec `docs/superpowers/specs/language/2026-07-08-guard-coverage-lint-design.md` (hardened `3b012d1`, site-scoped `f64ea78`).

**Architecture:** New E-layer module `Cure.Elab.GuardLint` (Core→SMT-LIB translator, Z3 query runner reusing `Cure.SMT.Process`, process-dictionary warnings channel) + a surgical change to `guard_chain` in `lib/cure/elab/elaborator.ex` (thread an accumulator of elaborated guard Core terms; recover a provably-exhaustive final guarded arm; shadow-warn) + an Antigen lint-soundness vertical mirroring the just-landed `ElabDotForcing`.

**Tech Stack:** Elixir, Z3 via `Cure.SMT.Process` (`z3 -smt2 -in` port), ExUnit, Antigen.

## Global Constraints (from the spec — every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch` (already checked out; no new branches/worktrees).
- **Layer E + Antigen only.** Files touched: `lib/cure/elab/guard_lint.ex` (new), `lib/cure/elab/elaborator.ex`, `lib/cure/elab/program.ex`, `lib/cure/elab/declarations.ex` (comment), `lib/antigen/generators/elab_guard_lint.ex` (new), `lib/antigen/assays/elab.ex`, `lib/antigen/runner.ex`, `lib/antigen/assays/dot_forcing.ex` (moduledoc), `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (one sentence), new test files. **NOTHING under `lib/cure/core/` changes** (not even comments — Task 4 verified none are stale there). No changes to `lib/cure/types/*` or `lib/cure/compiler/*` (two-pipeline discipline: those are the NON-dependent decoy pipeline; the dependent machinery is `lib/cure/elab/*` + `lib/cure/core/*` only).
- The two constructor-group `:non_exhaustive` sites (`build_guard_chain` at `elaborator.ex:2748`, `fold_leaf_rows` at `2987`) are **byte-identical unconditionally** — spec §2.3a. Do not touch them.
- Strict red-green TDD: write the failing test, run it, capture the exact failure, implement, re-run green, commit. Tests are behavioral and immutable once green. Existing pinned tests (`test/cure/elab/guard_test.exs`, `test/cure/elab/ctor_guard_test.exs`) must pass unmodified — the spec's pinned-fixture audit already verified no conflict.
- **ONE mix command at a time, ever** (a past concurrent run caused a kernel panic). Scoped `mix test <file>` per step; the full gate runs ONCE, alone, in Task 4.
- Git: commit per task, author flag on EVERY commit `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO Co-Authored-By/trailers, staging via explicit pathspec only (`git add -- <path>`), never `git add -A`/`.`.
- Do not run `mix cure.oracle` (destructive). Oracle coverage is via replay inside the full suite.
- Z3 is assumed present (locked decision: part of the language). `guard_lint.ex` still degrades conservatively if it isn't, and Task 1 tests that path.
- STOP-and-report (do not improvise) if: a pinned test fails in a way that implicates the lint; the trichotomy cell rejects with Z3 installed; any `:flip` metamorphic cell fails at Task 3 gate; or any change would touch `lib/cure/core/`.

## File Structure

- `lib/cure/elab/guard_lint.ex` — NEW: translator (§2.2 fragment), exhaustiveness/shadow queries, warnings channel.
- `lib/cure/elab/elaborator.ex` — `guard_chain/6`→`/7` (accumulator), final-arm recovery, shadow warn call; comment rewrites (Task 4).
- `lib/cure/elab/program.ex` — one reset line in `elaborate/1`.
- `test/cure/elab/guard_lint_test.exs` — NEW: unit (Task 1) + integration (Task 2) tests.
- `lib/antigen/generators/elab_guard_lint.ex` — NEW: fixed catalog + metamorphic generator (mirrors `elab_dot_forcing.ex`).
- `lib/antigen/assays/elab.ex` — two `run/1` clauses for `"elab/guard_lint"`.
- `lib/antigen/runner.ex` — one registry line.
- `test/antigen/elab_guard_lint_test.exs` — NEW: discrimination + gates + round-trip + wiring.
- `lib/cure/elab/declarations.ex`, `lib/antigen/assays/dot_forcing.ex`, roadmap row 4 — doc/comment edits (Task 4).

---

### Task 1: `Cure.Elab.GuardLint` — translator, queries, warnings channel

**Files:**
- Create: `lib/cure/elab/guard_lint.ex`
- Test: `test/cure/elab/guard_lint_test.exs` (unit describe only; Task 2 appends the integration describe)

**Interfaces (Produces — Task 2 consumes exactly these):**
- `GuardLint.prove_exhaustive(guard_cores :: [Core.term()], ctx :: Cure.Core.Context.t()) :: :proven | :not_proven`
- `GuardLint.shadowed?(guard_core, prior_cores :: [Core.term()], ctx) :: boolean()`
- `GuardLint.reset_warnings() :: :ok`-ish (return ignored), `GuardLint.record_warning(term()) :: :ok`-ish, `GuardLint.warnings() :: [term()]` (insertion order)

- [ ] **Step 1: Write the failing unit tests**

```elixir
defmodule Cure.Elab.GuardLintTest do
  @moduledoc """
  Spec 2026-07-08-guard-coverage-lint: the untrusted Z3 coverage lint. Unit
  describe drives GuardLint directly on hand-built Core; the integration
  describe (Task 2) drives it through Program.elaborate/1.
  """
  use ExUnit.Case, async: false

  alias Cure.Core.Context
  alias Cure.Elab.GuardLint

  # Context with two machine-Int vars: index 0 and index 1.
  defp int_ctx do
    Context.empty() |> Context.extend({:vint_type}) |> Context.extend({:vint_type})
  end

  defp p(op, a, b), do: {:prim, op, [a, b]}
  @x {:var, 0}
  @y {:var, 1}

  describe "prove_exhaustive/2 (§2.2 fragment, §2.3a recovery oracle)" do
    test "trichotomy over Int is proven" do
      assert :proven =
               GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:eq, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a complement pair is proven" do
      assert :proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:ge, @x, @y)], int_ctx())
    end

    test "an Int-only cover is proven over Int (documents the fragment's Int semantics)" do
      # x <= 0 | x >= 1 — exhaustive over Int, NOT over Float; translatable only
      # because the vars are Int-typed in ctx (a Float var falls out at int_form).
      assert :proven =
               GuardLint.prove_exhaustive(
                 [p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})],
                 int_ctx()
               )
    end

    test "a genuine gap is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a Float-typed variable makes its guard untranslatable (not proven)" do
      ctx = Context.empty() |> Context.extend({:vfloat_type}) |> Context.extend({:vfloat_type})
      assert :not_proven = GuardLint.prove_exhaustive([p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})], ctx)
    end

    test "an untranslatable guard can never help prove exhaustiveness (K13)" do
      mystery = {:ctor, :Mystery, [@x]}
      assert :not_proven = GuardLint.prove_exhaustive([mystery], int_ctx())
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), mystery], int_ctx())
    end

    test "the empty guard list is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([], int_ctx())
    end
  end

  describe "shadowed?/3" do
    test "a literally repeated translatable guard is shadowed" do
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "an implied guard is shadowed" do
      # x < y implies x <= y
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:le, @x, @y)], int_ctx())
    end

    test "a non-implied guard is not shadowed" do
      refute GuardLint.shadowed?(p(:gt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "no priors -> never shadowed" do
      refute GuardLint.shadowed?(p(:lt, @x, @y), [], int_ctx())
    end

    test "a literally repeated UNtranslatable guard is shadowed via atom interning (§2.2)" do
      g = {:ctor, :Mystery, [@x]}
      assert GuardLint.shadowed?(g, [g], int_ctx())
    end

    test "distinct untranslatable guards are not shadowed (distinct constants)" do
      refute GuardLint.shadowed?({:ctor, :MysteryB, [@x]}, [{:ctor, :MysteryA, [@x]}], int_ctx())
    end
  end

  describe "warnings channel (§2.5)" do
    test "record/read/reset round-trip in insertion order" do
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
      GuardLint.record_warning({:guard_shadowed, 1})
      GuardLint.record_warning({:guard_shadowed, 2})
      assert GuardLint.warnings() == [{:guard_shadowed, 1}, {:guard_shadowed, 2}]
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
    end
  end
end
```

Note `async: false`: primarily because Task 2 appends integration tests to this same file that call `Emit.compile_and_load` (compiling `:"Cure.GuardLintTri"` et al.), which mutates GLOBAL VM code-server state — the established reason this codebase already uses for `async: false` alongside `compile_and_load` (`test/cure/elab/erasure_relevance_test.exs:43-44`: "load a BEAM module ..., which mutates global VM state, so this module must not run concurrently"). Secondarily, it also keeps this file's Z3 port-spawning serial, avoiding unnecessary concurrent OS processes. (The warnings channel itself is plain process-dictionary state, isolated per ExUnit test process regardless of `async`, so it does not by itself require `async: false`.)

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/guard_lint_test.exs`
Expected: every test fails with `UndefinedFunctionError` — `Cure.Elab.GuardLint` does not exist. If you instead see a compile error in the test file, fix the test file, not the assertions.

- [ ] **Step 3: Implement the module**

```elixir
defmodule Cure.Elab.GuardLint do
  @moduledoc """
  Untrusted Z3 guard-coverage lint (spec 2026-07-08-guard-coverage-lint).

  Two queries over ELABORATED guard Core terms (always with their typing
  `Context`, because the fragment is Int-only and must see operand types):

    * `prove_exhaustive/2` — is the disjunction of the guards valid? `:proven`
      lets `guard_chain` accept a final guarded arm as the catch-all (its test
      elided; the kernel re-checks the emitted term as always — §2.3a). Every
      failure mode (refuted / unknown / timeout / untranslatable / Z3 absent)
      is `:not_proven`, leaving behavior byte-identical to pre-lint.
    * `shadowed?/3` — is a guard implied by the disjunction of the guards
      before it (its arm dead)? Only ever produces a warning.

  Translation fragment (§2.2): `{:prim, cmp, [a, b]}` over Int-typed operands
  (vars checked against the Context, `{:int_lit, _}`, linear `add/sub/mul`),
  plus literal `True`/`False`. Anything else falls back to an uninterpreted
  Bool constant interned BY TERM — identical untranslatable guards share a
  constant (so shadow detection catches a literal repeat), distinct ones do
  not, and an uninterpreted constant can never make a disjunction valid, so
  exhaustiveness can never lean on one (K13: untranslatable ⇒ not proven).

  Z3 is OUT of the TCB: nothing here influences a kernel judgement (locked
  SMT trust-boundary decision). Warnings ride a process-dictionary list reset
  by `Cure.Elab.Program.elaborate/1` (§2.5) — not an `Env` field.
  """

  alias Cure.Core.Context
  alias Cure.SMT.Process, as: Z3

  @warnings_key :cure_guard_lint_warnings
  @timeout 3_000

  # -- Warnings channel (§2.5) -------------------------------------------------

  def reset_warnings, do: Process.put(@warnings_key, [])

  def record_warning(w), do: Process.put(@warnings_key, [w | Process.get(@warnings_key, [])])

  def warnings, do: Process.get(@warnings_key, []) |> Enum.reverse()

  # -- Lint queries -------------------------------------------------------------

  @spec prove_exhaustive([tuple()], Context.t()) :: :proven | :not_proven
  def prove_exhaustive([], _ctx), do: :not_proven

  def prove_exhaustive(guards, ctx) do
    {forms, st} = render_guards(guards, ctx)

    case check_sat("(assert (not " <> disj(forms) <> "))", st) do
      :unsat -> :proven
      _ -> :not_proven
    end
  end

  @spec shadowed?(tuple(), [tuple()], Context.t()) :: boolean()
  def shadowed?(_guard, [], _ctx), do: false

  def shadowed?(guard, prior, ctx) do
    {[g | ps], st} = render_guards([guard | prior], ctx)

    case check_sat("(assert (and " <> g <> " (not " <> disj(ps) <> ")))", st) do
      :unsat -> true
      _ -> false
    end
  end

  # -- Rendering (§2.2) ----------------------------------------------------------

  defp disj([f]), do: f
  defp disj(fs), do: "(or " <> Enum.join(fs, " ") <> ")"

  defp render_guards(guards, ctx) do
    Enum.map_reduce(guards, %{ints: MapSet.new(), atoms: %{}}, fn g, st ->
      case bool_form(g, ctx, st) do
        {:ok, s, st1} ->
          {s, st1}

        :error ->
          case Map.fetch(st.atoms, g) do
            {:ok, name} ->
              {name, st}

            :error ->
              name = "u" <> Integer.to_string(map_size(st.atoms))
              {name, %{st | atoms: Map.put(st.atoms, g, name)}}
          end
      end
    end)
  end

  @cmp %{lt: "<", le: "<=", gt: ">", ge: ">=", eq: "=", ne: "distinct"}

  defp bool_form({:prim, op, [a, b]}, ctx, st) when is_map_key(@cmp, op) do
    with {:ok, sa, st} <- int_form(a, ctx, st),
         {:ok, sb, st} <- int_form(b, ctx, st) do
      {:ok, "(" <> Map.fetch!(@cmp, op) <> " " <> sa <> " " <> sb <> ")", st}
    else
      _ -> :error
    end
  end

  defp bool_form({:ctor, :True, []}, _ctx, st), do: {:ok, "true", st}
  defp bool_form({:ctor, :False, []}, _ctx, st), do: {:ok, "false", st}
  defp bool_form(_other, _ctx, _st), do: :error

  defp int_form({:int_lit, n}, _ctx, st), do: {:ok, int_lit(n), st}

  defp int_form({:var, i}, ctx, st) do
    case Context.lookup(ctx, i) do
      {:vint_type} -> {:ok, var_name(i), %{st | ints: MapSet.put(st.ints, i)}}
      _ -> :error
    end
  end

  # Keep the fragment linear: `mul` needs a literal multiplicand.
  defp int_form({:prim, :mul, [a, b]}, ctx, st) do
    if match?({:int_lit, _}, a) or match?({:int_lit, _}, b),
      do: arith("*", a, b, ctx, st),
      else: :error
  end

  defp int_form({:prim, :add, [a, b]}, ctx, st), do: arith("+", a, b, ctx, st)
  defp int_form({:prim, :sub, [a, b]}, ctx, st), do: arith("-", a, b, ctx, st)
  defp int_form(_other, _ctx, _st), do: :error

  defp arith(sym, a, b, ctx, st) do
    with {:ok, sa, st} <- int_form(a, ctx, st),
         {:ok, sb, st} <- int_form(b, ctx, st) do
      {:ok, "(" <> sym <> " " <> sa <> " " <> sb <> ")", st}
    else
      _ -> :error
    end
  end

  defp int_lit(n) when n < 0, do: "(- " <> Integer.to_string(-n) <> ")"
  defp int_lit(n), do: Integer.to_string(n)

  defp var_name(i), do: "v" <> Integer.to_string(i)

  # -- Z3 execution (§2.4: reuse Cure.SMT.Process ONLY) --------------------------

  defp check_sat(assertion, st) do
    decls =
      Enum.map(Enum.sort(MapSet.to_list(st.ints)), &("(declare-const " <> var_name(&1) <> " Int)")) ++
        Enum.map(Enum.sort(Map.values(st.atoms)), &("(declare-const " <> &1 <> " Bool)"))

    query = Enum.join(decls ++ [assertion, "(check-sat)"], "\n")

    if Z3.z3_available?() do
      run_isolated(fn -> Z3.start_link(timeout: @timeout) end, query)
    else
      :unknown
    end
  end

  # `Cure.SMT.Process.start_link` LINKS the solver GenServer to US (the
  # elaborator/test process). A Z3 binary crash/kill is captured as an ordinary
  # `:exit_status` port message inside `Process`'s own `handle_call` and replied
  # as `{:error, _}` — no crash. But a genuine bug INSIDE the `Process` GenServer
  # (an unhandled message, an exception in its own receive loop) terminates that
  # linked process abnormally, and the resulting EXIT SIGNAL is not something any
  # `try/catch` in our code can intercept — with `trap_exit` at its default
  # `false`, an unhandled linked EXIT kills the receiving process outright,
  # bypassing ordinary exception handling entirely (this is a real per-`Cure.SMT.Process`
  # gap: `Cure.SMT.Solver.run_with_z3` has the identical exposure and no extra
  # guard against it either — but that pipeline is opt-in refinement checking,
  # while this lint sits on every `Program.elaborate/1` call, where spec §3 make
  # "must never crash an elaboration" an absolute, so we harden past parity with
  # the existing caller rather than merely matching it). Toggling `trap_exit` for
  # the duration of the query turns any such crash into an ordinary `{:EXIT, pid,
  # reason}` message we explicitly drain and fold into `:unknown`, instead of
  # letting it kill the caller. Residual, accepted trade-off: for the query's
  # brief window (≤ `@timeout`), an UNRELATED linked process crashing also
  # arrives as a mailbox message instead of killing us; we only drain the one
  # tagged with our own `pid`, so an unrelated `{:EXIT, _, _}` is left queued as
  # ordinary (harmless, since this call runs in an ordinary synchronous
  # process, not a `handle_info` loop expecting none) rather than propagating —
  # acceptable given the alternative (Z3 crashing the elaborator) is strictly
  # worse and the window is short.
  defp run_isolated(start_fun, query) do
    prior = Process.flag(:trap_exit, true)

    try do
      case start_fun.() do
        {:ok, pid} ->
          try do
            case Z3.query(pid, query) do
              {:unsat, _} -> :unsat
              {:sat, _} -> :sat
              _ -> :unknown
            end
          catch
            # A dead port / call timeout / trapped linked crash degrades
            # conservatively (§2.3, §3).
            _, _ -> :unknown
          after
            try do
              Z3.stop(pid)
            catch
              _, _ -> :ok
            end

            # Drain the EXIT message `stop/1` (a normal GenServer.stop) or a
            # crash may have queued, so it never leaks into the caller's own
            # mailbox once trap_exit is restored below.
            receive do
              {:EXIT, ^pid, _} -> :ok
            after
              0 -> :ok
            end
          end

        _ ->
          :unknown
      end
    after
      Process.flag(:trap_exit, prior)
    end
  end
end
```

Implementation notes for the executor:
- `alias Cure.SMT.Process, as: Z3` is load-bearing: the warnings channel uses Elixir's own `Process.put/get`, which a bare `alias Cure.SMT.Process` would shadow.
- `Z3.query/2` sends one SMT-LIB2 text through the port and classifies on `sat`/`unsat`/`unknown` output; declarations + assert + `(check-sat)` go in one string. A fresh process per query means no cross-query `(reset)` concerns.
- If `Context.extend/2` or `Context.empty/0` signatures differ from the test's usage (they were verified at plan time: `lib/cure/core/context.ex:24-46`), fix the TEST's helper, never the assertions.

- [ ] **Step 4: Run to verify green**

Run: `mix test test/cure/elab/guard_lint_test.exs`
Expected: 14 tests, 0 failures. (If trichotomy is `:not_proven` with Z3 installed, debug the SMT string by IO.puts-ing `query` — do not weaken the test.)

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/guard_lint.ex test/cure/elab/guard_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): GuardLint — untrusted Z3 coverage/shadow queries + warnings channel" \
  -- lib/cure/elab/guard_lint.ex test/cure/elab/guard_lint_test.exs
```

---

### Task 2: `guard_chain` recovery + shadow warnings + reset wiring

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (alias line 17; `guard_chain` clauses at 2439-2466; its two callers at 2404 and 2430)
- Modify: `lib/cure/elab/program.ex` (`elaborate/1` at line 16)
- Test: `test/cure/elab/guard_lint_test.exs` (append the integration describe)

**Interfaces:**
- Consumes: `GuardLint.prove_exhaustive/2`, `shadowed?/3`, `record_warning/1`, `warnings/0`, `reset_warnings/0` (Task 1).
- Produces: surface behavior only — no new public functions.

- [ ] **Step 1: Append the failing integration tests**

Append inside `Cure.Elab.GuardLintTest` (before the final `end`):

```elixir
  describe "elaboration integration (§6): recovery + warnings through Program.elaborate/1" do
    alias Cure.Elab.{Emit, Program}

    @nat "mod M\n  type Nat = Z | S(Nat)\n"

    test "trichotomy without a catch-all is accepted and runs correctly on all three regions" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x == b -> S(Z())\n" <>
          "    x when x > b -> S(S(Z()))\n" <>
          "  fn lo() -> Nat = cmp(1, 5)\n" <>
          "  fn mid() -> Nat = cmp(5, 5)\n" <>
          "  fn hi() -> Nat = cmp(9, 5)\nend\n"

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.GuardLintTri", functions: [:cmp, :lo, :mid, :hi])

      assert apply(mod, :lo, []) == :Z
      assert apply(mod, :mid, []) == {:S, :Z}
      assert apply(mod, :hi, []) == {:S, {:S, :Z}}
    end

    test "a two-guard complement without a catch-all is accepted" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x >= b -> S(Z())\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a genuine gap still rejects with the pinned error shape" do
      src =
        @nat <>
          "  fn cmp(a: Int, b: Int) -> Nat = match a\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x > b -> S(Z())\nend\n"

      assert {:error, {:unsupported_guard, :non_exhaustive}} = Program.elaborate(src)
    end

    test "semantically exhaustive but untranslatable guards still reject (K13 observable)" do
      src =
        @nat <>
          "  fn pos(i: Int) -> Bool = i > 0\n" <>
          "  fn nonpos(i: Int) -> Bool = i <= 0\n" <>
          "  fn cls(n: Int) -> Nat = match n\n" <>
          "    x when pos(x) -> Z()\n" <>
          "    x when nonpos(x) -> S(Z())\nend\n"

      assert {:error, {:unsupported_guard, :non_exhaustive}} = Program.elaborate(src)
    end

    test "a shadowed guard warns; the program still elaborates" do
      src =
        @nat <>
          "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x < b -> S(Z())\n" <>
          "    x -> S(S(Z()))\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
      assert [{:guard_shadowed, 1}] = GuardLint.warnings()
    end

    test "an unshadowed chain leaves no warnings (and elaborate/1 resets stale ones)" do
      GuardLint.record_warning({:guard_shadowed, 99})

      src =
        @nat <>
          "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
          "    x when x < b -> Z()\n" <>
          "    x when x > b -> S(Z())\n" <>
          "    x -> S(S(Z()))\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
      assert GuardLint.warnings() == []
    end
  end
```

- [ ] **Step 2: Run to verify the right failures**

Run: `mix test test/cure/elab/guard_lint_test.exs`
Expected: the 14 Task-1 tests still pass; the 6 new tests fail — trichotomy/complement with `MatchError` (`Program.elaborate` returns `{:error, {:unsupported_guard, :non_exhaustive}}` today), the shadowed test with `MatchError` on `warnings()` (empty today), the reset test failing on the stale `{:guard_shadowed, 99}` surviving. The two "still rejects" tests may already pass — that is fine and expected (they pin no-regression).

- [ ] **Step 3: Implement the elaborator + program changes**

(a) `lib/cure/elab/elaborator.ex:17` — extend the alias:

```elixir
  alias Cure.Elab.{GuardLint, MetaCtx, Subst, Unify}
```

(b) Replace the two `guard_chain` clauses (currently `elaborator.ex:2439-2466`) with arity-7 versions threading `acc` (the already-elaborated guard Core terms, in order), and update the comment above the first clause:

```elixir
  # The final arm closes the chain: it must be an unguarded catch-all — unless
  # the untrusted Z3 lint proves the chain's guards exhaustive (spec
  # 2026-07-08-guard-coverage-lint §2.3a), in which case the final guarded arm
  # IS the catch-all: its provably-true test is elided and its body goes
  # through the ordinary bind_catchall_body path, so the kernel re-checks
  # exactly the term an unguarded catch-all would have produced. Every lint
  # failure (unproven / untranslatable / Z3 unavailable) reproduces today's
  # rejection byte-for-byte — including when the final guard itself fails to
  # elaborate, which was never reached pre-lint.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env, acc) do
    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(
          scrut_expr,
          Keyword.fetch!(meta, :pattern),
          single_body(body),
          expected,
          names,
          ctx,
          env
        )

      guard ->
        pat = Keyword.fetch!(meta, :pattern)

        elaborated =
          with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard) do
            elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env)
          end

        case elaborated do
          {:ok, test} ->
            maybe_warn_shadowed(test, acc, ctx)

            if GuardLint.prove_exhaustive(acc ++ [test], ctx) == :proven do
              bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)
            else
              {:error, {:unsupported_guard, :non_exhaustive}}
            end

          _error ->
            {:error, {:unsupported_guard, :non_exhaustive}}
        end
    end
  end

  # A guarded arm becomes a `:case` on the inductive Bool (`bool_case/5`); an
  # unguarded catch-all before the end shadows every later arm and closes the
  # chain early.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body} | rest], expected, names, ctx, env, acc) do
    pat = Keyword.fetch!(meta, :pattern)

    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)

      guard ->
        with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard),
             {:ok, body_expr} <- guard_bind(scrut_expr, pat, single_body(body)),
             {:ok, test} <-
               elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env),
             {:ok, tt} <- elaborate_expr_checked(body_expr, expected, names, ctx, env),
             {:ok, ff} <- guard_chain(scrut_expr, rest, expected, names, ctx, env, acc ++ [test]) do
          maybe_warn_shadowed(test, acc, ctx)
          {:ok, bool_case(test, expected, tt, ff, ctx)}
        end
    end
  end

  # Dead-arm lint (§2.1): a guard implied by the disjunction of the guards
  # before it can never fire. Warning only — elaboration is unaffected. The
  # index is the guard's 0-based position among the chain's guarded arms.
  defp maybe_warn_shadowed(_test, [], _ctx), do: :ok

  defp maybe_warn_shadowed(test, acc, ctx) do
    if GuardLint.shadowed?(test, acc, ctx),
      do: GuardLint.record_warning({:guard_shadowed, length(acc)})

    :ok
  end
```

Behavioral fine points the executor must preserve:
- The final-arm clause's `_error ->` branch maps ANY guard-elaboration failure to `{:error, {:unsupported_guard, :non_exhaustive}}` — today's exact behavior (pre-lint, a final guarded arm was rejected before its guard was ever elaborated). Do not leak the inner error.
- In the middle clause the shadow check fires only on the success path (after the whole `with`), so a failing chain elaboration emits no warnings for arms that never make it into emitted Core. Order in the final clause: warn (if shadowed) BEFORE the exhaustiveness decision — a shadowed final guard on a proven chain is still dead code worth reporting.
- `acc ++ [test]` keeps guard order; all guards in one chain share the same `names`/`ctx` (the recursion never extends `ctx`), so de Bruijn indices are consistent across the accumulated terms — the property `GuardLint`'s per-index SMT constants rely on.

(c) Update the two callers to seed the accumulator:

At `elaborator.ex:2404` (inside `try_guard_match`):
```elixir
        guard_chain(scrut_expr, arms, expected, names, ctx, env, [])
```
At `elaborator.ex:2430` (inside `bind_once_guard`):
```elixir
      with {:ok, chain} <-
             guard_chain({:variable, [], fresh}, arms, expected1, names1, ctx1, env, []) do
```

(d) `lib/cure/elab/program.ex:16` — reset the channel at the entry (spec §2.5):

```elixir
  def elaborate(source) when is_binary(source) do
    Cure.Elab.GuardLint.reset_warnings()

    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      check_ast(ast)
    end
  end
```

- [ ] **Step 4: Run to verify green**

Run: `mix test test/cure/elab/guard_lint_test.exs`
Expected: 20 tests, 0 failures.

- [ ] **Step 5: Run the neighboring pinned suites (immutability check)**

Run (one at a time, in this order):
- `mix test test/cure/elab/guard_test.exs` — expected 4 tests, 0 failures (the 66-74 pin still rejects: `x == 0 | x == 1` is genuinely non-exhaustive, Z3 agrees).
- `mix test test/cure/elab/ctor_guard_test.exs` — expected all pass (conservative §2.3a site, untouched).
- `mix test test/cure/elab/match_test.exs test/cure/elab/conditional_test.exs` — expected all pass.

If any pinned test fails, STOP and report — do not edit pinned tests.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex lib/cure/elab/program.ex test/cure/elab/guard_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): guard_chain exhaustiveness recovery + shadow warnings via GuardLint" \
  -- lib/cure/elab/elaborator.ex lib/cure/elab/program.ex test/cure/elab/guard_lint_test.exs
```

---

### Task 3: Antigen `elab/guard_lint` lint-soundness vertical

**Files:**
- Create: `lib/antigen/generators/elab_guard_lint.ex`
- Modify: `lib/antigen/assays/elab.ex` (two `run/1` clauses, inserted after the `"elab/dot_forcing"` relation clause, before the `elab/soundness` clauses)
- Modify: `lib/antigen/runner.ex` (one line after `defp assay_module("elab/dot_forcing")` at line 350)
- Test: `test/antigen/elab_guard_lint_test.exs`

**Interfaces:**
- Consumes: `Antigen.Challenge.new/1`, `to_pieces/1`, `from_pieces/7` (all landed; the `"expect_error"` payload key is whitelisted since F's `284132c`), `Antigen.Assays.Elab.elaborate/1` + `verdict_bit/1` + `reject_head/1` (landed in F).
- Produces: `Antigen.Generators.ElabGuardLint.guard_lint_challenges/0`, `catalog/0`, `source/1`, `body/1`, `metamorphic_challenges/0`; assay label `"elab/guard_lint"`.

Structural template: mirror the landed `lib/antigen/generators/elab_dot_forcing.ex` and `test/antigen/elab_dot_forcing_test.exs` exactly (same `Challenge.new` fields, same test-file shape — read both before writing). Z3 note: the accept labels of cells 1/2/5 hold only with Z3 present, which is a language-level guarantee (locked decision) — do not add availability gating.

- [ ] **Step 1: Write the failing tests**

`test/antigen/elab_guard_lint_test.exs` — mirror `test/antigen/elab_dot_forcing_test.exs`'s structure with this content (adjust ONLY helper call shapes if the landed file differs — read it first):

```elixir
defmodule Antigen.ElabGuardLintTest do
  @moduledoc """
  Spec 2026-07-08-guard-coverage-lint §6: the lint-soundness vertical. The
  catalog pins hand-verified exhaustive/non-exhaustive labels two-sided; the
  metamorphic layer pins that dropping a guard from a proven-exhaustive set
  flips the verdict (the lint is load-bearing and never over-proves).
  """
  use ExUnit.Case, async: false

  alias Antigen.Challenge
  alias Antigen.Assays.Elab, as: Assay
  alias Antigen.Generators.ElabGuardLint, as: Gen

  describe "assay discrimination" do
    test "a correct catalog cell passes" do
      [c | _] = Gen.guard_lint_challenges()
      assert Assay.run(c) == :ok
    end

    test "a wrong expected verdict is a violation" do
      [c | _] = Gen.guard_lint_challenges()
      flipped = %{c | payload: %{c.payload | expect: :reject}}
      assert {:violation, {:guard_lint_verdict_wrong, _, _}} = Assay.run(flipped)
    end

    test "a wrong reject-reason head is a violation" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :reject))
      wrong = %{c | payload: Map.put(c.payload, :expect_error, :not_the_real_head)}
      assert {:violation, {:guard_lint_wrong_reject_reason, _, _}} = Assay.run(wrong)
    end

    test "a broken :flip (identical base and variant) is a violation" do
      src = Gen.source("exhaustive/trichotomy")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/guard_lint",
          label: :none,
          payload: %{id: "x", transform: "t", relation: :flip, base_src: src, variant_src: src},
          note: "discrimination"
        )

      assert {:violation, {:guard_lint_relation_wrong, _, _, _}} = Assay.run(c)
    end
  end

  describe "two-sided catalog gate" do
    test "every cell's verdict and reject-head match the elaborator" do
      for c <- Gen.guard_lint_challenges() do
        assert Assay.run(c) == :ok, "catalog cell #{c.payload.id} disagrees with the elaborator"
      end
    end

    test "the catalog is two-sided and six cells" do
      expects = Gen.catalog() |> Enum.map(&elem(&1, 1))
      assert length(expects) == 6
      assert :accept in expects and :reject in expects
    end
  end

  describe "metamorphic gate" do
    test "every relation holds (drop_guard flips, alpha_rename holds)" do
      for c <- Gen.metamorphic_challenges() do
        assert Assay.run(c) == :ok,
               "metamorphic #{c.payload.id}/#{c.payload.transform} (#{c.payload.relation}) violated"
      end
    end

    test "drop_guard produces flips for exactly the two proven-exhaustive cells" do
      flips =
        Gen.metamorphic_challenges()
        |> Enum.filter(&(&1.payload.transform == "drop_guard"))
        |> Enum.map(& &1.payload.id)
        |> Enum.sort()

      assert flips == ["exhaustive/complement", "exhaustive/trichotomy"]
    end
  end

  describe "corpus round-trip" do
    test "an accept cell survives to_pieces/from_pieces" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :accept))
      {scaffold, pieces} = Challenge.to_pieces(c)
      c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert Assay.run(c2) == :ok
    end

    test "a reject cell (expect_error-carrying) survives to_pieces/from_pieces" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :reject))
      {scaffold, pieces} = Challenge.to_pieces(c)
      c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert c2.payload.expect_error == c.payload.expect_error
      assert Assay.run(c2) == :ok
    end
  end

  test "runner registry resolves the assay" do
    assert Antigen.Runner.assay_module_for("elab/guard_lint") == Antigen.Assays.Elab
  end
end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/antigen/elab_guard_lint_test.exs`
Expected: failures with `UndefinedFunctionError` on `Antigen.Generators.ElabGuardLint` and (for the hand-built flip-discrimination challenge) `FunctionClauseError` in `Antigen.Assays.Elab.run/1` (no `"elab/guard_lint"` clause yet).

- [ ] **Step 3: Implement generator, assay clauses, registry line**

(a) `lib/antigen/generators/elab_guard_lint.ex`:

```elixir
defmodule Antigen.Generators.ElabGuardLint do
  @moduledoc """
  Lint-soundness vertical for the Z3 guard-coverage lint (spec
  2026-07-08-guard-coverage-lint §6, locked Antigen-V6 decision): source-level
  `:elab_program` challenges pinning that `guard_chain`'s exhaustiveness
  recovery accepts exactly the hand-verified-exhaustive guard sets and nothing
  else. `drop_guard` (`:flip`) is the load-bearing pin: removing one guard
  from a proven-exhaustive set MUST flip accept -> reject — a lint that keeps
  accepting is over-proving (the soundness failure this assay exists to catch).
  `alpha_rename` (`:same`) pins frame-insensitivity. Transforms operate on the
  probe-fn BODY only, never `preamble <> body`.
  """

  alias Antigen.Challenge

  @preamble """
    type Nat = Z | S(Nat)
  """

  @doc "Wrap a probe body into a self-contained, elaborable module."
  @spec module(String.t()) :: String.t()
  def module(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  # -- Two-sided catalog: {id, expect, expect_error | nil, note, body} ---------
  @catalog [
    {"exhaustive/trichotomy", :accept, nil,
     "lt/eq/gt trichotomy over Int, no catch-all — the headline recovery cell",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x == b -> S(Z())
         x when x > b -> S(S(Z()))
     """},
    {"exhaustive/complement", :accept, nil,
     "two-guard complement over Int, no catch-all",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x >= b -> S(Z())
     """},
    {"gap/missing_eq", :reject, :unsupported_guard,
     "lt/gt with the equality case missing — genuinely non-exhaustive",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x > b -> S(Z())
     """},
    {"untranslatable/user_fn", :reject, :unsupported_guard,
     "semantically exhaustive via user Bool fns, but outside the fragment — K13 keeps it rejected",
     """
       fn pos(i: Int) -> Bool = i > 0
       fn nonpos(i: Int) -> Bool = i <= 0
       fn cls(n: Int) -> Nat = match n
         x when pos(x) -> Z()
         x when nonpos(x) -> S(Z())
     """},
    {"shadowed/with_catchall", :accept, nil,
     "repeated guard with a catch-all — warns (channel tested at unit level) but accepts",
     """
       fn cls(n: Int, b: Int) -> Nat = match n
         x when x < b -> Z()
         x when x < b -> S(Z())
         x -> S(S(Z()))
     """},
    {"control/guarded_catchall", :accept, nil,
     "structurally exhaustive control — the lint never runs here",
     """
       fn cls(n: Int) -> Nat = match n
         x when x == 0 -> Z()
         x -> S(Z())
     """}
  ]

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec guard_lint_challenges() :: [Challenge.t()]
  def guard_lint_challenges do
    Enum.map(@catalog, fn {id, expect, err, note, body} ->
      payload = %{id: id, src: module(body), expect: expect}
      payload = if err, do: Map.put(payload, :expect_error, err), else: payload

      Challenge.new(
        kind: :elab_program,
        assay: "elab/guard_lint",
        label: expect,
        payload: payload,
        note: note
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, expect, _e, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case entry(id) do
      {_id, _e, _err, _n, body} -> module(body)
      nil -> nil
    end
  end

  @doc "Look up a catalog entry's probe-fn BODY by id (transform input)."
  @spec body(String.t()) :: String.t() | nil
  def body(id) do
    case entry(id) do
      {_id, _e, _err, _n, body} -> body
      nil -> nil
    end
  end

  defp entry(id), do: Enum.find(@catalog, fn {i, _, _, _, _} -> i == id end)

  # -- Metamorphic challenges --------------------------------------------------

  @doc """
  Metamorphic challenges.

    * `drop_guard` (`:flip`) — on each proven-exhaustive ACCEPTING base, remove
      one guarded arm; the set is no longer exhaustive and the verdict must
      flip to reject. This is the lint-soundness pin (never over-prove).
    * `alpha_rename` (`:same`) — rename the guard-bound variable on EVERY
      base; the verdict must not change.
  """
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, expect, _err, _note, body} ->
      base_src = module(body)

      invariance =
        [{"alpha_rename", alpha_rename(body)}]
        |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
        |> Enum.map(fn {t, vbody} -> challenge(id, t, :same, base_src, module(vbody)) end)

      flips =
        case expect do
          :accept ->
            [{"drop_guard", drop_guard(body)}]
            |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
            |> Enum.map(fn {t, vbody} -> challenge(id, t, :flip, base_src, module(vbody)) end)

          _ ->
            []
        end

      invariance ++ flips
    end)
  end

  defp challenge(id, transform, relation, base_src, variant_src) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/guard_lint",
      label: :none,
      payload: %{
        id: id,
        transform: transform,
        relation: relation,
        base_src: base_src,
        variant_src: variant_src
      },
      note: "#{id} #{relation} under #{transform}"
    )
  end

  # -- Metamorphic transforms (probe-fn BODY input only) ------------------------

  # Remove the middle/closing guarded arm of a proven-exhaustive set. Matches on
  # the arm's CONTENT only (no leading-whitespace/newline dependence) — mirrors
  # ElabDotForcing's corrupt_dot/promote_use convention, which matches an
  # unanchored substring rather than an exact indented line, so this stays
  # correct regardless of how the `@catalog` heredocs happen to be indented
  # (the shadowed and control cells — whose arms differ — return nil and
  # produce no flip; a future rewording that removes the fragment entirely
  # would surface as a missing flip in "drop_guard produces flips for exactly
  # the two proven-exhaustive cells", not a silent no-op).
  defp drop_guard(body) do
    cond do
      String.contains?(body, "x when x == b -> S(Z())") ->
        remove_line_containing(body, "x when x == b -> S(Z())")

      String.contains?(body, "x when x >= b -> S(Z())") ->
        remove_line_containing(body, "x when x >= b -> S(Z())")

      true ->
        nil
    end
  end

  # Delete the one line containing `fragment` (indentation and all), leaving
  # the surrounding lines correctly stitched together.
  defp remove_line_containing(body, fragment) do
    body
    |> String.split("\n")
    |> Enum.reject(&String.contains?(&1, fragment))
    |> Enum.join("\n")
  end

  # Rename the guard-bound variable `x` consistently (alpha-equivalence);
  # standalone `x` only, so `x0` collisions cannot arise from the catalog text.
  defp alpha_rename(body), do: String.replace(body, ~r/\bx\b/, "x0")
end
```

Label-correctness argument the executor should sanity-check before the gate (read, don't run): the two `drop_guard` variants leave a SINGLE guarded arm as the final arm (`x < b` alone) — not exhaustive, Z3 refutes, `guard_chain` rejects `:non_exhaustive` → `:flip` holds. `alpha_rename` on `untranslatable/user_fn` renames `x` in both `cls` arms and in nothing else (`pos`/`nonpos` use `i`) — verdict-preserving. The shadowed cell's drop_guard is `nil` by construction (its arms contain neither guard fragment).

(b) `lib/antigen/assays/elab.ex` — insert after the `"elab/dot_forcing"` relation clause (after current line ~141), before the `elab/soundness` clauses, mirroring the dot_forcing pair exactly:

```elixir
  # elab/guard_lint — catalog form (spec 2026-07-08-guard-coverage-lint §6):
  # hand-verified exhaustive/non-exhaustive labels, two-sided; reject cells pin
  # the error HEAD (:unsupported_guard) so a fixture that rots into rejecting
  # for an unrelated reason (parse error, unbound name) infects.
  def run(%Challenge{kind: :elab_program, assay: "elab/guard_lint", payload: %{expect: expect} = p}) do
    result = elaborate(p.src)
    actual = verdict_bit(result)

    cond do
      actual != expect ->
        {:violation, {:guard_lint_verdict_wrong, p.id, %{expected: expect, actual: actual}}}

      actual == :reject and Map.has_key?(p, :expect_error) ->
        got = reject_head(result)

        if got == p.expect_error do
          :ok
        else
          {:violation, {:guard_lint_wrong_reject_reason, p.id, got}}
        end

      true ->
        :ok
    end
  end

  # elab/guard_lint — relation form: `:same` (verdict invariant under a
  # typing-preserving perturbation) or `:flip` (dropping a guard from a
  # proven-exhaustive set must flip accept -> reject — the never-over-prove pin).
  def run(%Challenge{kind: :elab_program, assay: "elab/guard_lint", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation,
       {:guard_lint_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end
```

(c) `lib/antigen/runner.ex` — after line 350 (`defp assay_module("elab/dot_forcing"), do: Antigen.Assays.Elab`):

```elixir
  defp assay_module("elab/guard_lint"), do: Antigen.Assays.Elab
```

- [ ] **Step 4: Run to verify green**

Run: `mix test test/antigen/elab_guard_lint_test.exs`
Expected: 11 tests, 0 failures. A catalog-gate failure here means a LABEL disagrees with the elaborator — STOP and report (spec §3: the lint must never prove exhaustive a set that isn't; a label contradiction is a real finding, not a fixture to "fix").

- [ ] **Step 5: Run the neighboring Antigen suites**

Run: `mix test test/antigen/elab_dot_forcing_test.exs test/antigen/elab_erasure_test.exs`
Expected: all pass (the new clauses must not shadow or reorder existing dispatch).

- [ ] **Step 6: Commit**

```bash
git add -- lib/antigen/generators/elab_guard_lint.ex lib/antigen/assays/elab.ex lib/antigen/runner.ex test/antigen/elab_guard_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): elab/guard_lint lint-soundness vertical (catalog + drop_guard flip)" \
  -- lib/antigen/generators/elab_guard_lint.ex lib/antigen/assays/elab.ex lib/antigen/runner.ex test/antigen/elab_guard_lint_test.exs
```

---

### Task 4: `bool_elim` vocabulary cleanup, roadmap note, full gate

**Files:**
- Modify (comments/docs ONLY — zero executable-code changes): `lib/cure/elab/elaborator.ex`, `lib/cure/elab/declarations.ex`, `lib/antigen/assays/dot_forcing.ex`
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (row 4, one sentence)
- Verified-no-change: `lib/std/bool.cure` (its `bool_elim` mention is historically accurate — "retiring the bespoke `bool_elim` primitive"), `lib/antigen/generators/totality.ex` (line 313 historically accurate; `diverging_bool_elim_branch`/`terminating_bool_elim_branch` are kept-forever test-pinned identifiers; `note:` strings are challenge DATA, not comments — leave all of it), `lib/cure/core/kernel.ex` (no `bool_elim` mention exists).

- [ ] **Step 1: Rewrite the eight stale elaborator comments**

These are the current stale texts (re-grep `bool_elim` in `lib/cure/elab/` first; if line drift moved them, match on text — plan-time verification ran `grep -n bool_elim lib/cure/elab/elaborator.ex` and found 11 matching lines grouping into the EIGHT distinct comment sections numbered below, not five/six as earlier spec drafts of this section counted; items 2 and 3 close that gap). Reword each so it describes the `:case`-on-Bool lowering that exists (`bool_case/5`), keeping surrounding comment density and style. Required outcomes:

1. `try_guard_match` header comment (~2387, partially rewritten in Task 2's Step 3 — finish it if any `bool_elim` text remains): describe the chain as `:case`-on-Bool via `bool_case/5`, mention the lint recovery, keep the variable-scrutinee rationale.
2. `elaborate_match`'s nested-guard `with`-chain comment (~1321-1326, inside the `desugar_nested_arms` clause): "leaf folds the reached rows into a `bool_elim` `if`-chain whose tail is" → "leaf folds the reached rows into a `:case`-on-Bool `if`-chain whose tail is"; keep the rest of the sentence (Wadler/Augustsson `match … default` / Idris `CaseBuilder` errorCase framing) untouched.
3. `elaborate_match`'s single-level ctor-guard comment (~1328-1331, inside the `desugar_ctor_guards` clause): "matrix) is folded into a guardless arm whose body is a `bool_elim`\n# `if`-chain over the constructor group's rows" → "matrix) is folded into a guardless arm whose body is a `:case`-on-Bool\n# `if`-chain over the constructor group's rows"; keep the rest of the sentence (same-constructor fall-through / `:vdata` path framing) untouched.
4. `bind_once_guard` comment (~2406-2410): "across the `bool_elim` chain" → "across the guard chain".
5. The guarded-arm comment (~2447) — already replaced verbatim in Task 2 Step 3(b).
6. `try_literal_match` comment (~2499-2505): "desugar to a chain of Boolean eliminations… becomes `bool_elim (n == 0) a b`" → "desugar to a chain of `:case`-on-Bool decisions (`bool_case/5`)… becomes `case (n == 0) of True -> a | False -> b`"; keep the no-`:vdata` rationale sentence.
7. Ctor-guard section comment (~2660-2662): "the `if`s lower to the committed `bool_elim`" → "the `if`s lower to `:case` on the inductive Bool (through the general `:conditional` clause)".
8. Matrix comment (~2952): "folded into a `bool_elim` `if`-chain" → "folded into a `:case`-on-Bool `if`-chain".

And `lib/cure/elab/declarations.ex:374-375`: "(a constant-motive bool_elim)" → "(a constant-motive `:case` on the inductive Bool)".

- [ ] **Step 2: Fix the `dot_forcing.ex` moduledoc claim**

In `lib/antigen/assays/dot_forcing.ex`'s moduledoc, the sentence claiming the carried-eq dispatch "is exercised end-to-end by that spec's unit tests and the `nidot` ni03/ni07" oracle fixtures is stale: replace the ni03/ni07 part so the paragraph states — ni03/ni07 landed as the SIMPLIFIED directly-invertible two-index family (Idris cannot express the carried differential without a `with` block), so they do NOT reach the carried-eq branch; end-to-end carried coverage lives in `test/cure/elab/named_implicit_tail_test.exs` and the `Antigen.Generators.ElabDotForcing` catalog's carried cells. Keep the rest of the moduledoc untouched.

- [ ] **Step 3: Roadmap row 4 note**

In `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`, append one sentence to row 4's status prose: "Z3 guard-coverage lint landed (spec 2026-07-08-guard-coverage-lint): provably-exhaustive guard chains (trichotomy-style, Int fragment) no longer need a catch-all at the `guard_chain` site — a deliberate extension beyond Idris, foundation-spec-authorized; ctor-group sites stay conservative (K13), shadowed guards warn."

- [ ] **Step 4: Verify the cleanup is comment/doc-only and the grep criterion holds**

Run: `git diff --stat` then `git diff -- lib/cure/elab/elaborator.ex lib/cure/elab/declarations.ex lib/antigen/assays/dot_forcing.ex` — every hunk in this task must be inside a comment, `@moduledoc`, or `@doc`.
Run: `grep -rn bool_elim lib/ --include='*.ex' --include='*.cure'`
Expected remaining matches ONLY: `lib/std/bool.cure` (historically accurate), `lib/antigen/generators/totality.ex` (historically-accurate line ~313 + the two kept-forever identifiers and their docs/notes). Anything else = a missed stale mention; reword it.

- [ ] **Step 5: Commit the cleanup**

```bash
git add -- lib/cure/elab/elaborator.ex lib/cure/elab/declarations.ex lib/antigen/assays/dot_forcing.ex docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs: retire stale bool_elim vocabulary; correct dot_forcing ni03/ni07 claim; roadmap row-4 lint note" \
  -- lib/cure/elab/elaborator.ex lib/cure/elab/declarations.ex lib/antigen/assays/dot_forcing.ex docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
```

- [ ] **Step 6: Full gate (ONE at a time, in this order, nothing else running)**

1. `mix test test/antigen/` — expected: 486 tests (475 + 11 new), 0 failures.
2. `mix test` — expected: ~3226 tests (3195 + 20 + 11 new), 0 failures, includes `oracle_replay_test.exs` green (re-verifying that `guard/guard01–06` and `guardscrut/gs01–03` stayed relation-`same` — the lint touched none of them). One known non-reproducible Antigen-seed flake exists; if you see exactly one Antigen seed failure, re-run the full suite once (alone); if it doesn't reproduce, note it honestly in the report. Any other failure = STOP and report.

- [ ] **Step 7: Final verification**

- `git diff --stat <first-task-1-commit>~1 HEAD -- lib/cure/core/` must be EMPTY.
- `git diff --stat <first-task-1-commit>~1 HEAD -- lib/cure/types/ lib/cure/compiler/` must be EMPTY.
- `git log --format='%an %ae' <first-task-1-commit>~1..HEAD` shows only `Made In Heaven madeinheaven@madeinheaven.com`.

---

## Self-review notes (spec-coverage map)

- §1/§2.1/§2.3a recovery → Task 2. §2.2 translator + K13 → Task 1 (unit) + Task 2 (`untranslatable` integration test) + Task 3 (`untranslatable/user_fn` cell). §2.1 shadow → Tasks 1/2. §2.4 Process-only reuse → Task 1 Step 3. §2.5 warnings channel + reset → Tasks 1/2. §3 trust boundary → global constraints + Task 4 Step 7. §4 no-oracle-probes + replay → Task 4 Step 6; row-4 note → Task 4 Step 3. §5 cleanup inventory → Task 4 Steps 1-2 (with the verified-no-change list). §6 unit/integration/Antigen/gate → Tasks 1/2/3/4. §8.6 grep → Task 4 Step 4.
- The pinned-fixture audit is already recorded as SATISFIED in the spec (§6); Task 2 Step 5 re-checks it empirically.
- #15 interplay: after this lands, add a note to task #15 that its prim→delta-globals retarget must update `GuardLint`'s `{:prim, …}` recognizer (one clause each in `bool_form`/`int_form`) — orchestrator action, not part of this plan's tasks.
