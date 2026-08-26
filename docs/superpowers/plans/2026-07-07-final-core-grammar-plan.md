# Final-Core Grammar Validator Scaffold (Wave 0 / K11a) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the `Cure.Core.Validator` grammar-boundary scaffold plus the subject-reduction (#638) and progress (#639) regression harnesses, so every later cleanup wave has an executable "which constructs are still legacy" checklist and a metatheory guardrail.

**Architecture:** A new `Cure.Core.Validator` module walks a Core term and, for each named grammar **clause**, emits a diagnostic tagged with that clause's current **mode** (`:off | :warn | :reject`) drawn from a config map. The full clause set encodes the *entire* Final-Core target grammar (spec §A/§J); Wave-0 modes run it as pure instrumentation (legacy-detecting clauses `:warn`, not-yet-reshaped clauses `:off`, **no clause `:reject`**). It is wired into `Cure.Core.Kernel.check_def/2` — scanning both the declared type and the body — to surface warnings via `Cure.Pipeline.Events` and to reject only when a clause is config-overridden to `:reject` (the flip mechanism, exercised in tests, enabled per-wave later). A separate `Cure.Core.MetaCheck` module holds two property predicates — `type_preserved?/2` (#638) and `progresses?/2` (#639) — driven over seed corpora by two harness test files.

**Tech Stack:** Elixir, ExUnit (`mix test`), the existing `Cure.Core` kernel (`term.ex`, `kernel.ex`, `normalise.ex`, `conv.ex`, `value.ex`), `Cure.Pipeline.Events`.

## Global Constraints

- Language is Elixir; all tests run via `mix test <path>`; a compile error counts as a failing test (red).
- **Scope is K11a ONLY.** Do NOT add grade fields to binders, delete any node, change `term.ex` node arities, or introduce qualified `Sym`/level-expression representations — those are later waves. This task builds the *scaffold that will check for* those shapes, not the shapes.
- **The Wave-0 default config has NO `:reject` clause.** Wiring into the kernel MUST be non-breaking: every definition the kernel admits today still admits after wiring. Verify with the full suite.
- `kernel.ex` is inside the TCB. Its change here (an added, default-non-rejecting validator call in `check_def`) is a grammar-boundary addition pre-approved as Agda/Lean-aligning, but the **full `mix test` gate must pass** before the run is declared done.
- **Only one build/test run at a time.** Never launch concurrent `mix test` invocations — a past concurrent full-suite run caused a kernel panic. Serialize all suites.
- Git commits are single-author — do NOT add any `Co-Authored-By` / co-sign trailer.
- Clause names are fixed identifiers reused across tasks; use them verbatim: `grade_on_binders`, `usage_relevance`, `no_eq_node`, `no_prim_node`, `no_hole`, `qualified_syms`, `ctor_signature`, `case_coverage`, `level_expr`, `no_absurd_node`, `no_legacy_reducer`.
- **Strict TDD, every task:** write the failing test (red) → run it and confirm the failure reason matches (Step 2) → write the minimal implementation that makes it green (Step 3/4) → only then, if the new code introduces duplication or an awkward shape (e.g. the accumulating `violation/2` clauses across Tasks 3–4), refactor with the full `test/cure/core/validator_test.exs` suite kept green throughout. Never write implementation ahead of its test.
- **Tests are immutable once green.** A test that starts failing after a later change is a signal the implementation regressed — fix the implementation, never the test. The only exception is a test proven to encode the wrong behavior (state the proof before touching it); "it's faster to edit the test" is never a valid reason. This applies to every test file this plan creates.
- **Tests assert behavior through the public interface**, never private helpers: no test in this plan may call `children/1` or `violation/2` (both private) directly — only `Validator.clauses/0`, `wave0_config/0`, `nodes/1`, `validate/1,2`, `check_def_config/0`, `Kernel.check_def/2`, `MetaCheck.type_preserved?/2`, and `MetaCheck.progresses?/2`.

---

## File Structure

- Create `lib/cure/core/validator.ex` — `Cure.Core.Validator`: clause registry, Wave-0 config, node walker, clause predicates, `validate/2`, `check_def_config/0`.
- Create `lib/cure/core/meta_check.ex` — `Cure.Core.MetaCheck`: `type_preserved?/2` (#638), `progresses?/2` (#639).
- Modify `lib/cure/core/kernel.ex` — wire the validator into `check_def/2` (both the declared type and the body).
- Modify `lib/cure/pipeline/events.ex` — register the new `:kernel` pipeline stage.
- Create `test/cure/core/validator_test.exs` — validator clause + config + walker + validate tests.
- Create `test/cure/core/subject_reduction_test.exs` — #638 harness over a seed corpus.
- Create `test/cure/core/progress_test.exs` — #639 harness over a seed corpus.

Clause → Wave-0 mode (the default config, encoded in Task 1):

| Clause | Wave-0 mode | Why |
|---|---|---|
| `no_hole` | `:warn` | holes appear in current terms; log them (flips `:reject` at K3/Wave 1) |
| `no_eq_node` | `:warn` | legacy `{:eq}/{:refl}/{:rewrite}` present today |
| `no_prim_node` | `:warn` | legacy `{:prim}` present today |
| `no_absurd_node` | `:warn` | legacy `{:absurd}` present today |
| `grade_on_binders` | `:off` | binders carry no grade yet — would fire on every node |
| `qualified_syms` | `:off` | globals/data/ctor are bare atoms today — would fire on every node |
| `level_expr` | `:off` | levels are integers today — would fire on every `:type` |
| `ctor_signature` | `:off` | needs signature resolution (not a pure structural check) |
| `case_coverage` | `:off` | needs the family env (not a pure structural check) |
| `usage_relevance` | `:off` | a typing rule, enforced in the kernel when its wave lands |
| `no_legacy_reducer` | `:off` | a reduction-behavior rule, not structural |

---

### Task 1: Validator skeleton — clause registry, Wave-0 config, diagnostic type

**Files:**
- Create: `lib/cure/core/validator.ex`
- Test: `test/cure/core/validator_test.exs`

**Interfaces:**
- Produces: `Cure.Core.Validator.clauses/0 :: [atom()]`, `Cure.Core.Validator.wave0_config/0 :: %{atom() => :off | :warn | :reject}`. Diagnostic shape `%{clause: atom(), mode: mode(), message: String.t(), node: tuple()}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/validator_test.exs
defmodule Cure.Core.ValidatorTest do
  # async: false — Task 5 adds a test that calls `Application.put_env(:cure,
  # :final_core_config, …)`. That key is process-independent GLOBAL state read
  # by `Kernel.check_def/2` (the shared TCB entry point every other `test/cure/core/`
  # suite also calls). Running this file concurrently with another async suite
  # while the override is live would risk a spurious cross-file rejection the
  # moment any other suite's checked def contains a hole. Given this codebase's
  # own history of kernel-related test-concurrency hazards (see Global
  # Constraints), keep this whole file serial rather than relying on no other
  # suite ever adding a hole-bearing `check_def` call.
  use ExUnit.Case, async: false
  alias Cure.Core.Validator

  describe "clause registry and Wave-0 config" do
    test "wave0_config assigns a mode to every registered clause and no others" do
      assert MapSet.new(Map.keys(Validator.wave0_config())) == MapSet.new(Validator.clauses())
    end

    test "no clause is :reject in Wave 0 (pure instrumentation)" do
      refute Enum.any?(Validator.wave0_config(), fn {_c, mode} -> mode == :reject end)
    end

    test "legacy-detecting clauses warn; not-yet-reshaped clauses are off" do
      cfg = Validator.wave0_config()
      assert cfg.no_hole == :warn
      assert cfg.no_eq_node == :warn
      assert cfg.no_prim_node == :warn
      assert cfg.no_absurd_node == :warn
      assert cfg.grade_on_binders == :off
      assert cfg.qualified_syms == :off
      assert cfg.level_expr == :off
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/validator_test.exs`
Expected: FAIL — `Cure.Core.Validator` is undefined (compile error).

- [ ] **Step 3: Write minimal implementation**

```elixir
# lib/cure/core/validator.ex
defmodule Cure.Core.Validator do
  @moduledoc """
  The Final-Core grammar boundary (Wave 0 / K11a).

  Structurally checks a Core term against the *target* Final-Core grammar (design
  spec §A/§J). Each grammar commitment is a named **clause** with a **mode**:

    * `:off`    — not checked (target shape does not exist in the grammar yet, or
                  the clause is non-structural and enforced elsewhere).
    * `:warn`   — violation detected and reported, not rejected.
    * `:reject` — violation is a hard error.

  Wave-0 runs as pure instrumentation: legacy-detecting clauses `:warn`, the rest
  `:off`, none `:reject`. Each wave flips its clause to `:reject` as the kernel
  stops producing the legacy form. This module never type-checks — that is the
  kernel's job; non-structural clauses (`ctor_signature`, `case_coverage`,
  `usage_relevance`, `no_legacy_reducer`) are registered for completeness but have
  no structural predicate and are enforced in the kernel/reducer when their wave
  lands.
  """

  @type mode :: :off | :warn | :reject
  @type clause :: atom()
  @type config :: %{clause() => mode()}
  @type diagnostic :: %{clause: clause(), mode: mode(), message: String.t(), node: tuple()}

  @clauses [
    :grade_on_binders,
    :usage_relevance,
    :no_eq_node,
    :no_prim_node,
    :no_hole,
    :qualified_syms,
    :ctor_signature,
    :case_coverage,
    :level_expr,
    :no_absurd_node,
    :no_legacy_reducer
  ]

  @wave0_config %{
    grade_on_binders: :off,
    usage_relevance: :off,
    no_eq_node: :warn,
    no_prim_node: :warn,
    no_hole: :warn,
    qualified_syms: :off,
    ctor_signature: :off,
    case_coverage: :off,
    level_expr: :off,
    no_absurd_node: :warn,
    no_legacy_reducer: :off
  }

  @doc "Every registered grammar clause (the executable checklist)."
  @spec clauses() :: [clause()]
  def clauses, do: @clauses

  @doc "The Wave-0 default mode for every clause (pure instrumentation; no :reject)."
  @spec wave0_config() :: config()
  def wave0_config, do: @wave0_config
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/validator_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/validator.ex test/cure/core/validator_test.exs
git commit -m "feat(core): Validator clause registry + Wave-0 config (K11a)"
```

---

### Task 2: The node walker

**Files:**
- Modify: `lib/cure/core/validator.ex`
- Test: `test/cure/core/validator_test.exs`

**Interfaces:**
- Produces: `Cure.Core.Validator.nodes/1 :: (tuple()) -> [tuple()]` — pre-order list of every Core sub-term (the term itself first). Handles nested binders, `:data` params/indices, `:ctor` args, and `:case` scrutinee/motive/branch-bodies, and does NOT mis-read a `:case` branch tuple `{ctor, arity, body}` as a node.

- [ ] **Step 1: Write the failing test**

```elixir
# add inside test/cure/core/validator_test.exs
  describe "nodes/1 walker" do
    test "enumerates the term and all sub-terms pre-order" do
      term = {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_lit, 3}}
      got = Cure.Core.Validator.nodes(term)
      assert hd(got) == term
      assert {:lam, {:type, 0}, {:var, 0}} in got
      assert {:type, 0} in got
      assert {:var, 0} in got
      assert {:int_lit, 3} in got
    end

    test "descends into case scrut/motive/branch bodies without yielding branch tuples" do
      # a branch for a constructor literally named :refl must NOT surface as a {:refl, _} node
      term = {:case, {:var, 0}, {:type, 0}, [{:refl, 1, {:var, 0}}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:var, 0} in got
      assert {:type, 0} in got
      refute Enum.any?(got, &match?({:refl, _}, &1))
    end

    test "descends into data params/indices and ctor args" do
      term = {:data, :Vec, [{:int_type}], [{:int_lit, 2}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:int_type} in got
      assert {:int_lit, 2} in got
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/validator_test.exs`
Expected: FAIL — `nodes/1` undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# add to lib/cure/core/validator.ex

  @doc "All Core sub-terms of `term`, pre-order (the term itself first)."
  @spec nodes(tuple()) :: [tuple()]
  def nodes(term), do: [term | Enum.flat_map(children(term), &nodes/1)]

  # Immediate Core-term children (NOT the term itself). Both the current binder
  # forms and the future graded 4-tuple forms are matched so the walker survives
  # the later grade reshape. `:case` branches are descended structurally (body
  # only) so a branch tuple is never treated as a node.
  defp children({:pi, dom, cod}), do: [dom, cod]
  defp children({:pi, _grade, dom, cod}), do: [dom, cod]
  defp children({:lam, dom, body}), do: [dom, body]
  defp children({:lam, _grade, dom, body}), do: [dom, body]
  defp children({:sigma, a, b}), do: [a, b]
  defp children({:sigma, _grade, a, b}), do: [a, b]
  defp children({:app, f, a}), do: [f, a]
  defp children({:pair, a, b}), do: [a, b]
  defp children({:fst, p}), do: [p]
  defp children({:snd, p}), do: [p]
  defp children({:data, _n, ps, is}), do: ps ++ is
  defp children({:ctor, _n, args}), do: args
  defp children({:case, s, m, brs}), do: [s, m | Enum.map(brs, fn {_c, _ar, body} -> body end)]
  defp children({:eq, ty, a, b}), do: [ty, a, b]
  defp children({:refl, a}), do: [a]
  defp children({:rewrite, p, m, b}), do: [p, m, b]
  defp children({:prim, _op, args}), do: args
  defp children(_leaf), do: []
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/validator_test.exs`
Expected: PASS (6 tests total).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/validator.ex test/cure/core/validator_test.exs
git commit -m "feat(core): Validator node walker (case-branch safe)"
```

---

### Task 3: Wave-0-active clause predicates + `validate/2` partitioning

**Files:**
- Modify: `lib/cure/core/validator.ex`
- Test: `test/cure/core/validator_test.exs`

**Interfaces:**
- Produces: `Cure.Core.Validator.validate/1` and `validate/2 :: (tuple(), config()) -> {:ok, [diagnostic()]} | {:error, [diagnostic()]}`. `{:ok, warnings}` when no `:reject` diagnostics; `{:error, rejections}` otherwise. Wave-0-active predicates for `no_hole`, `no_eq_node`, `no_prim_node`, `no_absurd_node`.

- [ ] **Step 1: Write the failing test**

```elixir
# add inside test/cure/core/validator_test.exs
  describe "validate/2 (Wave-0 active clauses)" do
    alias Cure.Core.Validator

    test "a clean current-grammar term yields no diagnostics" do
      assert {:ok, []} = Validator.validate({:lam, {:type, 0}, {:var, 0}})
    end

    test "a legacy :eq node warns under Wave-0 config" do
      assert {:ok, [w]} = Validator.validate({:eq, {:type, 0}, {:var, 0}, {:var, 0}})
      assert w.clause == :no_eq_node and w.mode == :warn
    end

    test "a hole warns under Wave-0 config (does not reject yet)" do
      assert {:ok, [w]} = Validator.validate({:hole, :h0})
      assert w.clause == :no_hole and w.mode == :warn
    end

    test "an :absurd node and a :prim node each warn" do
      assert {:ok, [%{clause: :no_absurd_node}]} = Validator.validate({:absurd})
      assert {:ok, [%{clause: :no_prim_node}]} = Validator.validate({:prim, :add, [{:int_lit, 1}, {:int_lit, 2}]})
    end

    test "config override to :reject flips admission (the per-wave flip mechanism)" do
      cfg = Map.put(Validator.wave0_config(), :no_hole, :reject)
      assert {:error, [r]} = Validator.validate({:hole, :h0}, cfg)
      assert r.clause == :no_hole and r.mode == :reject
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/validator_test.exs`
Expected: FAIL — `validate/2` undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# add to lib/cure/core/validator.ex

  @doc "Validate `term` against the Wave-0 config."
  @spec validate(tuple()) :: {:ok, [diagnostic()]} | {:error, [diagnostic()]}
  def validate(term), do: validate(term, @wave0_config)

  @doc """
  Validate `term` against `config`. Returns `{:error, rejections}` if any
  `:reject`-mode clause is violated, else `{:ok, warnings}`.
  """
  @spec validate(tuple(), config()) :: {:ok, [diagnostic()]} | {:error, [diagnostic()]}
  def validate(term, config) do
    diags =
      for node <- nodes(term),
          {clause, mode} <- config,
          mode != :off,
          msg = violation(clause, node),
          msg != nil do
        %{clause: clause, mode: mode, message: msg, node: node}
      end

    case Enum.filter(diags, &(&1.mode == :reject)) do
      [] -> {:ok, Enum.filter(diags, &(&1.mode == :warn))}
      rejections -> {:error, rejections}
    end
  end

  # -- clause predicates: node -> nil (ok) | message (violation) --------------
  # Wave-0-active (legacy-form detectors). Match exact node arities so a :case
  # branch never collides with a 2-tuple :refl node.

  defp violation(:no_hole, {:hole, _}), do: "hole present in Core term (K3)"

  defp violation(:no_eq_node, {:eq, _, _, _}), do: "primitive :eq node; use inductive Eq (K1)"
  defp violation(:no_eq_node, {:refl, _}), do: "primitive :refl node; use ctor refl (K1)"
  defp violation(:no_eq_node, {:rewrite, _, _, _}), do: "primitive :rewrite node; use case-sugar (K1)"

  defp violation(:no_prim_node, {:prim, _, _}), do: "primitive :prim node; use delta-globals (K2)"

  defp violation(:no_absurd_node, {:absurd}), do: "absurd node; use empty case (K4)"

  # non-firing fallback for every clause/node not matched above
  defp violation(_clause, _node), do: nil
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/validator_test.exs`
Expected: PASS (11 tests total).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/validator.ex test/cure/core/validator_test.exs
git commit -m "feat(core): Validator active clauses + validate/2 partitioning"
```

---

### Task 4: Deferred checklist clause predicates (`:off`, ready to flip)

**Files:**
- Modify: `lib/cure/core/validator.ex`
- Test: `test/cure/core/validator_test.exs`

**Interfaces:**
- Produces: structural predicates for `grade_on_binders`, `qualified_syms`, `level_expr` that recognize the *legacy* shape (fire when the clause is turned on). `ctor_signature`, `case_coverage`, `usage_relevance`, `no_legacy_reducer` remain non-firing (documented as non-structural). These predicates must sit ABOVE the catch-all `violation(_, _)` clause added in Task 3.

- [ ] **Step 1: Write the failing test**

```elixir
# add inside test/cure/core/validator_test.exs
  describe "deferred clauses recognize legacy shape when flipped on" do
    alias Cure.Core.Validator

    test "grade_on_binders fires on a current (ungraded) binder when set to :warn" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      assert {:ok, ws} = Validator.validate({:pi, {:type, 0}, {:var, 0}}, cfg)
      assert Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "grade_on_binders does NOT fire on a hypothetical graded binder" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      graded = {:pi, :omega, {:type, 0}, {:var, 0}}
      assert {:ok, ws} = Validator.validate(graded, cfg)
      refute Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "qualified_syms fires on a bare-atom global; level_expr fires on an integer level" do
      cfg =
        Validator.wave0_config()
        |> Map.put(:qualified_syms, :warn)
        |> Map.put(:level_expr, :warn)

      assert {:ok, ws} = Validator.validate({:app, {:global, :foo}, {:type, 2}}, cfg)
      assert Enum.any?(ws, &(&1.clause == :qualified_syms))
      assert Enum.any?(ws, &(&1.clause == :level_expr))
    end

    test "in Wave-0 config these deferred clauses stay silent (are :off)" do
      assert {:ok, []} = Validator.validate({:pi, {:type, 0}, {:global, :foo}})
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/validator_test.exs`
Expected: FAIL — deferred predicates not implemented (they currently hit the catch-all and return nil, so the `:warn` assertions fail).

- [ ] **Step 3: Write minimal implementation**

```elixir
# add to lib/cure/core/validator.ex, ABOVE the catch-all `violation(_clause, _node)` clause

  # grade_on_binders — current 3-tuple binders carry no grade; the future graded
  # 4-tuple forms ({:pi, grade, dom, cod}) do NOT match and so pass.
  defp violation(:grade_on_binders, {:pi, _, _}), do: "pi binder carries no grade"
  defp violation(:grade_on_binders, {:lam, _, _}), do: "lam binder carries no grade"
  defp violation(:grade_on_binders, {:sigma, _, _}), do: "sigma binder carries no grade"

  # qualified_syms — bare-atom identity instead of a qualified Sym.
  defp violation(:qualified_syms, {:global, n}) when is_atom(n),
    do: "global uses a bare atom, not a qualified symbol (K12)"

  defp violation(:qualified_syms, {:data, n, _, _}) when is_atom(n),
    do: "data family uses a bare atom, not a qualified symbol (K12)"

  defp violation(:qualified_syms, {:ctor, n, _}) when is_atom(n),
    do: "constructor uses a bare atom, not a qualified symbol (K12)"

  # level_expr — integer level instead of a level-expression.
  defp violation(:level_expr, {:type, l}) when is_integer(l),
    do: "universe level is an integer, not a level-expression (K7)"

  # ctor_signature / case_coverage / usage_relevance / no_legacy_reducer are
  # non-structural (need the env / typing / reduction) — enforced in the kernel
  # when their wave lands, never here. They fall through to the catch-all.
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/validator_test.exs`
Expected: PASS (15 tests total).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/validator.ex test/cure/core/validator_test.exs
git commit -m "feat(core): Validator deferred checklist clauses (off, ready to flip)"
```

---

### Task 5: Wire the validator into `Kernel.check_def/2`

**Files:**
- Modify: `lib/cure/core/validator.ex` (add `check_def_config/0`)
- Modify: `lib/cure/core/kernel.ex` (`check_def/2`)
- Modify: `lib/cure/pipeline/events.ex` (register the new `:kernel` stage atom)
- Test: `test/cure/core/validator_test.exs`

**Interfaces:**
- Consumes: `Validator.validate/2`, `Validator.wave0_config/0`.
- Produces: `Cure.Core.Validator.check_def_config/0 :: () -> config()` (defaults to `wave0_config/0`, overridable via `Application.get_env(:cure, :final_core_config, ...)`). `Kernel.check_def/2` unchanged signature `:ok | {:error, term()}`; now emits `{:final_core_violation, [diagnostic()]}` errors only when a clause is config-overridden to `:reject`. The validator scans **both** the declared `type_term` and the `body_term` — a legacy node in a signature (e.g. a `:eq` node used as a definition's type) is just as much a grammar-boundary hit as one in the body, and the checklist's job is to name every legacy construct still reachable through a checked def, not just half of it.

- [ ] **Step 1: Write the failing test**

```elixir
# add inside test/cure/core/validator_test.exs
  describe "check_def_config/0 and kernel wiring" do
    alias Cure.Core.{Validator, Env, Kernel}

    test "check_def_config defaults to the Wave-0 config" do
      assert Validator.check_def_config() == Validator.wave0_config()
    end

    test "a clean def still admits under the default (non-breaking)" do
      # idty : Type 0 -> Type 0  ;  body = λx. x  (clean, admits)
      env = Env.add_def(Env.empty(), :idty, {:pi, {:type, 0}, {:type, 0}}, {:lam, {:type, 0}, {:var, 0}})
      assert :ok == Kernel.check_def(env, :idty)
    end

    test "with a reject-override config, a hole-bearing def fails admission" do
      env = Env.add_def(Env.empty(), :withhole, {:pi, {:type, 0}, {:type, 0}}, {:lam, {:type, 0}, {:hole, :h}})

      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_hole, :reject))
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, [%{clause: :no_hole}]}} = Kernel.check_def(env, :withhole)
    end

    test "a legacy node in the declared TYPE is caught too, not just the body" do
      # helper : Eq(Int, 1, 1) ; body = refl(1) — a legacy `:eq` node used AS a
      # definition's type (still typeable pre-K1). `eqty` reuses that same `:eq`
      # type but its body is a clean `{:global, :helper}` reference, so the ONLY
      # legacy node reachable from `eqty`'s own {type_term, body_term} pair is in
      # its type_term. If the wiring only scanned body_term (the pre-fix shape),
      # this def would wrongly admit even under a :reject override.
      eq_ty = {:eq, {:int_type}, {:int_lit, 1}, {:int_lit, 1}}

      env =
        Env.empty()
        |> Env.add_def(:helper, eq_ty, {:refl, {:int_lit, 1}})
        |> Env.add_def(:eqty, eq_ty, {:global, :helper})

      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_eq_node, :reject))
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :eqty)
      assert Enum.any?(rejections, &(&1.clause == :no_eq_node))
    end
  end
```

`Env` is `Cure.Core.Env` (defined in `lib/cure/core/inductive.ex`): `Env.empty/0` constructs it and `Env.add_def(env, name, type_term, body_term)` registers a def (verified against `test/cure/core/def_test.exs`).

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/validator_test.exs`
Expected: FAIL — `check_def_config/0` undefined, `check_def` does not yet reject holes, and the type-term test fails (the def wrongly admits).

- [ ] **Step 3: Write minimal implementation**

```elixir
# add to lib/cure/core/validator.ex
  @doc "Active config for kernel admission; Wave-0 by default, overridable in config/tests."
  @spec check_def_config() :: config()
  def check_def_config, do: Application.get_env(:cure, :final_core_config, @wave0_config)
```

`check_def/2`'s existing shape (unchanged except the marked line) is:

```elixir
  @spec check_def(Env.t(), atom()) :: :ok | {:error, term()}
  def check_def(env, name) do
    case Env.get_def(env, name) do
      nil ->
        {:error, :unknown_global}

      %{type: type_term, body: body_term} ->
        ctx = Context.empty(env)

        with {:ok, _level} <- infer_sort(ctx, type_term),
             :ok <- check(ctx, body_term, Eval.eval(type_term, [])),
             :ok <- run_final_core_validator(type_term, body_term) do  # <-- changed line
          :ok
        end
    end
  end
```

The current file has no validator call at all — `check_def/2`'s `with` today ends at `check(ctx, body_term, Eval.eval(type_term, []))`. The only change is adding one new `with` step calling the new `run_final_core_validator/2` (defined below, scanning both `type_term` and `body_term`); the `nil ->` branch and every line above the marked one are copied verbatim from the current file. Add the new private helper below `check_def/2`:

```elixir
  # Grammar-boundary instrumentation (K11a). Scans BOTH the declared type and
  # the body — a legacy node in a signature is as much a checklist hit as one
  # in the body. Emits warnings via the pipeline and rejects only clauses
  # configured to :reject (none, by Wave-0 default); on a mixed verdict,
  # rejections from either term are combined.
  defp run_final_core_validator(type_term, body_term) do
    cfg = Cure.Core.Validator.check_def_config()

    case {Cure.Core.Validator.validate(type_term, cfg), Cure.Core.Validator.validate(body_term, cfg)} do
      {{:ok, w1}, {:ok, w2}} ->
        Enum.each(w1 ++ w2, fn d ->
          Cure.Pipeline.Events.emit(
            :kernel,
            :final_core_violation,
            %{clause: d.clause, message: d.message},
            %{}
          )
        end)

        :ok

      {{:error, r1}, {:ok, _}} -> {:error, {:final_core_violation, r1}}
      {{:ok, _}, {:error, r2}} -> {:error, {:final_core_violation, r2}}
      {{:error, r1}, {:error, r2}} -> {:error, {:final_core_violation, r1 ++ r2}}
    end
  end
```

`Events.emit/4` is safe to call here: it dispatches through the supervised
`Cure.Pipeline.Events.Registry` (started by `Cure.Application`, which `mix test`
boots via `mod: {Cure.Application, []}`); dispatch on a registry with no
subscribers simply returns `:ok`. Warnings are also only emitted when a body
actually contains a legacy node, so clean defs never touch `emit`.

`Cure.Pipeline.Events`'s `@type stage()` is a closed union (`:lexer | :parser |
:type_checker | :codegen | :fsm_verifier | :sup_verifier | :app_verifier |
:registry | :synthesis | :doc_mermaid`) that the module's own moduledoc/comment
enumerates and keeps in sync with every new stage added over time; `emit/4`'s
runtime guard only checks `is_atom(stage)` so passing the new `:kernel` atom
works today, but leaving it out of that union is spec drift the next Dialyzer
run (or the next person reading that enumeration) would trip over. Add it in
the same small edit:

```elixir
# lib/cure/pipeline/events.ex — extend the stage union and its comment
  # ... `:doc_mermaid` the Mermaid diagram emitter for `cure doc` (v0.27.0);
  # `:kernel` covers the trusted Core kernel's Final-Core grammar-boundary
  # instrumentation (K11a). Every other stage maps to one of the compilation
  # pipeline phases.
  @type stage ::
          :lexer
          | :parser
          | :type_checker
          | :codegen
          | :fsm_verifier
          | :sup_verifier
          | :app_verifier
          | :registry
          | :synthesis
          | :doc_mermaid
          | :kernel
```

- [ ] **Step 4: Run the validator test, then the full core suite (serially)**

Run: `mix test test/cure/core/validator_test.exs`
Expected: PASS (19 tests total).

Then, to confirm the wiring is non-breaking, run the whole kernel suite ONCE (no other suite running concurrently):

Run: `mix test test/cure/core/`
Expected: PASS — no regressions from the added `check_def` validator call.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/validator.ex lib/cure/core/kernel.ex lib/cure/pipeline/events.ex test/cure/core/validator_test.exs
git commit -m "feat(core): run Final-Core validator in check_def (warn-only default) (K11a)"
```

---

### Task 6: Subject-reduction harness (#638)

**Files:**
- Create: `lib/cure/core/meta_check.ex`
- Test: `test/cure/core/subject_reduction_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Kernel.infer/2`, `Cure.Core.Kernel.normalize/2`, `Cure.Core.Conv.conv_values?/4`.
- Produces: `Cure.Core.MetaCheck.type_preserved?/2 :: (Context.t(), tuple()) -> boolean()` — true iff `term` infers a type, normalizes, and the normal form infers a definitionally-equal type. Returns false if `term` is ill-typed or normalization exhausts fuel.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/subject_reduction_test.exs
defmodule Cure.Core.SubjectReductionTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context}

  # Seed corpus of closed, well-typed, *inferable* terms, each exercising a
  # reduction (or already normal). Grows per wave. Every entry is closed and
  # global-free so it needs no def env. NB: bare `{:pair, …}` is check-only (the
  # kernel has no infer rule for it), so sigma terms are excluded until a later
  # wave adds an inferable eliminator corpus.
  @corpus [
    {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_type}},        # beta -> {:int_type}
    {:app, {:lam, {:int_type}, {:var, 0}}, {:int_lit, 7}},     # beta -> {:int_lit, 7}
    {:type, 0}                                                 # already normal
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    # applying a type to a type is ill-typed -> not type-preserved
    refute MetaCheck.type_preserved?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every corpus term preserves its type under normalization (#638)" do
    for term <- @corpus do
      assert MetaCheck.type_preserved?(Context.empty(), term), "not type-preserved: #{inspect(term)}"
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/subject_reduction_test.exs`
Expected: FAIL — `Cure.Core.MetaCheck` undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# lib/cure/core/meta_check.ex
defmodule Cure.Core.MetaCheck do
  @moduledoc """
  Metatheory regression harnesses for the trusted Core (K11a): subject reduction
  (#638) and progress (#639). These are property predicates driven over corpora
  by the harness test files; they are guardrails, not proofs, and each corpus
  grows as later waves land.
  """

  alias Cure.Core.{Kernel, Conv, Context}

  @doc """
  Subject reduction (#638): `term` infers a type, its normal form infers a type,
  and the two types are definitionally equal. False if ill-typed or fuel-exhausted.
  """
  @spec type_preserved?(Context.t(), tuple()) :: boolean()
  def type_preserved?(ctx, term) do
    with {:ok, ty1} <- Kernel.infer(ctx, term),
         nf when nf != :fuel_exhausted <- Kernel.normalize(ctx, term),
         {:ok, ty2} <- Kernel.infer(ctx, nf) do
      Conv.conv_values?(ty1, ty2, Context.length(ctx), Context.signature(ctx))
    else
      _ -> false
    end
  end
end
```

Use `Context.length(ctx)` and `Context.signature(ctx)` here, not hardcoded `0`/`nil`: the corpus today is closed terms under `Context.empty()` (depth 0, no certified globals) so the two are observationally identical right now, but the function's own type signature commits to an arbitrary `Context.t()`, and the moduledoc says the corpus "grows as later waves land" — a future non-empty context, or one with certified globals in its signature, would otherwise get silently wrong depth/δ-gating in the conversion check.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/subject_reduction_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/meta_check.ex test/cure/core/subject_reduction_test.exs
git commit -m "feat(core): subject-reduction harness MetaCheck.type_preserved? (#638)"
```

---

### Task 7: Progress harness (#639)

**Files:**
- Modify: `lib/cure/core/meta_check.ex`
- Test: `test/cure/core/progress_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Kernel.infer/2`, `Cure.Core.Kernel.normalize/2`.
- Produces: `Cure.Core.MetaCheck.progresses?/2 :: (Context.t(), tuple()) -> boolean()` — true iff a well-typed `term` normalizes (no fuel exhaustion) to a term whose head is a canonical/value former (not a stuck eliminator). False if ill-typed.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/progress_test.exs
defmodule Cure.Core.ProgressTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context}

  # Closed, well-typed, inferable terms; each normalizes to a canonical head.
  @corpus [
    {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_type}},    # -> {:int_type} (canonical)
    {:app, {:lam, {:int_type}, {:var, 0}}, {:int_lit, 7}}, # -> {:int_lit, 7}
    {:lam, {:type, 0}, {:var, 0}}                          # already canonical (lam head)
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    refute MetaCheck.progresses?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every closed well-typed corpus term reaches a canonical head (#639)" do
    for term <- @corpus do
      assert MetaCheck.progresses?(Context.empty(), term), "stuck / no progress: #{inspect(term)}"
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/progress_test.exs`
Expected: FAIL — `progresses?/2` undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# add to lib/cure/core/meta_check.ex

  @doc """
  Progress (#639): a closed well-typed `term` normalizes (no fuel exhaustion) to a
  term with a canonical/value head — never a stuck eliminator. False if ill-typed.
  """
  @spec progresses?(Context.t(), tuple()) :: boolean()
  def progresses?(ctx, term) do
    case Kernel.infer(ctx, term) do
      {:ok, _ty} ->
        case Kernel.normalize(ctx, term) do
          :fuel_exhausted -> false
          nf -> canonical_head?(nf)
        end

      _ ->
        false
    end
  end

  defp canonical_head?({:lam, _, _}), do: true
  defp canonical_head?({:lam, _, _, _}), do: true
  defp canonical_head?({:pair, _, _}), do: true
  defp canonical_head?({:ctor, _, _}), do: true
  defp canonical_head?({:type, _}), do: true
  defp canonical_head?({:pi, _, _}), do: true
  defp canonical_head?({:pi, _, _, _}), do: true
  defp canonical_head?({:sigma, _, _}), do: true
  defp canonical_head?({:sigma, _, _, _}), do: true
  defp canonical_head?({:data, _, _, _}), do: true
  defp canonical_head?({:int_type}), do: true
  defp canonical_head?({:int_lit, _}), do: true
  defp canonical_head?({:float_type}), do: true
  defp canonical_head?({:float_lit, _}), do: true
  defp canonical_head?(_), do: false
```

- [ ] **Step 4: Run the progress suite, then the whole core suite once (serially)**

Run: `mix test test/cure/core/progress_test.exs`
Expected: PASS (2 tests).

Then, the final serial gate for this plan:

Run: `mix test test/cure/core/`
Expected: PASS — validator, subject-reduction, and progress suites all green with no kernel regression.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/meta_check.ex test/cure/core/progress_test.exs
git commit -m "feat(core): progress harness MetaCheck.progresses? (#639)"
```

---

## Done criteria

- `Cure.Core.Validator` exists with the full 11-clause checklist, a Wave-0 config that is pure instrumentation (no `:reject`), a case-branch-safe node walker, active legacy-detecting predicates, and deferred predicates ready to flip.
- The validator runs inside `Kernel.check_def/2` against both the declared type and the body, warn-only by default (non-breaking), rejecting only under a `:reject` config override — the per-wave flip mechanism, proven by test.
- `Cure.Core.MetaCheck` provides `type_preserved?/2` (#638) and `progresses?/2` (#639), each with a working detection test and a passing seed corpus.
- `mix test test/cure/core/` passes in a single serial run.

## Out of scope (later waves — do NOT do here)

Adding grade fields to binders, deleting `{:eq}/{:refl}/{:rewrite}/{:prim}/{:absurd}`, qualified `Sym` ids, level-expressions, flipping any clause to `:reject` in the default config, and the K5 index-refinement typing rule. This plan builds only the scaffold and harnesses (K11a).
