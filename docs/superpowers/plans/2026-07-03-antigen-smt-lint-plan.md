# Antigen V6 — SMT Lint Soundness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Property-test the untrusted SMT lint `Cure.SMT.Solver` for *lint soundness* (never over-claim) via three assays over a bounded brute-force oracle, wired as a fixed catalog.

**Architecture:** New `Antigen.Assays.SmtLint` (a `run/1`→`run/2` op-map seam, mirroring V1/V2/V4/V5) checks `prove_implication`/`check_sat`/`prove_with_counterexample` against an Antigen-owned bounded integer evaluator `eval_pred/2` over the MetaAST predicate format. A fixed `Antigen.Generators.SmtQuery` catalog + `Runner.assay_module/1` dispatch + a `:smt_query` `Challenge` kind complete the wiring. No `Cure.*` edits.

**Tech Stack:** Elixir/ExUnit, real Z3 subprocess via `Cure.SMT.Process` (confirmed installed: `/opt/homebrew/bin/z3`).

## Global Constraints

- **All mix invocations use `MIX_ENV=test`**, run from the worktree root `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`. **One build/test run at a time** (concurrent runs caused a kernel panic).
- **No edits to `Cure.SMT.*` / `Cure.Core.*` / `Cure.Elab.*`** — reached read-only through the op-map. No `:meck`, no new dependency.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NEVER a `Co-Authored-By` trailer.
- **StreamData quarantine:** `Antigen.Assays.SmtLint` must contain no literal `StreamData` token (comments/moduledoc included) — `architecture_test.exs` greps for it.
- **Assay `run/1,2` returns only `:ok | {:violation, term()}`** — `:unknown`/timeout/incompleteness fold into `:ok`, never a third outcome.
- **`@domain = -32..32`** committed constant; **no `:hot`/`:cold` PGO hints** (use plain `check_sat/2` and default `prove_implication/4`).
- **Unconditional:** never gate on `Solver.available?/0`; no `@tag :skip`.
- **New generator atoms** added to `Challenge.@known_atoms`.
- Stay on branch `autopilot/antigen-tier-b` — no new worktree.
- **Tests are immutable once written (strict TDD):** each task's Step 1 tests are
  written first and pass only by editing implementation code (Step 3) — never by
  weakening, deleting, or rewriting a test to match whatever the code currently does.
  The ONE pre-authorized exception is Task 3's known-finding test (Step 4 note): if the
  real Z3/Parser no longer reproduce the negative-witness bug, the test's premise is
  empirically wrong, and the plan explicitly says to flip the assertion to `:ok` and
  report non-reproduction — that is not "editing a test for convenience," it's the
  skill's standard "prove the test itself is wrong first" exception, spelled out in
  advance because the reproduction depends on live Z3 behavior outside the plan's
  control. No other test in this plan may be weakened under any circumstance.
- **A real infection is a finding, not a bug in the plan (spec §7):** if any CLEAN
  baseline test (i.e. every test in Tasks 1–4 except the Task 3 known-finding fixture)
  unexpectedly fails against the REAL Solver at a GREEN step — meaning the real Z3 lint
  itself produced a false discharge / false unsat / bogus counterexample / false
  proven for one of the catalog's deliberately simple, decidable predicates — that is
  itself a genuine soundness finding. STOP, do not alter the predicate or weaken the
  assertion to make it pass, and report it with the same weight as the `parse_model`
  finding. This is the same "prove the test is wrong first" discipline as above, applied
  to the solver instead of the parser: a surprising failure here means the SOLVER's
  behavior is suspect, not the test.

## File structure

- Create `lib/antigen/assays/smt_lint.ex` — the three-family assay + private `eval_pred/2`.
- Create `lib/antigen/generators/smt_query.ex` — fixed catalogs + shared MetaAST predicate builders.
- Create `test/antigen/assays/smt_lint_test.exs` — per-task tests + the parse_model known-finding fixture.
- Modify `lib/antigen/runner.ex` — three `assay_module/1` clauses.
- Modify `lib/antigen/challenge.ex` — `:smt_query` kind in the `@type kind ::` union + `@known_atoms` additions.

## Reconciliations (read before Task 1)

1. **The `parse_model` negative-value bug (spec §9-item-2) is handled the V4 way.** The
   real `Cure.SMT.Parser.parse_model/1` truncates a negative Z3 witness `(- N)` to the
   malformed string `"(- N"` (not an integer). So:
   - The **clean catalog** V6c baseline uses only implications whose counterexample
     space is **strictly non-negative** (so Z3 returns a clean integer witness →
     genuinely `:ok`).
   - A **dedicated known-finding test** (kept OUT of the generator catalog, exactly
     like V4's `:MkP`/`:g` fixtures) uses an implication whose counterexample space is
     **strictly negative** (`x > -100 ⇒ x >= 0` → counterexample space `x ∈ {-99..-1}`,
     all negative), forcing the parser bug, and asserts the assay surfaces
     `{:violation, {:unusable_model, _}}`. This documents the bug as a true-positive.
   - The V6c assay therefore distinguishes THREE model outcomes: a refuting integer
     witness → `:ok`; a non-refuting **integer** witness → `{:bogus_counterexample, m}`
     (the negative-control case); a **non-integer** (malformed) value → `{:unusable_model, m}`
     (the parser-bug finding). `is_integer/1` is the discriminator — no defensive
     re-parse of `Cure.SMT.*` output (that would MASK the bug; V6 *finds*, never fixes/hides).
2. **`eval_pred/2` mirrors `Translator.translate_op/1` EXACTLY** (verified translator.ex:225-238):
   `:==` is equality (`==`), `:!=` is disequality (`!=`/`not ==`), `:>`/`:<`/`:>=`/`:<=`
   comparisons, `:+`/`:-`/`:*` integer arithmetic, `:and`/`:or`/`:not` boolean, unary
   `:-` negation. `:/`(div)/`:%`(mod) are in the translator's set but OUT of the
   catalog's scope (§8 non-goals) — `eval_pred/2` does not implement them (an
   unhandled operator raises, which is correct: a catalog entry using one is a plan bug).
3. **Predicate builders live in the generator** (`Antigen.Generators.SmtQuery`), but
   Tasks 1–3 write assay tests BEFORE Task 4 creates that module. So Tasks 1–3 define
   their own tiny inline builders in the test file (`lit/1`, `xvar/0`, `bop/3`); Task 4's
   generator re-defines the same builders module-privately. This duplication is
   intentional and small (three one-liners) — do NOT try to share them across the
   test/lib boundary mid-plan. The catalog's non-goals (§8) exclude unary operators
   (`:not`/unary `:-`), so no `uop/2` builder is needed anywhere in this plan — don't
   add one; an unused `defp` triggers a compiler warning for no benefit.
4. **V6c also directly checks `{:proven, nil}` soundness** (tightens spec §4's V6c
   text). The spec states "`{:proven, nil}` is checked by V6a's discharge property" —
   but `prove_implication` (V6a) and `prove_with_counterexample` (V6c) are genuinely
   different code paths: `prove_implication` translates via `generate_subtype_query`
   under `QF_UFLIA` (translator.ex:81-100); `prove_with_counterexample` builds its own
   hand-rolled `QF_LIA` query string directly in `solver.ex:115-120`. A bug unique to
   the latter's query-building or result path (e.g. a false `{:proven, nil}` on an
   invalid implication) would NOT be caught by V6a's stubbed-`prove_implication`
   control, which never touches `prove_with_counterexample` at all. Since "never
   claim a stronger answer than the truth" is the vertical's entire premise (§1) and
   `prove_with_counterexample` is an explicit Target (§2), leaving its own proven-claim
   unchecked is a real coverage gap, not a deliberate non-goal. Task 3 therefore adds
   a bounded-domain check to the `{:proven, nil}` branch (mirroring V6a exactly) and a
   `{:false_proven, ...}` negative control — this is what makes the plan's original
   test-count arithmetic (13 after Task 3, 15 after Task 4) actually add up.

---

### Task 1: `eval_pred/2` + `smt/implication` assay (V6a)

**Files:**
- Create: `lib/antigen/assays/smt_lint.ex`
- Test: `test/antigen/assays/smt_lint_test.exs`

**Interfaces:**
- Produces: `Antigen.Assays.SmtLint.run/1 :: :ok | {:violation, term()}`; `run/2` (challenge, op-map); `__real__/0 :: map()`; `@domain` range. Private `eval_pred/2 :: integer() | boolean()`.
- Consumes: `Antigen.Challenge`, `Cure.SMT.Solver.prove_implication/4`.

- [ ] **Step 1: Write the failing tests**

```elixir
defmodule Antigen.Assays.SmtLintTest do
  use ExUnit.Case, async: false
  # async: false — these clauses spawn a Z3 subprocess (Cure.SMT.Process); serialize
  # to avoid subprocess contention with the parallel suite (spec §6, open item #3).

  alias Antigen.Assays.SmtLint
  alias Antigen.Challenge

  # --- inline MetaAST builders (Task 4's generator re-defines these) ---
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp xvar, do: {:variable, [], "x"}
  defp bop(op, a, b), do: {:binary_op, [operator: op], [a, b]}
  # x > n
  defp gt(n), do: bop(:>, xvar(), lit(n))

  defp impl_ch(p1, p2) do
    Challenge.new(kind: :smt_query, assay: "smt/implication", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: 1)
  end

  describe "eval_pred/2 (via public run behavior is enough, but sanity-check the oracle)" do
    # eval_pred is private; exercise it indirectly through a negative control whose
    # correctness depends on eval_pred computing the right truth values (Step-3 impl).
    test "oracle drives the false_discharge control (finds a witness in x>0 ∧ not x>5)" do
      # Enum.find walks @domain -32..32 ascending, so the witness it reports is
      # whichever is smallest in {1..5} (x=1) — assert the property, not a specific x.
      k = %{SmtLint.__real__() | prove_implication: fn _p1, _p2, _v, _b -> true end}
      assert {:violation, {:false_discharge, %{x: x}}} =
               SmtLint.run(impl_ch(gt(0), gt(5)), k)
      assert x > 0 and not (x > 5)
    end
  end

  describe "smt/implication (V6a)" do
    test "valid implication baseline: x > 5 ⇒ x > 0, real lint proves it, no bounded counterexample" do
      assert SmtLint.run(impl_ch(gt(5), gt(0))) == :ok
    end

    test "invalid implication baseline: x > 0 ⇒ x > 5, real lint returns false (or unknown) → no false discharge" do
      assert SmtLint.run(impl_ch(gt(0), gt(5))) == :ok
    end

    test "negative control: a prove_implication stub returning true on the invalid implication" do
      k = %{SmtLint.__real__() | prove_implication: fn _p1, _p2, _v, _b -> true end}
      assert {:violation, {:false_discharge, _}} = SmtLint.run(impl_ch(gt(0), gt(5)), k)
    end
  end
end
```

- [ ] **Step 2: Run to verify RED**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: FAIL — `Antigen.Assays.SmtLint` undefined.

- [ ] **Step 3: Write minimal implementation**

Create `lib/antigen/assays/smt_lint.ex`:

```elixir
defmodule Antigen.Assays.SmtLint do
  @moduledoc """
  Property tests for the untrusted SMT lint `Cure.SMT.Solver` (spec: antigen-smt-lint).

  Framed by the locked decision that Z3 is OUT of the dependent-kernel TCB — the SMT
  layer is an untrusted lint, never a proof. The property is LINT SOUNDNESS, not
  completeness: the lint may give up (`:unknown`), but must never over-claim.

    * smt/implication — `prove_implication == true` ⟹ no bounded counterexample (V6a).
    * smt/unsat       — `check_sat == :unsat` ⟹ no bounded satisfying witness (V6b).
    * smt/witness     — `prove_with_counterexample`'s `{:failed, model}` genuinely
      refutes, and a `{:proven, nil}` claim has no bounded counterexample (V6c).

  The oracle is an Antigen-owned bounded evaluator `eval_pred/2` over the MetaAST
  predicate format, decided over a fixed integer domain (`@domain`). This is a
  sound-in-one-direction differential: a bounded counterexample proves the lint
  over-claimed; the converse never fires (completeness is out of scope). `:unknown`
  is always a legal, non-infecting answer.

  Ops go through an injectable @real map (run/2); negative controls weaken the
  code-under-test without touching `Cure.SMT.*` or `:meck`.
  """
  alias Antigen.Challenge
  alias Cure.SMT.Solver

  @domain -32..32

  @real %{
    prove_implication: &Solver.prove_implication/4,
    check_sat: &Solver.check_sat/2,
    prove_with_counterexample: &Solver.prove_with_counterexample/4
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :smt_query} = c), do: run(c, @real)

  def run(%Challenge{kind: :smt_query, assay: "smt/implication", payload: %{p1: p1, p2: p2, var: var}}, k) do
    case k.prove_implication.(p1, p2, var, :int) do
      true ->
        case Enum.find(@domain, fn x -> eval_pred(p1, x) and not eval_pred(p2, x) end) do
          nil -> :ok
          x -> {:violation, {:false_discharge, %{x: x, p1: p1, p2: p2}}}
        end

      _ ->
        # false / :unknown — the lint did not over-claim (completeness is out of scope)
        :ok
    end
  end

  # --- bounded oracle: independent evaluator over the MetaAST predicate format ---
  # Mirrors Translator.translate_op/1 semantics exactly (single free variable = x).
  defp eval_pred({:literal, _meta, n}, _x), do: n
  defp eval_pred({:variable, _meta, _name}, x), do: x

  defp eval_pred({:binary_op, meta, [l, r]}, x) do
    a = eval_pred(l, x)
    b = eval_pred(r, x)

    case Keyword.get(meta, :operator) do
      :+ -> a + b
      :- -> a - b
      :* -> a * b
      :> -> a > b
      :< -> a < b
      :>= -> a >= b
      :<= -> a <= b
      :== -> a == b
      :!= -> a != b
      :and -> a and b
      :or -> a or b
    end
  end

  defp eval_pred({:unary_op, meta, [o]}, x) do
    v = eval_pred(o, x)

    case Keyword.get(meta, :operator) do
      :not -> not v
      :- -> -v
    end
  end
end
```

- [ ] **Step 4: Run to verify GREEN**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: PASS (4). The valid-implication baseline confirms the real Z3 lint proves
`x > 5 ⇒ x > 0`; if it instead returns `:unknown`, the test still passes (`:ok`) — but
note in the run output whether Z3 proved it (expected) or gave up.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/smt_lint.ex test/antigen/assays/smt_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): smt/implication assay — prove_implication never falsely discharges (bounded oracle)"
```

---

### Task 2: `smt/unsat` assay (V6b)

**Files:** Modify `lib/antigen/assays/smt_lint.ex`; append tests.

**Interfaces:**
- Consumes: `Cure.SMT.Solver.check_sat/2`.

- [ ] **Step 1: Write the failing tests** (append to `smt_lint_test.exs`)

```elixir
  describe "smt/unsat (V6b)" do
    # x > 0 ∧ x < 0  — unsatisfiable
    defp conj(a, b), do: bop(:and, a, b)
    defp lt(n), do: bop(:<, xvar(), lit(n))

    defp sat_ch(constraint) do
      Challenge.new(kind: :smt_query, assay: "smt/unsat", label: :positive,
        payload: %{constraint: constraint, var: "x"}, seed: 1)
    end

    test "unsat baseline: x > 0 ∧ x < 0 is unsat, no bounded witness → :ok" do
      assert SmtLint.run(sat_ch(conj(gt(0), lt(0)))) == :ok
    end

    test "sat baseline: x > 0 is sat (lint returns :sat not :unsat) → :ok" do
      assert SmtLint.run(sat_ch(gt(0))) == :ok
    end

    test "negative control: a check_sat stub returning :unsat on the satisfiable x > 0" do
      k = %{SmtLint.__real__() | check_sat: fn _ast, _vt -> :unsat end}
      assert {:violation, {:false_unsat, %{x: x}}} = SmtLint.run(sat_ch(gt(0)), k)
      assert x > 0
    end
  end
```

- [ ] **Step 2: Run to verify RED**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: FAIL — no `run/2` clause for `"smt/unsat"` (FunctionClauseError on the three new tests).

- [ ] **Step 3: Write minimal implementation** (add clause to `smt_lint.ex`, after the `smt/implication` clause)

```elixir
  def run(%Challenge{kind: :smt_query, assay: "smt/unsat", payload: %{constraint: constraint, var: var}}, k) do
    case k.check_sat.(constraint, %{var => :int}) do
      :unsat ->
        case Enum.find(@domain, fn x -> eval_pred(constraint, x) end) do
          nil -> :ok
          x -> {:violation, {:false_unsat, %{x: x, constraint: constraint}}}
        end

      _ ->
        # :sat / :unknown — the lint did not claim unsat
        :ok
    end
  end
```

- [ ] **Step 4: Run to verify GREEN**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: PASS (7).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/smt_lint.ex test/antigen/assays/smt_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): smt/unsat assay — check_sat never falsely reports :unsat"
```

---

### Task 3: `smt/witness` assay (V6c) + parse_model known-finding

**Files:** Modify `lib/antigen/assays/smt_lint.ex`; append tests.

**Interfaces:**
- Consumes: `Cure.SMT.Solver.prove_with_counterexample/4`.

- [ ] **Step 1: Write the failing tests** (append to `smt_lint_test.exs`)

```elixir
  describe "smt/witness (V6c)" do
    defp witness_ch(p1, p2) do
      Challenge.new(kind: :smt_query, assay: "smt/witness", label: :positive,
        payload: %{p1: p1, p2: p2, var: "x"}, seed: 1)
    end

    test "witness baseline: invalid x > 0 ⇒ x > 5 yields a genuine (non-negative) counterexample → :ok" do
      # counterexample space x ∈ {1..5} — strictly non-negative, so the real
      # Parser returns a clean integer (dodges the negative-value parser bug).
      assert SmtLint.run(witness_ch(gt(0), gt(5))) == :ok
    end

    test "negative control: a prove_with_counterexample stub returning a non-refuting integer model" do
      # x=99 satisfies BOTH x>0 and x>5, so it is NOT a counterexample to x>0 ⇒ x>5.
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:failed, %{"x" => 99}} end}
      assert {:violation, {:bogus_counterexample, _}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
    end

    test "unusable-model control: a stub returning a non-integer (malformed) model value" do
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:failed, %{"x" => "(- 7"}} end}
      assert {:violation, {:unusable_model, _}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
    end

    test "proven/unknown are legal: a stub returning {:proven, nil} or {:unknown, nil} → :ok" do
      k1 = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:proven, nil} end}
      k2 = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:unknown, nil} end}
      assert SmtLint.run(witness_ch(gt(5), gt(0)), k1) == :ok
      assert SmtLint.run(witness_ch(gt(0), gt(5)), k2) == :ok
    end

    test "negative control: a prove_with_counterexample stub returning {:proven, nil} on the invalid implication" do
      # x > 0 ⇒ x > 5 is invalid (x=1 refutes it). A stub falsely claiming :proven is a
      # false-proven soundness violation — symmetric to V6a's false_discharge, but this
      # exercises prove_with_counterexample's OWN proven-claim path (a different code
      # path/query from prove_implication; reconciliation #4 explains why V6a's control
      # does not already cover this).
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:proven, nil} end}
      assert {:violation, {:false_proven, %{x: x}}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
      assert x > 0 and not (x > 5)
    end
  end

  describe "parse_model negative-witness finding (real Solver + real Parser)" do
    # x > -100 ⇒ x >= 0 : counterexample space x ∈ {-99..-1} — STRICTLY negative.
    # Z3 must return a negative witness, which Cure.SMT.Parser.parse_model/1
    # truncates to a malformed string "(- N" (confirmed bug, spec §9-item-2).
    # The assay surfaces this as {:unusable_model, _} — a TRUE POSITIVE, documented,
    # kept OUT of the clean generator catalog.
    defp ge(n), do: bop(:>=, xvar(), lit(n))

    test "real prove_with_counterexample on a negative-witness implication yields an unusable model (TRUE POSITIVE)" do
      ch = Challenge.new(kind: :smt_query, assay: "smt/witness", label: :negative,
        payload: %{p1: gt(-100), p2: ge(0), var: "x"}, seed: 99)
      # If Z3/Parser ever start returning a clean negative integer, this flips to :ok
      # and the finding is fixed — treat that as a signal, not a test failure to force.
      assert {:violation, {:unusable_model, _}} = SmtLint.run(ch)
    end
  end
```

- [ ] **Step 2: Run to verify RED**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: FAIL — no `run/2` clause for `"smt/witness"`.

- [ ] **Step 3: Write minimal implementation** (add clause + helper to `smt_lint.ex`, after the `smt/unsat` clause)

```elixir
  def run(%Challenge{kind: :smt_query, assay: "smt/witness", payload: %{p1: p1, p2: p2, var: var}}, k) do
    case k.prove_with_counterexample.(p1, p2, var, :int) do
      {:failed, model} ->
        case model_value(model, var) do
          {:ok, xv} ->
            if eval_pred(p1, xv) and not eval_pred(p2, xv),
              do: :ok,
              else: {:violation, {:bogus_counterexample, model}}

          :error ->
            # non-integer / malformed witness — the lint promised a counterexample but
            # delivered an unusable value (e.g. Parser.parse_model negative-value bug)
            {:violation, {:unusable_model, model}}
        end

      {:proven, nil} ->
        # A claimed proof must itself be sound: no bounded x may witness p1 ∧ ¬p2
        # (mirrors V6a's discharge check exactly). NOT redundant with V6a: that assay
        # stubs/exercises prove_implication, a separate query/code path from
        # prove_with_counterexample (reconciliation #4) — this is the only place that
        # checks THIS function's own proven-claim.
        case Enum.find(@domain, fn x -> eval_pred(p1, x) and not eval_pred(p2, x) end) do
          nil -> :ok
          x -> {:violation, {:false_proven, %{x: x, p1: p1, p2: p2}}}
        end

      {:unknown, nil} ->
        :ok
    end
  end

  defp model_value(model, var) when is_map(model) do
    case Map.get(model, var) do
      v when is_integer(v) -> {:ok, v}
      _ -> :error
    end
  end

  defp model_value(_model, _var), do: :error
```

- [ ] **Step 4: Run to verify GREEN**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: PASS (13) — 7 carried over from Tasks 1–2, plus 6 new in this task (witness
baseline, bogus-counterexample control, unusable-model control, proven/unknown-legal,
false-proven control, parse_model known-finding). **The parse_model known-finding test
passing confirms the real
`Cure.SMT.Parser.parse_model/1` negative-value truncation empirically** (via the real
Z3 subprocess). If that ONE test instead comes back `:ok`, it means Z3-in-this-env
returned the negative witness in a form the parser handled — record that in the report
(the finding did not reproduce here) and change the assertion to `== :ok`; do NOT
force a red. If the witness baseline (non-negative) fails with `{:unusable_model, _}`,
Z3 returned a NEGATIVE witness for `x>0 ⇒ x>5` (should be impossible — space is
{1..5}); re-examine the predicate.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/smt_lint.ex test/antigen/assays/smt_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): smt/witness assay — counterexample consistency (finds parse_model negative-value bug)"
```

---

### Task 4: `SmtQuery` catalogs + runner wiring + kind + atoms

**Files:**
- Create: `lib/antigen/generators/smt_query.ex`
- Modify: `lib/antigen/runner.ex`, `lib/antigen/challenge.ex`
- Test: append to `smt_lint_test.exs`.

**Interfaces:**
- Produces: `Antigen.Generators.SmtQuery.implication_challenges/0`, `unsat_challenges/0`, `witness_challenges/0` :: `[Challenge.t()]`.
- Consumes: `Antigen.Runner.replay_one/1`.

- [ ] **Step 1: Write the failing tests** (append to `smt_lint_test.exs`)

```elixir
  describe "generator + runner wiring" do
    alias Antigen.Generators.SmtQuery
    alias Antigen.Runner

    test "each catalog is non-empty and correctly tagged" do
      assert SmtQuery.implication_challenges() != []
      assert SmtQuery.unsat_challenges() != []
      assert SmtQuery.witness_challenges() != []
      assert Enum.all?(SmtQuery.implication_challenges(), & &1.assay == "smt/implication")
      assert Enum.all?(SmtQuery.unsat_challenges(), & &1.assay == "smt/unsat")
      assert Enum.all?(SmtQuery.witness_challenges(), & &1.assay == "smt/witness")
    end

    test "runner dispatches all three ids and the whole clean catalog is :ok" do
      all =
        SmtQuery.implication_challenges() ++
          SmtQuery.unsat_challenges() ++ SmtQuery.witness_challenges()

      assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
    end
  end
```

- [ ] **Step 2: Run to verify RED**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: FAIL — `Antigen.Generators.SmtQuery` undefined.

- [ ] **Step 3: Create the generator**

Create `lib/antigen/generators/smt_query.ex`:

```elixir
defmodule Antigen.Generators.SmtQuery do
  @moduledoc """
  Fixed catalogs of MetaAST predicate queries for the `Antigen.Assays.SmtLint`
  families (spec: antigen-smt-lint). Deterministic, no corpus banking.

  All entries are inside decidable one-variable linear integer arithmetic and are
  chosen so the real Z3 lint answers soundly (clean catalog re-checks `:ok`). The
  negative-witness implication that surfaces the `Cure.SMT.Parser` negative-value
  bug is intentionally NOT here — it is a known-finding fixture in `smt_lint_test.exs`
  (mirrors V4's erased-first ctor/def fixtures).
  """
  alias Antigen.Challenge

  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp xvar, do: {:variable, [], "x"}
  defp bop(op, a, b), do: {:binary_op, [operator: op], [a, b]}
  defp gt(n), do: bop(:>, xvar(), lit(n))
  defp lt(n), do: bop(:<, xvar(), lit(n))

  @doc "V6a — implication soundness catalog."
  @spec implication_challenges() :: [Challenge.t()]
  def implication_challenges do
    [
      impl(gt(5), gt(0), 0),   # valid: x>5 ⇒ x>0
      impl(gt(0), gt(5), 1)    # invalid: real lint returns false → no false discharge
    ]
  end

  @doc "V6b — unsat soundness catalog."
  @spec unsat_challenges() :: [Challenge.t()]
  def unsat_challenges do
    [
      unsat(bop(:and, gt(0), lt(0)), 2),  # unsat: x>0 ∧ x<0
      unsat(gt(0), 3)                     # sat: real lint returns :sat → :ok
    ]
  end

  @doc "V6c — witness consistency catalog (non-negative counterexamples only)."
  @spec witness_challenges() :: [Challenge.t()]
  def witness_challenges do
    [
      witness(gt(0), gt(5), 4)  # counterexample space {1..5}, all non-negative
    ]
  end

  defp impl(p1, p2, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/implication", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: seed)
  end

  defp unsat(constraint, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/unsat", label: :positive,
      payload: %{constraint: constraint, var: "x"}, seed: seed)
  end

  defp witness(p1, p2, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/witness", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: seed)
  end
end
```

- [ ] **Step 4: Wire the runner** — add to `lib/antigen/runner.ex`, next to the other `assay_module/1` clauses (after the `erasure/*` clauses):

```elixir
  defp assay_module("smt/implication"), do: Antigen.Assays.SmtLint
  defp assay_module("smt/unsat"), do: Antigen.Assays.SmtLint
  defp assay_module("smt/witness"), do: Antigen.Assays.SmtLint
```

- [ ] **Step 5: Wire the Challenge kind + atoms** — in `lib/antigen/challenge.ex`:

Add `:smt_query` to the `@type kind ::` union (after `:erasure_term`):

```elixir
          | :erasure_term
          | :smt_query
```

Add to `@known_atoms` (after the V4 erasure block):

```elixir
    # SMT-lint vertical (V6): kind (MetaAST predicate payloads use string keys/var
    # names, not atoms, so no extra generator atoms beyond the kind itself)
    :smt_query
```

- [ ] **Step 6: Run to verify GREEN**

Run: `MIX_ENV=test mix test test/antigen/assays/smt_lint_test.exs`
Expected: PASS (15). The wiring test proves `Runner.replay_one/1` dispatches all three
ids and the whole clean catalog re-checks `:ok` under the real Z3 lint.

- [ ] **Step 7: Commit**

```bash
git add lib/antigen/generators/smt_query.ex lib/antigen/runner.ex lib/antigen/challenge.ex test/antigen/assays/smt_lint_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): SmtQuery catalogs + smt/* runner dispatch + :smt_query kind"
```

---

### Task 5: Full-suite verification (Stage 5 gate)

**Files:** none (verification only).

- [ ] **Step 1: Quarantine check**

Run: `MIX_ENV=test mix test test/antigen/architecture_test.exs`
Expected: PASS (1) — `SmtLint` has no literal `StreamData` token.

- [ ] **Step 2: Full suite (single authorized run)**

Run: `MIX_ENV=test mix test`
Expected: PASS, 0 failures — prior 2713 + 15 new = ~2728 (exact count may differ by
doctest bookkeeping; the invariant is **0 failures**). If any pre-existing test now
fails, STOP — the `:smt_query` kind or `@known_atoms` edit regressed something.

- [ ] **Step 3: Restore any test-run side effects**

Run: `git checkout -- test/antigen/seeds.sexp 2>/dev/null; git status --short`
Expected: clean working tree (the SMT tests do not bank, so this should be a no-op;
confirm nothing unexpected is dirty).

- [ ] **Step 4: (Report is Stage 5 of autopilot — written separately.)** The completion
  report must **headline the `parse_model` negative-value finding** (the second real
  bug the initiative surfaced) alongside the three clean assays, mirroring V4's report
  structure.

---

## Self-review (against spec)

- **Spec §4 three families** → Tasks 1 (V6a), 2 (V6b), 3 (V6c). ✓
- **Spec §5 op-map seam + three ids + `@domain -32..32`** → Task 1 Step 3 (`@real`, `run/1`→`run/2`), all clauses use `@domain`. ✓
- **Spec §5 three negative controls** → Task 1 (false_discharge), Task 2 (false_unsat), Task 3 (bogus_counterexample). Plus the extra `unusable_model`, `false_proven` (reconciliation #4 — tightens spec §4's V6c text), and proven/unknown-legal controls. ✓
- **Spec §6 unconditional / `:unknown` legal / no PGO hints / async:false** → `run/2` folds `false`/`:unknown`/`:sat` to `:ok`; `check_sat/2` + default `prove_implication/4` used (no hint arg); test module `async: false`. ✓
- **Spec §7 invariants** → no `Cure.*` edits (op-map only); no `StreamData` (Task 5 Step 1); `:ok | {:violation,_}` only; clean catalog `:ok` (Task 4 Step 6); atoms added (Task 4 Step 5). ✓
- **Spec §9-item-1 operator coverage** → `eval_pred/2` covers `:+,:-,:*,:>,:<,:>=,:<=,:==,:!=,:and,:or,:not` (unary `:-`,`:not`), matching `translate_op/1`. ✓
- **Spec §9-item-2 parse_model bug** → Reconciliation #1: clean catalog non-negative, known-finding fixture asserts `{:unusable_model,_}`, `is_integer` discriminator, no `Cure.SMT.*` re-parse. ✓
- **Spec §9-item-4 kind + atoms + 3 assay_module clauses (no catch-all)** → Task 4 Steps 4–5. ✓
- **Spec §10 catalog items 1–9** → items 1–2 (Task 1 baselines), 3 (Task 1 control), 4–5 (Task 2 baselines), 6 (Task 2 control), 7 (Task 3 baseline), 8 (Task 3 control), 8b — `false_proven` control, beyond the literal §10 list per reconciliation #4 (Task 3 control), 9 (Task 4 wiring). ✓
- **Type consistency:** `run/1,2`, `__real__/0`, `@domain`, `eval_pred/2`, `model_value/2` names consistent across tasks; generator fns `implication_challenges/0`/`unsat_challenges/0`/`witness_challenges/0` match Task 4 tests. ✓
- **No placeholders:** every code step shows full code. ✓
