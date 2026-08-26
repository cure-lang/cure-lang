# Antigen kernel-law assays — Implementation Plan (Run B)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use `- [ ]` checkboxes.

**Goal:** Add three relational kernel-law assays (de Bruijn shift/subst algebra, weakening, reduction order-independence) to Antigen, reusing the `:typed_term` challenge kind — pure-Antigen, kernel-API only, no TCB edits.

**Architecture:** One new assay module `Antigen.Assays.KernelLaw` dispatching on assay-id; three new `:typed_term` assay-ids wired into `default_gen` + the runner registry; a one-line guard widening so `Term.typed_term/1` accepts the new ids. The law logic is lifted verbatim from probes already empirically validated against the live kernel (0 failures over 500 real generated terms + hand terms, per the spec-review).

**Tech Stack:** Elixir; `Cure.Core.{Term, Context, Eval, Normalise, Kernel}`; `Antigen.{Challenge, Runner}`; `Antigen.Generators.{Term, SigMenu}`; `Antigen.Assays.Term`.

## Global Constraints

- Ghost-authored commits: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- `MIX_ENV=test mix test …`; macOS has no `timeout`; one build/test run at a time.
- **No `Cure.Core.*` (TCB) edits** — only read-only calls into its public API. No `StreamData` literal under `lib/antigen/generators/` or `assays/`.
- **The three new assay-ids all emit `:typed_term`**, so `default_gen` grows 11→14 branches, all new positions (12,13,14) join **Group T**. Run A's group guard MUST be updated in lockstep (`t: [4,5,6,9,10,11,12,13,14]`).
- Tests immutable once correct (change impl, not the test).

---

## Task 1: Widen `Term.typed_term/1` guard + registry rows (foundation)

**Files:** Modify `lib/antigen/generators/term.ex`, `lib/antigen/runner.ex`; Test `test/antigen/assays/kernel_law_test.exs` (new file, first tests).

**Interfaces:**
- Produces: `Term.typed_term(assay_id)` accepts any binary id (was: only `@assay_ids`); `Runner.assay_module_for("kernel/shift_subst" | "kernel/weakening" | "kernel/confluence")` → `Antigen.Assays.KernelLaw`.

- [ ] **Step 1: Write the failing test** — create `test/antigen/assays/kernel_law_test.exs`:

```elixir
defmodule Antigen.Assays.KernelLawTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Term, as: TermGen
  alias Antigen.Runner

  test "typed_term/1 accepts the new kernel-law assay-ids (guard widened)" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      # returns a Gen.t() (a tagged tuple), not raising FunctionClauseError
      assert is_tuple(TermGen.typed_term(id))
    end
  end

  test "runner registry routes the three kernel-law ids to KernelLaw" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      assert Runner.assay_module_for(id) == Antigen.Assays.KernelLaw
    end
  end
end
```

- [ ] **Step 2: Run — expect FAIL** (`MIX_ENV=test mix test test/antigen/assays/kernel_law_test.exs`) — both tests raise `FunctionClauseError`: the first because the widened-guard-less `typed_term/1` still rejects the new id; the second because `assay_module/1` has no catch-all clause (confirmed: every existing clause is a literal-string match with no fallback), so an unregistered id falls through and raises rather than returning `nil`.

- [ ] **Step 3: Implement** —
  (a) In `lib/antigen/generators/term.ex`, widen the guard on the public `typed_term/1` clause from `when assay_id in @assay_ids` to `when is_binary(assay_id)`. The body is unchanged (it only stores `assay_id` in the challenge's `assay:` field; it never branches on it). Leave `@assay_ids` and `Term.default_gen/0` untouched.
  (b) In `lib/antigen/runner.ex`, add three rows to the `assay_module/1` private registry (next to the existing `"term/…"` rows):

```elixir
  defp assay_module("kernel/shift_subst"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/weakening"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/confluence"), do: Antigen.Assays.KernelLaw
```

- [ ] **Step 4: Run — expect PASS** for both tests in this file. `Antigen.Assays.KernelLaw` doesn't exist yet, but neither test calls it — the registry test only compares the bare atom returned by `assay_module_for/1` (a private-registry delegate; no `Code.ensure_loaded`, no `apply`, no struct construction), so referencing an as-yet-undefined module name compiles and runs cleanly (confirmed empirically: a probe registry function returning an atom for an undefined module compiles, runs, and `Code.ensure_loaded?/1` correctly reports `false` for it). No hedge needed — this step is a hard PASS, not a "proceed to Task 2 if it errors" fallback.

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/term.ex lib/antigen/runner.ex test/antigen/assays/kernel_law_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): widen typed_term guard + register kernel-law assay-ids"
```

---

## Task 2: `Antigen.Assays.KernelLaw` — the three assays

**Files:** Create `lib/antigen/assays/kernel_law.ex`; extend `test/antigen/assays/kernel_law_test.exs`.

**Interfaces:**
- Produces: `KernelLaw.run(%Challenge{})` → `:ok | {:violation, detail}`, dispatching on `c.assay`. Consumes `Cure.Core.{Term,Context,Eval,Normalise,Kernel}`, `SigMenu.{env_of,rebuild_context}`, `Antigen.Assays.Term.assay_fuel/0`.

- [ ] **Step 1: Write the failing tests** — append to `test/antigen/assays/kernel_law_test.exs`:

```elixir
  alias Antigen.Assays.KernelLaw
  alias Antigen.Challenge

  defp ch(assay, term, ctx \\ []),
    do: Challenge.new(kind: :typed_term, assay: assay, label: :well_typed,
                      payload: %{sig: :v1, ctx: ctx, type: {:data, :Nat, [], []}, term: term})

  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  test "shift_subst: a well-formed term satisfies all four laws" do
    assert :ok = KernelLaw.run(ch("kernel/shift_subst", {:lam, {:data, :Nat, [], []}, {:ctor, :S, [{:var, 0}]}}))
  end

  test "shift_subst: the checker is not tautological (independently re-derive laws 2 and 3)" do
    # guard against the assay always returning :ok — recompute the two most
    # error-prone laws (composition and commutation) here and confirm both
    # sides genuinely agree for this term AND that the computation is
    # non-trivial (if the assay ignored its input it would still pass, so we
    # also check that shifting/substituting actually changed something).
    t = {:ctor, :S, [{:var, 0}]}

    # law 2 (shift composition): shift(shift(t,a,c),b,c) == shift(t,a+b,c)
    law2_lhs = Cure.Core.Term.shift(Cure.Core.Term.shift(t, 1, 0), 1, 0)
    law2_rhs = Cure.Core.Term.shift(t, 2, 0)
    assert law2_lhs == law2_rhs
    assert law2_lhs != t   # shift actually changed something

    # law 3 (shift/subst commutation): shift(subst(t,j,r),a,c) == subst(shift(t,a,c),j+a,shift(r,a,c))
    law3_lhs = Cure.Core.Term.shift(Cure.Core.Term.subst(t, 0, @sz), 1, 0)
    law3_rhs = Cure.Core.Term.subst(Cure.Core.Term.shift(t, 1, 0), 1, Cure.Core.Term.shift(@sz, 1, 0))
    assert law3_lhs == law3_rhs
    assert law3_lhs != Cure.Core.Term.shift(t, 1, 0)   # subst actually changed something

    assert :ok = KernelLaw.run(ch("kernel/shift_subst", t))
  end

  test "weakening: closed well-typed term preserves typing + type-agreement" do
    assert :ok = KernelLaw.run(ch("kernel/weakening", @sz))
  end

  test "weakening: an ill-typed term is vacuously :ok (not a false violation)" do
    # `Z` applied as a function is ill-typed; infer fails ⇒ vacuous
    assert :ok = KernelLaw.run(ch("kernel/weakening", {:app, @z, @z}))
  end

  test "confluence: a redex normalizes identically via nf and whnf→nf" do
    assert :ok = KernelLaw.run(ch("kernel/confluence", {:app, {:lam, {:data, :Nat, [], []}, {:var, 0}}, @sz}))
  end

  # spec §4 item 3 calls for both a positive AND a vacuous (fuel-exhausted)
  # confluence fixture — the assay fuel is fixed (`Assays.Term.assay_fuel/0`,
  # 500), not caller-supplied, so the only way to exercise the vacuous branch
  # through the public `KernelLaw.run/1` API is a term that genuinely needs
  # >500 reduction steps. `plus` (sig :v1) is structurally recursive on its
  # first argument (spec §2's wiring reuses the same v1 env as the other
  # assays), so `plus(deep_s(700), Z)` unfolds 700 times — confirmed
  # empirically: depth 500 is already enough to exhaust `nf`'s fuel=500
  # budget (depth 400 is not), so depth 700 gives comfortable headroom.
  defp deep_s(0), do: @z
  defp deep_s(n), do: {:ctor, :S, [deep_s(n - 1)]}

  test "confluence: a genuinely fuel-exhausting term is vacuously :ok" do
    t = {:app, {:app, {:global, :plus}, deep_s(700)}, @z}
    assert :ok = KernelLaw.run(ch("kernel/confluence", t))
  end
```

- [ ] **Step 2: Run — expect FAIL** — `Antigen.Assays.KernelLaw` undefined.

- [ ] **Step 3: Implement** — `lib/antigen/assays/kernel_law.ex` (logic lifted verbatim from the review's validated probes):

```elixir
defmodule Antigen.Assays.KernelLaw do
  @moduledoc """
  Relational kernel-law assays (spec §3), all via the public `Cure.Core.*` API
  (no TCB edits): de Bruijn σ-algebra (`kernel/shift_subst`), weakening under an
  unused binder (`kernel/weakening`), and reduction order-independence
  (`kernel/confluence`). Each is a `:typed_term` challenge dispatched by assay-id.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Antigen.Assays.Term, as: TermAssay
  alias Cure.Core.{Term, Context, Eval, Normalise, Kernel}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{assay: "kernel/shift_subst", payload: p}), do: shift_subst(p.term)
  def run(%Challenge{assay: "kernel/weakening", payload: p}), do: weakening(p)
  def run(%Challenge{assay: "kernel/confluence", payload: p}), do: confluence(p)

  defp ctx_of(p), do: SigMenu.rebuild_context(SigMenu.env_of(p.sig), p.ctx)

  # ── 3a. de Bruijn σ-algebra (pure; no ctx needed) ──────────────────────────
  defp shift_subst(t) do
    with :ok <- law1(t), :ok <- law2(t), :ok <- law3(t), :ok <- law4(t), do: :ok
  end

  defp law1(t) do
    lhs = Term.shift(t, 0, 0)
    if lhs == t, do: :ok, else: {:violation, {:shift_subst_law, 1, lhs, t}}
  end

  defp law2(t) do
    case Enum.find_value([{1, 1, 0}, {2, 1, 0}, {1, 2, 1}, {2, 2, 1}], fn {a, b, c} ->
           lhs = Term.shift(Term.shift(t, a, c), b, c)
           rhs = Term.shift(t, a + b, c)
           if lhs != rhs, do: {a, b, c, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 2, f}}
    end
  end

  # commutation, for c ≤ j: shift(subst(t,j,r),a,c) == subst(shift(t,a,c), j+a, shift(r,a,c))
  defp law3(t) do
    combos = for j <- [0, 1], c <- [0, 1], a <- [1, 2], r <- [@z, @sz], c <= j, do: {j, c, a, r}
    case Enum.find_value(combos, fn {j, c, a, r} ->
           lhs = Term.shift(Term.subst(t, j, r), a, c)
           rhs = Term.subst(Term.shift(t, a, c), j + a, Term.shift(r, a, c))
           if lhs != rhs, do: {j, c, a, r, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 3, f}}
    end
  end

  # subst-of-fresh-index no-op: subst(shift(t,1,c),c,r) == shift(t,1,c)
  defp law4(t) do
    case Enum.find_value(for(c <- [0, 1], r <- [@z, @sz], do: {c, r}), fn {c, r} ->
           shifted = Term.shift(t, 1, c)
           lhs = Term.subst(shifted, c, r)
           if lhs != shifted, do: {c, r, lhs, shifted}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 4, f}}
    end
  end

  # ── 3b. weakening under an unused binder ───────────────────────────────────
  defp weakening(p) do
    ctx = ctx_of(p)
    t = p.term

    case Kernel.infer(ctx, t) do
      {:error, _} ->
        :ok

      {:ok, v} ->
        a_value = Eval.eval(@nat, Context.env(ctx))
        ctx2 = Context.extend(ctx, a_value)
        t2 = Term.shift(t, 1, 0)

        case Kernel.infer(ctx2, t2) do
          {:error, err} ->
            {:violation, {:weakening_broke_typing, err}}

          {:ok, v2} ->
            q = Normalise.quote(v, Context.length(ctx))
            q2 = Normalise.quote(v2, Context.length(ctx2))
            if q2 == Term.shift(q, 1, 0), do: :ok, else: {:violation, {:weakening_type_mismatch, q, q2}}
        end
    end
  end

  # ── 3c. reduction order-independence ───────────────────────────────────────
  defp confluence(p) do
    ctx = ctx_of(p)
    t = p.term
    fuel = TermAssay.assay_fuel()
    full = Normalise.nf(ctx, t, fuel: fuel)

    staged =
      case Normalise.whnf(ctx, t, fuel: fuel) do
        :fuel_exhausted -> :skip
        w -> Normalise.nf(ctx, w, fuel: fuel)
      end

    cond do
      full == :fuel_exhausted -> :ok
      staged in [:skip, :fuel_exhausted] -> :ok
      full == staged -> :ok
      true -> {:violation, {:confluence_mismatch, full, staged}}
    end
  end
end
```

- [ ] **Step 4: Run — expect PASS** (`MIX_ENV=test mix test test/antigen/assays/kernel_law_test.exs`).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/assays/kernel_law.ex test/antigen/assays/kernel_law_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): KernelLaw assays — shift/subst, weakening, confluence"
```

---

## Task 3: Wire into `default_gen` + update group guard (14 branches)

**Files:** Modify `lib/mix/tasks/antigen.ex`, `lib/antigen/runner.ex`; Test `test/antigen/runner_test.exs`.

**Interfaces:**
- Produces: `Mix.Tasks.Antigen.default_gen/0` → 14-branch `{:frequency, ws}`; `Runner.gen_group_table/0` → `%{f: [1,2,3], t: [4,5,6,9,10,11,12,13,14], m: [7,8]}`.

- [ ] **Step 1: Update the group-guard test (RED)** — in `test/antigen/runner_test.exs`, change the existing guard test's expectations from 11 to 14 and the Group-T list:

```elixir
  test "default_gen has exactly 14 branches in the documented group order (guard)" do
    {:frequency, ws} = Mix.Tasks.Antigen.default_gen()
    assert length(ws) == 14
    assert Antigen.Runner.gen_group_table() ==
             %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11, 12, 13, 14], m: [7, 8]}
  end
```

Also add an integration test proving the three verticals run clean on the sound kernel:

```elixir
  test "kernel-law verticals run to completion with 0 infections on the sound kernel" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      opts = [gen: Antigen.Generators.Term.typed_term(id), count: 40,
              corpus_path: tmp("kl_c_#{String.replace(id, "/", "_")}.sexp"),
              seeds_path: tmp("kl_s_#{String.replace(id, "/", "_")}.sexp"),
              report_dir: tmp("kl_r_#{String.replace(id, "/", "_")}")]
      r = Antigen.Runner.explore(opts)
      assert r.infections == 0, "#{id} false-positived on the sound kernel"
    end
  end
```

- [ ] **Step 2: Run — expect the guard test RED, the integration test already GREEN** (`MIX_ENV=test mix test test/antigen/runner_test.exs`). The guard test fails (`length(ws) == 14` against the still-11-branch `default_gen`/old `@group_table` — this is the red test Step 3 makes green). The integration test is **not** red at this checkpoint and that is expected, not a gap: it drives `Antigen.Generators.Term.typed_term(id)` directly rather than through `default_gen`, so it depends only on Task 1 (guard widening) + Task 2 (`KernelLaw`), both already done — it exercises Runner.explore end-to-end as an integration/regression check on that wiring, not as a red test for Task 3's own change (default_gen/group-table wiring). Confirmed empirically: with only this step's test edits applied and Task 3's Step 3 changes withheld, the suite reports exactly 1 failure (the guard test) and the integration test passes.

- [ ] **Step 3: Implement** —
  (a) In `lib/mix/tasks/antigen.ex`, append three branches to `default_gen/0`'s `Antigen.Gen.frequency([...])` list (after the existing 11, positions 12–14):

```elixir
      {1, Antigen.Generators.Term.typed_term("kernel/shift_subst")},
      {1, Antigen.Generators.Term.typed_term("kernel/weakening")},
      {1, Antigen.Generators.Term.typed_term("kernel/confluence")}
```

  (b) In `lib/antigen/runner.ex`, update `@group_table`:

```elixir
  @group_table %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11, 12, 13, 14], m: [7, 8]}
```

- [ ] **Step 4: Run — expect PASS** (`MIX_ENV=test mix test test/antigen/runner_test.exs`).

- [ ] **Step 5: Commit**
```bash
git add lib/mix/tasks/antigen.ex lib/antigen/runner.ex test/antigen/runner_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): wire kernel-law verticals into default_gen (11→14 branches)"
```

---

## Self-Review

**Spec coverage:** §2 guard-widening + registry → Task 1; §3a/b/c assays → Task 2 (all four laws, weakening floor+agreement+vacuous, confluence+vacuous); §2 default_gen +3 / group-table 14 → Task 3; §4 tests → Tasks 1–3 (item 4 guard-widening red is Task 1; item 5 integration is Task 3); §5 files match; §6 ladder is documentation (no code). §7 non-goals respected (no TCB, no new kind, no Idris/Cure proof).

**Placeholder scan:** none — every step has concrete code, lifted from the review-validated probes.

**Type consistency:** `KernelLaw.run/1` takes `%Challenge{}`, defined Task 2, referenced by the registry rows (Task 1) as a bare module atom (no call). `gen_group_table/0`/`@group_table` (Run A) updated Task 3, asserted by the guard test. `Term.typed_term/1` guard widened Task 1, consumed by Task 3's default_gen branches + the integration test.

**Ordering:** Task 1 (guard+registry) before Task 2 (assay module the registry names) before Task 3 (default_gen wiring + guard bump). Stage 5: full suite once + `mix antigen --count 800` confirming the three verticals participate with 0 infections and unaffected health lines.
