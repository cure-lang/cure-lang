# Sound first-order index unification for dependent `case` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the one-directional `branch_index_subst/4` zip in the kernel's dependent-`case` checker with a sound bidirectional first-order unifier over the scrutinee-vs-constructor index vectors — closing the Antigen 4.3 incompleteness (a dropped ground result index) and, with the same unifier, discharging provably-unreachable branches.

**Architecture:** One new private kernel function `unify_indices/4` returning `{:solved, subst} | :trivial | :impossible`, feeding the EXISTING `specialize_branch_context`/`specialize_branch_value`/`replace_branch_vars` application layer unchanged. `check_case_branches` gains one `:impossible` arm. No new modules; no change to the `rewrite`/transport layer, coverage, or exhaustiveness. Spec: `docs/superpowers/specs/kernel/2026-07-01-case-index-unification-design.md`.

**Tech Stack:** Elixir, ExUnit, the existing `Cure.Core.*` kernel.

## Global Constraints

- One `mix test` / `mix compile` process at any moment — NEVER concurrent (a past concurrent full-suite run caused a kernel panic). Serialize every build/test invocation.
- Ghost-written commits — NO `Co-Authored-By` / co-author trailers.
- Tests are immutable once green: make a failing test pass by changing `lib/cure/core/kernel.ex`, never by weakening/skipping/deleting a test. The sole exception is a test proven to encode outdated/wrong behavior, justified in the commit message before editing (this plan invokes that exception exactly once, for the 4.3 Antigen assertion — see Task 1).
- Compile with OTP 26–28 (already the environment).
- Soundness boundary (spec §5): `subst` entries are only definitional consequences of the match; `:impossible` fires ONLY on a definite rigid constructor/data head clash; uncertainty is NEVER `:impossible`; occurs-check on every bind; a same-key merge conflict is `:impossible`, never a silent overwrite.

## Reference facts (verified against the worktree — rely on these; do not re-derive)

**Current `check_case_branches` (`lib/cure/core/kernel.ex`), the `true ->` arm:**
```elixir
true ->
  %{args: tele, result_indices: result_indices} = ctor
  {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele)
  subst = branch_index_subst(ctx, result_indices, scrut_indices, arity)
  ctx_branch = specialize_branch_context(ctx_branch, subst)
  s_values = Enum.map(result_indices, &Eval.eval(&1, Enum.reverse(arg_vals)))
  ctor_value = {:vctor, cname, arg_vals}
  expected =
    motive_value
    |> apply_motive(s_values ++ [ctor_value])
    |> specialize_branch_value(ctx_branch, subst)
  case check(ctx_branch, body, expected) do
    :ok -> {:cont, :ok}
    {:error, _} -> {:halt, {:error, :branch_type}}
  end
```
The family-scoping guard (`{:foreign_ctor, _}`) and arity guard run BEFORE this arm (unchanged).

**Current `branch_index_subst/4` (to be replaced):**
```elixir
defp branch_index_subst(ctx, result_indices, scrut_indices, arity) do
  depth = Context.length(ctx)
  result_indices
  |> Enum.zip(scrut_indices)
  |> Enum.reduce(%{}, fn
    {{:var, i}, scrut_value}, acc ->
      replacement = scrut_value |> Quote.reify(depth) |> Term.shift(arity, 0)
      Map.put(acc, i, replacement)
    {_other, _scrut_value}, acc -> acc
  end)
end
```

**Helpers/APIs (exact):**
- `Context.length(ctx)` → outer depth (before telescope extension). `Context.signature(ctx)` → the `Env`.
- `extend_with_telescope(ctx, tele)` → `{ctx_branch, arg_vals}`; ctor args occupy `ctx_branch` indices `0..arity-1` (most-recently-bound = lowest).
- `Quote.reify(value, depth)` → term; `{:vdata, name, vs}` reifies to `{:data, name, reified_vs, []}` (FLATTENED spine, `indices: []` always — `quote.ex:45`); `{:vctor, name, vs}` → `{:ctor, name, reified_vs}`; a neutral var `{:vneutral, {:nvar, lvl}}` reifies to a `{:var, k}` with `k = depth-1-lvl ≥ 0`.
- `Term.shift(term, amount, cutoff \\ 0)` → shifts free `{:var, k}` with `k >= cutoff` by `amount` (respects binder depth for `:pi/:lam/:sigma`, `quote`/`term.ex:88-116`).
- `Eval.eval/2`, `apply_motive/2`, `specialize_branch_context/2`, `specialize_branch_value/3`, `replace_branch_vars/2` — unchanged; `subst` is `%{de_bruijn_index => term}` in `ctx_branch`'s numbering.

**De Bruijn contract (spec §4.4 — one coherent index space, `ctx_branch`):**
- `result_indices` (the `r` side) are terms over the ctor telescope ONLY → all their vars are `< arity`, already `ctx_branch`-relative, no shift.
- `scrut_indices` (the `s` side) are values in the OUTER context → reify at `Context.length(ctx)` then `Term.shift(arity, 0)` to lift into `ctx_branch` → all their vars are `≥ arity`.
- The two var ranges are therefore DISJOINT, which fixes the solve direction unambiguously (no runtime ambiguity).

**Antigen 4.3 probe** (`lib/antigen/generators/indexed.ex`, `test/antigen/assays/indexed_test.exs`): `Generators.Indexed.refinement(:well_typed)` currently replays `{:violation, {:wrongly_rejected, {:refine, :branch_type}}}`; after the fix it replays `:ok`. `refinement(:ill_typed)` (wrong-body probe) must STILL replay `:ok` (rejected). The seed bank is `test/antigen/indexed_seed_test.exs` (`@seed_candidates`), which currently EXCLUDES `refinement(:well_typed)`.

---

### Task 1: `unify_indices/4` — bidirectional positive refinement (closes 4.3)

**Files:**
- Modify: `lib/cure/core/kernel.ex` (replace `branch_index_subst/4`; edit the `true ->` arm)
- Modify: `test/antigen/assays/indexed_test.exs` (flip the 4.3 assertion)
- Modify: `test/antigen/indexed_seed_test.exs` (seed `refinement(:well_typed)`)
- Test: `test/cure/core/case_soundness_index_test.exs` (NEW file, sibling of the existing `case_soundness_test.exs`; Tests 1, 2, 4, 5b, 7)

**Interfaces:**
- Produces: `unify_indices(ctx, result_indices, scrut_indices, arity) :: {:solved, map()} | :trivial | :impossible`. In THIS task `:impossible` is *never returned* (clash/conflict → conservative `:undecided` internally → no binding); the value is introduced in Task 2. `check_case_branches` consumes `{:solved, s}`/`:trivial` only.

- [ ] **Step 1: Flip the 4.3 Antigen assertion.** In `test/antigen/assays/indexed_test.exs`, replace the body of the test `"4.3 refinement-complete well-typed case — records kernel's verdict"`:

```elixir
  test "4.3 refinement-complete well-typed case is now accepted (completeness fix)" do
    # Pre-fix this replayed {:wrongly_rejected, {:refine, :branch_type}} (the
    # documented incompleteness). unify_indices now solves n := Causal from the
    # wrap ctor's ground result index and refines h : Ix n to Ix Causal.
    assert :ok == A.run(G.refinement(:well_typed))
  end
```

- [ ] **Step 2: Run it, verify RED** (against the unmodified kernel)

Run: `mix test test/antigen/assays/indexed_test.exs -v`
Expected: FAIL — the flipped test returns `{:violation, {:wrongly_rejected, {:refine, :branch_type}}}`.

- [ ] **Step 3: Write the kernel characterization + red tests** in a NEW file `test/cure/core/case_soundness_index_test.exs` (sibling of `case_soundness_test.exs`; keeps the 4.1 file focused). Tests 1, 2, 4, 5b, 7:

```elixir
defmodule Cure.Core.CaseSoundnessIndexTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @dec {:data, :Dec, [], []}

  # Dec with two nullary ctors; Ix(n:Dec) with wrap:(p:Dec)->Ix(Causal).
  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
    |> Inductive.declare(Inductive.family(:Ix, [], [{:n, @dec}], 0),
         [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])])
  end

  # de Bruijn (innermost = 0): in def_type Π(n).Π(h:Ix n).Π(ix:Ix n). Ix n,
  # n is var0 under its own binder, var1 under h, var2 under ix.
  @ix0 {:data, :Ix, [], [{:var, 0}]}
  @ix1 {:data, :Ix, [], [{:var, 1}]}
  @ix2 {:data, :Ix, [], [{:var, 2}]}

  # Test 1 — Positive refinement (4.3 core): reusing h : Ix n as Ix Causal.
  test "Test 1: an outer hypothesis h : Ix n is reusable as Ix Causal in the wrap branch" do
    def_type = {:pi, @dec, {:pi, @ix0, {:pi, @ix1, @ix2}}}
    motive = {:lam, @dec, {:lam, @ix0, @ix1}}
    # wrap branch adds one binder (p), so h (was var1 before the case) is var2 inside.
    body = {:lam, @dec, {:lam, @ix0, {:lam, @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 2 — Refinement soundness (§5.1): the machinery does not fabricate a false
  # equation. SAME shape and SAME def_type/body as Test 1 (reusing outer hypothesis
  # `h : Ix n` in the wrap branch), but the motive now hard-demands the WRONG ground
  # index: `Ix Dcoupled` instead of `Ix Causal`. wrap's own result index is always
  # Causal, so a sound unifier can only ever derive `n := Causal` (the TRUE,
  # entailed fact) — never `n := Dcoupled`. `h`, refined to `Ix Causal`, then does
  # NOT match the required `Ix Dcoupled` (both rigid ground terms of the SAME
  # family Ix, per design §8 item 2), so the case must still be rejected. This is
  # the direction Test 1 does not cover: Test 1 shows a previously-rejected good
  # program now accepts; this shows the same machinery does not go on to fabricate
  # an equation the match never actually established.
  test "Test 2: a body relying on an unentailed index equation is still rejected" do
    def_type = {:pi, @dec, {:pi, @ix0, {:pi, @ix1, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}}
    motive = {:lam, @dec, {:lam, @ix0, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}
    body = {:lam, @dec, {:lam, @ix0, {:lam, @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, _} = Kernel.check_def(env, :probe)
  end

  # Test 4 — Occurs-check (§5.3), regression half. Given the proven disjoint-range
  # invariant (§4.4: r-side vars always < arity, s-side vars always >= arity after
  # reify+shift), a real cyclic pair cannot arise from any legitimate case branch —
  # so no adversarial construction exists to positively exercise occurs_index?/2
  # returning true on real input while keeping this test green pre-fix (any
  # fixture that meaningfully drives the new var-var solving path is, by
  # construction, a NEW-capability case like Test 1/2, not a same-behavior
  # regression). This test instead documents the honest, weaker claim: a
  # legitimate bare-ctor-arg-var match (the one case today's kernel already
  # handles) keeps checking unchanged under the new unifier — i.e. the occurs-check
  # machinery, even though present on every bind, adds no false rejections on
  # ordinary structural-recursion input. It does NOT prove the guard would
  # actually catch a genuine cycle (no such input is constructible here); that
  # guarantee rests on the disjoint-range proof in §4.4, not on this test.
  test "Test 4: structural-recursion refinement of a nested-index family still checks" do
    # Pair(a:Dec, b:Dec) family Two(Pair) with mk:(x:Dec)->Two(P x x)... kept simple:
    # Two(i:Dec) with pack:(y:Dec)->Two(y); match Two(m) with variable m → bind m := y.
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Two, [], [{:i, @dec}], 0),
           [Inductive.ctor(:pack, [{:y, @dec}], [{:var, 0}])])
    two0 = {:data, :Two, [], [{:var, 0}]}
    def_type = {:pi, @dec, {:pi, two0, @dec}}          # Π(m:Dec). Π(t:Two m). Dec
    motive = {:lam, @dec, {:lam, two0, @dec}}          # λm'.λt'. Dec
    body = {:lam, @dec, {:lam, two0, {:case, {:var, 0}, motive, [{:pack, 1, {:var, 0}}]}}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 5b — Undecidable half (§5.4, monotonic degradation): a pairing the
  # unifier cannot classify as either a solvable variable or a rigid clash must
  # stay :undecided (never :impossible) and the branch must NOT be discharged.
  # A "good body, assert :ok" framing CANNOT prove this: a wrongly-discharged
  # branch and a correctly-checked-and-accepted branch are both observably :ok,
  # so no such test can distinguish them. Instead: a fresh family `Stray(n:Dec)`
  # whose only constructor's result index is one opaque global (`h`); the
  # scrutinee's own index is a DIFFERENT opaque global (`g`). Neither side is a
  # de Bruijn variable (so unify_one's var-solving clauses never fire) and
  # neither is `rigid_index?/1` (a bare `{:global, _}` is not in that predicate's
  # clauses), so the pair is genuinely :undecided in BOTH Task 1 and Task 2 —
  # it can never become :impossible. The branch is given a deliberately
  # ill-typed body (`{:type, 0}`); a kernel that wrongly discharged this branch,
  # or wrongly fabricated a binding from it, would return :ok. The correct,
  # conservative kernel does not discharge it, checks the body against the
  # constant motive's `Dec` requirement, and rejects it.
  test "Test 5b: an undecidable index does not skip the body check" do
    env =
      base_env()
      |> Inductive.declare(Inductive.family(:Stray, [], [{:n, @dec}], 0),
           [Inductive.ctor(:mkStray, [{:p, @dec}], [{:global, :h}])])
      |> Env.add_def(:g, @dec, {:ctor, :Causal, []})
    stray_g = {:data, :Stray, [], [{:global, :g}]}
    motive = {:lam, @dec, {:lam, {:data, :Stray, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, stray_g, @dec}                    # Π(s: Stray(global g)). Dec
    body = {:lam, stray_g, {:case, {:var, 0}, motive, [{:mkStray, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert {:error, :branch_type} = Kernel.check_def(env, :probe)
  end

  # Test 7 — Regression: the legit Box/Dec matches (mirrors case_typing_test) still
  # check; here we just re-assert a ground-indexed match refines the ctor arg.
  test "Test 7: ground-indexed Box match still refines the ctor argument (no regression)" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0),
           [Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])])
    box_causal = {:data, :Box, [], [{:ctor, :Causal, []}]}
    motive = {:lam, @dec, {:lam, {:data, :Box, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, box_causal, @dec}                 # Π(b:Box Causal). Dec
    body = {:lam, box_causal, {:case, {:var, 0}, motive, [{:mk, 1, {:var, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end
end
```

- [ ] **Step 4: Run the kernel tests, characterize** (against the unmodified kernel)

Run: `mix test test/cure/core/case_soundness_index_test.exs -v`
Expected: **Test 1 FAILS** (`check_def` returns `{:error, :branch_type}` — the dropped `n := Causal`). **Tests 2, 4, 5b, 7 PASS** — but "PASS" means each test's OWN assertion already holds today, not that every test accepts a program: 2 asserts `{:error, _}` (the under-refining kernel can only drop equations, so it already can't wrongly accept a body that needs a false `n := Dcoupled`); 4 and 7 assert `:ok` (legitimate bare-ctor-arg-var matches already check); 5b asserts `{:error, :branch_type}` (an already-undecidable index pairing already falls through to a normal, rejecting body check — not because anything is refined, but because nothing is wrongly discharged or wrongly bound either). If any of 2/4/5b/7 is unexpectedly RED, STOP and investigate — it means the pre-fix kernel is already less sound/complete than assumed (a finding, not something to silence). If a construction is malformed (a `check_def` crash rather than `{:error, _}`), fix the FIXTURE (de Bruijn indexing) until it characterizes cleanly — these four are the net, not the target.

> Note for Step 4: verify each fixture's de Bruijn indices by running; the `@ix0/@ix1/@ix2` depths and the `{:var, k}` body references are the fiddly part. Tests 2/4/5b/7 must be genuinely green pre-fix; Test 1 genuinely red. Do not proceed until this split is confirmed.

- [ ] **Step 5: Replace `branch_index_subst/4` with `unify_indices/4`** in `lib/cure/core/kernel.ex`. Delete `branch_index_subst/4` and add:

```elixir
  # Bidirectional first-order unification of a constructor's result-index vector
  # (`result_indices`, terms over the ctor telescope — vars < arity) against the
  # scrutinee's index vector (`scrut_indices`, outer-context values) in ctx_branch's
  # de Bruijn space (spec §4.3/§4.4). Verdict: {:solved, subst} | :trivial | :impossible.
  # In this task :impossible is not yet produced (clash/conflict → :undecided);
  # Task 2 adds it.
  defp unify_indices(ctx, result_indices, scrut_indices, arity) do
    outer_depth = Context.length(ctx)

    result_indices
    |> Enum.zip(scrut_indices)
    |> Enum.map(fn {r, s_val} ->
      {r, s_val |> Quote.reify(outer_depth) |> Term.shift(arity, 0)}
    end)
    |> reduce_index_pairs(%{}, arity)
  end

  defp reduce_index_pairs([], subst, _arity),
    do: (if map_size(subst) == 0, do: :trivial, else: {:solved, subst})

  defp reduce_index_pairs([{r, s} | rest], subst, arity) do
    case unify_one(r, s, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> reduce_index_pairs(rest, subst2, arity)
      :undecided -> reduce_index_pairs(rest, subst, arity)
    end
  end

  # r-side vars are always < arity (ctor telescope); s-side vars always >= arity
  # (outer). Disjoint ranges ⇒ the solve direction is unambiguous.
  # A bare ctor-telescope var on the r-side ALWAYS binds the ctor var to `s`
  # (whether s is a term or a var). Cure declares indexed types with NO params
  # (family(name, [], index_tele, level), declarations.ex:405), so a uniform
  # "parameter-like" index shows up here as a bare-var-vs-var pair; binding the
  # ctor's fresh var to the scrutinee is the harmless no-op that keeps the shared
  # parameter identical everywhere. (An earlier draft had a var-vs-var "tie-break"
  # binding the OUTER var instead — that corrupted uniform parameters and broke
  # Std.Vector.append; removed. See spec §4.3.)
  defp unify_one({:var, i}, s, arity, subst) when i < arity,
    do: bind_index(i, s, subst)                         # ctor arg := scrutinee term (Box case / prior behavior)

  defp unify_one(r, {:var, j}, arity, subst) when j >= arity,
    do: bind_index(j, r, subst)                         # outer index var := ctor result index (4.3)

  defp unify_one({:ctor, c, as}, {:ctor, c, bs}, arity, subst) when length(as) == length(bs),
    do: unify_spine(as, bs, arity, subst)

  # :data heads: compare the FLATTENED spine (params ++ indices); Quote.reify always
  # emits an empty `indices` list, so never split ps-vs-is (spec §4.3).
  defp unify_one({:data, n, ps, is}, {:data, n, ps2, is2}, arity, subst)
       when length(ps) + length(is) == length(ps2) + length(is2),
       do: unify_spine(ps ++ is, ps2 ++ is2, arity, subst)

  defp unify_one(r, s, _arity, subst) when r == s, do: {:ok, subst}   # syntactically equal → consistent

  defp unify_one(r, s, _arity, _subst) do
    # Definite rigid head clash ⇒ impossible; anything else ⇒ conservative undecided.
    # (Task 1 downgrades clash to :undecided — see reduce_index_pairs guard note.)
    if rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s),
      do: :undecided,                                   # TASK 1: no :impossible yet
      else: :undecided
  end

  defp unify_spine([], [], _arity, subst), do: {:ok, subst}
  defp unify_spine([a | as], [b | bs], arity, subst) do
    case unify_one(a, b, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> unify_spine(as, bs, arity, subst2)
      :undecided -> unify_spine(as, bs, arity, subst)
    end
  end
  defp unify_spine(_, _, _arity, subst), do: {:ok, subst}

  # Add {key => term} after an occurs-check; on a same-key clash keep conservative.
  defp bind_index(key, term, subst) do
    cond do
      occurs_index?(key, term) -> :undecided            # cyclic ⇒ degrade (spec §5.3)
      Map.has_key?(subst, key) ->
        old = Map.get(subst, key)
        cond do
          old == term -> {:ok, subst}                   # consistent
          rigid_index?(old) and rigid_index?(term) and head_key(old) != head_key(term) ->
            :undecided                                  # TASK 1: no :impossible yet (Task 2 flips)
          true -> :undecided
        end
      true -> {:ok, Map.put(subst, key, term)}
    end
  end

  defp rigid_index?({:ctor, _, _}), do: true
  defp rigid_index?({:data, _, _, _}), do: true
  defp rigid_index?({:type, _}), do: true
  defp rigid_index?({:pi, _, _}), do: true
  defp rigid_index?({:sigma, _, _}), do: true
  defp rigid_index?({:int_type}), do: true
  defp rigid_index?({:bool_type}), do: true
  defp rigid_index?({:float_type}), do: true
  defp rigid_index?({:int_lit, _}), do: true
  defp rigid_index?({:bool_lit, _}), do: true
  defp rigid_index?({:float_lit, _}), do: true
  defp rigid_index?(_), do: false

  defp head_key({:ctor, n, _}), do: {:ctor, n}
  defp head_key({:data, n, _, _}), do: {:data, n}
  defp head_key(t) when is_tuple(t), do: elem(t, 0)
  defp head_key(other), do: other

  # Conservative occurs-check: does {:var, key} appear anywhere in term? Ignores
  # binder-depth shifts (over-approximates ⇒ at worst a spurious :undecided, never
  # an unsound bind). Given disjoint ranges it effectively never fires on real input.
  defp occurs_index?(key, {:var, k}), do: k == key
  defp occurs_index?(key, t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&occurs_index?(key, &1))
  defp occurs_index?(key, l) when is_list(l), do: Enum.any?(l, &occurs_index?(key, &1))
  defp occurs_index?(_key, _), do: false
```

- [ ] **Step 6: Update the `check_case_branches` `true ->` arm** to consume the verdict. Replace the `subst = branch_index_subst(...)` line and keep the rest:

```elixir
            true ->
              %{args: tele, result_indices: result_indices} = ctor
              {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele)

              subst =
                case unify_indices(ctx, result_indices, scrut_indices, arity) do
                  {:solved, s} -> s
                  :trivial -> %{}
                  # :impossible is unreachable in Task 1; Task 2 adds a real arm here.
                  :impossible -> %{}
                end

              ctx_branch = specialize_branch_context(ctx_branch, subst)
              s_values = Enum.map(result_indices, &Eval.eval(&1, Enum.reverse(arg_vals)))
              ctor_value = {:vctor, cname, arg_vals}

              expected =
                motive_value
                |> apply_motive(s_values ++ [ctor_value])
                |> specialize_branch_value(ctx_branch, subst)

              case check(ctx_branch, body, expected) do
                :ok -> {:cont, :ok}
                {:error, _} -> {:halt, {:error, :branch_type}}
              end
```

- [ ] **Step 7: Run the kernel + Antigen tests, verify GREEN**

Run: `mix test test/cure/core/case_soundness_index_test.exs test/antigen/assays/indexed_test.exs -v`
Expected: ALL PASS — Test 1 now green (the `n := Causal` refinement applies), the flipped 4.3 assertion green, Tests 2/4/5b/7 still green.

- [ ] **Step 8: Seed the now-passing 4.3 challenge.** In `test/antigen/indexed_seed_test.exs`, add `Indexed.refinement(:well_typed)` to the `@seed_candidates` list (it now replays `:ok`, so the `run(c) == :ok` filter will bank it). Replace the comment above `@seed_candidates` (currently: `# Known-good-behavior seeds: every OTHER indexed/case challenge the kernel` / `# currently handles correctly. refinement(:well_typed) is intentionally absent` / `# — it exposes a documented incompleteness (wrongly rejected), so it does not` / `# replay :ok and must not be banked as a "known-good" seed.`) with:
```elixir
  # Known-good-behavior seeds: every indexed/case challenge the kernel handles
  # correctly. `refinement(:well_typed)` is now included — the 4.3 incompleteness
  # (a dropped ground result index) is closed by unify_indices/4, so it replays
  # :ok and is a legitimate known-good seed.
```

- [ ] **Step 9: Run the seeding test alone** (writes seeds), then confirm git shows only `seeds.sexp` grew:

Run: `mix test test/antigen/indexed_seed_test.exs -v` → PASS.
Run: `git -C <worktree> status --short test/antigen/seeds.sexp` → shows it modified.

- [ ] **Step 10: Full suite once**

Run: `mix test`
Expected: green. The 4.1 antibody, all indexed-case obligations, and `case_typing_test.exs` still pass.

- [ ] **Step 11: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/case_soundness_index_test.exs \
        test/antigen/assays/indexed_test.exs test/antigen/indexed_seed_test.exs test/antigen/seeds.sexp
git commit -m "feat(kernel): bidirectional first-order index unification for case (closes 4.3)

Replace the one-directional branch_index_subst zip with unify_indices/4, which
solves an index equation from EITHER side (ctor-telescope arg or outer scrutinee
index var), closing the documented 4.3 incompleteness. Flips the 4.3 Antigen
assertion (outdated: it encoded the now-closed incompleteness) to assert :ok and
seeds the challenge. Impossible-branch discharge follows in the next commit."
```

---

### Task 2: Impossible-branch discharge + merge-conflict detection

**Files:**
- Modify: `lib/cure/core/kernel.ex` (activate `:impossible`; add the `:impossible` arm)
- Test: `test/cure/core/case_soundness_index_test.exs` (add Tests 3, 5a, 6)

**Interfaces:**
- `unify_indices/4` now genuinely returns `:impossible` on (a) a definite rigid head clash between two index terms, or (b) a same-key merge conflict. `check_case_branches` discharges an `:impossible` branch WITHOUT checking its body.

- [ ] **Step 1: Write Tests 3, 5a, 6** appended to `test/cure/core/case_soundness_index_test.exs`:

```elixir
  # Test 3 — Impossible-branch discharge: scrutinee Ix Dcoupled, wrap builds
  # Ix Causal ⇒ the wrap branch is unreachable; its (deliberately ill-typed) body
  # is NOT checked. Companion: a REACHABLE Ix Causal scrutinee with the same body
  # is still rejected (discharge is not a blanket bypass).
  test "Test 3: an impossible wrap branch is discharged without checking its body" do
    ix_dcoupled = {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}
    motive = {:lam, @dec, {:lam, @ix0, @dec}}                 # λn'.λix'. Dec
    def_type = {:pi, ix_dcoupled, @dec}                        # Π(s:Ix Dcoupled). Dec
    # body is {:type,0} where Dec is expected — only accepted because the branch is dead.
    body = {:lam, ix_dcoupled, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  test "Test 3 companion: the SAME ill-typed body in a REACHABLE branch is rejected" do
    ix_causal = {:data, :Ix, [], [{:ctor, :Causal, []}]}
    motive = {:lam, @dec, {:lam, @ix0, @dec}}
    def_type = {:pi, ix_causal, @dec}                          # Π(s:Ix Causal). Dec — wrap IS reachable
    body = {:lam, ix_causal, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, :branch_type} = Kernel.check_def(env, :probe)
  end

  # Test 5a — Clash half (§5.2 "only" direction), DIRECT positional clash: a
  # definite rigid head clash between a ground ctor-result-index term and a
  # ground scrutinee index discharges the branch, WITHOUT going through
  # bind_index's same-key merge path (that path is Test 6, a DIFFERENT code
  # route: unify_one's own catch-all fires here, not a same-key conflict).
  # Foo(a:Dec, b:Dec) with mk2:(y:Dec)->Foo(Causal, y) — position `a` is a
  # HARDCODED ground index (Causal), position `b` is the ctor's own arg y (no
  # shared key with `a`). Scrutinee Foo(Dcoupled, Dcoupled): position `a`
  # clashes directly (Causal vs Dcoupled, two distinct rigid ground terms, no
  # variable involved on either side) — verifying clash-detection also works
  # positionally within a multi-index family, complementing Test 3's
  # single-index Ix clash.
  test "Test 5a: a direct positional clash (no shared key) discharges the branch" do
    env =
      base_env()
      |> Inductive.declare(Inductive.family(:Foo, [], [{:a, @dec}, {:b, @dec}], 0),
           [Inductive.ctor(:mk2, [{:y, @dec}], [{:ctor, :Causal, []}, {:var, 0}])])
    foo_dd = {:data, :Foo, [], [{:ctor, :Dcoupled, []}, {:ctor, :Dcoupled, []}]}
    motive = {:lam, @dec, {:lam, @dec, {:lam, {:data, :Foo, [], [{:var, 1}, {:var, 0}]}, @dec}}}
    def_type = {:pi, foo_dd, @dec}
    body = {:lam, foo_dd, {:case, {:var, 0}, motive, [{:mk2, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)   # mk2 can only build Foo(Causal,_) ⇒ discharged
  end

  # Test 6 — Merge consistency (§5.5): mk:(p:Dec)->Foo(p,p) matched against
  # Foo(Causal, Dcoupled) gives p two candidate bindings (Causal, Dcoupled) that
  # are not equal ⇒ :impossible (discharge), NOT a silently-overwritten unsound
  # subst. Unlike Test 5a (a DIRECT positional clash via unify_one's own
  # catch-all, no shared key), this construction specifically routes through
  # bind_index's SAME-KEY conflict path (both index positions solve the one
  # telescope var `p`), by giving the branch a body that is ill-typed under BOTH
  # candidate refinements, so a silent-overwrite kernel would reject and only a
  # correct merge-conflict→impossible kernel accepts.
  test "Test 6: conflicting shared-key bindings yield impossible, not a silent overwrite" do
    env =
      base_env()
      |> Inductive.declare(Inductive.family(:Foo, [], [{:a, @dec}, {:b, @dec}], 0),
           [Inductive.ctor(:mk, [{:p, @dec}], [{:var, 0}, {:var, 0}])])
    foo_cd = {:data, :Foo, [], [{:ctor, :Causal, []}, {:ctor, :Dcoupled, []}]}
    motive = {:lam, @dec, {:lam, @dec, {:lam, {:data, :Foo, [], [{:var, 1}, {:var, 0}]}, @dec}}}
    def_type = {:pi, foo_cd, @dec}
    body = {:lam, foo_cd, {:case, {:var, 0}, motive, [{:mk, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end
```

- [ ] **Step 2: Run Tests 3/5a/6, verify RED** (Task-1 kernel has no `:impossible` yet)

Run: `mix test test/cure/core/case_soundness_index_test.exs -v`
Expected: the new discharge tests FAIL (`{:error, :branch_type}` — the dead branch's `{:type,0}` body is wrongly checked). The Test 3 companion (reachable) already PASSES. **Observe Test 6 pre-fix behavior specifically** (spec §8): today's zip does `Map.put` twice and would proceed with `{p := Dcoupled}` (last-write) then reject on the ill-typed body — so it fails for a "wrong reason" (rejects) rather than accepting. That is still a RED for our `assert :ok`, and confirms the silent-overwrite path is unsound-shaped; note this in the commit.

- [ ] **Step 3: Activate `:impossible` in `unify_indices`.** Two edits in `lib/cure/core/kernel.ex`:

(a) the clash fallthrough of `unify_one`:
```elixir
  defp unify_one(r, s, _arity, _subst) do
    if rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s),
      do: :impossible,
      else: :undecided
  end
```

(b) the same-key conflict in `bind_index`:
```elixir
        cond do
          old == term -> {:ok, subst}
          rigid_index?(old) and rigid_index?(term) and head_key(old) != head_key(term) ->
            :impossible
          true -> :undecided
        end
```

- [ ] **Step 4: Add the real `:impossible` arm** to `check_case_branches`. Replace the Task-1 `subst = case ... :impossible -> %{} end` block with an explicit discharge:

```elixir
            true ->
              %{args: tele, result_indices: result_indices} = ctor

              case unify_indices(ctx, result_indices, scrut_indices, arity) do
                :impossible ->
                  {:cont, :ok}                         # unreachable branch: body NOT checked

                verdict ->
                  subst = case verdict do
                    {:solved, s} -> s
                    :trivial -> %{}
                  end

                  {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele)
                  ctx_branch = specialize_branch_context(ctx_branch, subst)
                  s_values = Enum.map(result_indices, &Eval.eval(&1, Enum.reverse(arg_vals)))
                  ctor_value = {:vctor, cname, arg_vals}

                  expected =
                    motive_value
                    |> apply_motive(s_values ++ [ctor_value])
                    |> specialize_branch_value(ctx_branch, subst)

                  case check(ctx_branch, body, expected) do
                    :ok -> {:cont, :ok}
                    {:error, _} -> {:halt, {:error, :branch_type}}
                  end
              end
```

(Note: `unify_indices` no longer needs `ctx_branch`, so it is computed only in the non-impossible arm — `unify_indices` takes the outer `ctx`.)

- [ ] **Step 5: Run the kernel tests, verify GREEN**

Run: `mix test test/cure/core/case_soundness_index_test.exs -v`
Expected: ALL pass — Tests 3, 5a, 6 green (discharge); Test 3 companion still rejects; Tests 1/2/4/5b/7 still green.

- [ ] **Step 6: Full suite once**

Run: `mix test`
Expected: green. Confirm `git -C <worktree> status --short` shows no unexpected mutation (replay must stay git-clean beyond the intended edits).

- [ ] **Step 7: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/case_soundness_index_test.exs
git commit -m "feat(kernel): discharge impossible case branches; merge-conflict is impossible

unify_indices now returns :impossible on a definite rigid index-head clash or a
same-key merge conflict; check_case_branches discharges such a branch without
checking its body (a reachable branch with the same body is still rejected). This
closes the symmetric incompleteness (unreachable GADT branches) and makes an
inconsistent shared-key refinement a clean :impossible, never a silent overwrite."
```

---

## Self-review

**Spec coverage:** §4.1/§4.2 (new fn + one arm) → Task 1 Steps 5-6, Task 2 Step 4. §4.3 unifier rules (var both directions, tie-break, `:ctor`/`:data` structural with flattened spine, syntactic-equal, clash, undecidable, same-key merge) → Task 1 Step 5 + Task 2 Step 3. §4.4 de Bruijn (reify at outer depth + shift by arity; disjoint ranges) → Task 1 Step 5 `unify_indices`. §4.5 coverage unchanged → not touched (verified in §8 regression). §5 invariants → tests: §5.1→Test 2, §5.2→Tests 3/5a, §5.3→Test 4, §5.4→Test 5b, §5.5→Test 6. §8 discipline (tests first; red/characterization split; immutable) → Task 1 Steps 1-4 (write+characterize before Step 5 impl), Task 2 Steps 1-2. §9 success criteria → both tasks + Stage-5 full suite.

**Placeholder scan:** every code step has concrete Core terms and full function bodies. The one soft spot flagged inline: Task 1 Step 4's note that fixtures 2/4/5b/7 must be confirmed green and Test 1 red *by running*, adjusting only fixture de Bruijn indices (never the assertions) — this is characterization, not a placeholder.

**Type consistency:** `unify_indices/4` verdict `{:solved, map} | :trivial | :impossible` used consistently across `reduce_index_pairs`, `check_case_branches`, and both tasks; `unify_one/4` → `{:ok, subst} | :undecided | :impossible`; `bind_index/3` same; `head_key/1`, `rigid_index?/1`, `occurs_index?/2`, `unify_spine/4` arities consistent. The Task-1 `check_case_branches` arm computes `ctx_branch`/`arg_vals` before the verdict; Task 2 moves them into the non-impossible arm (noted in Step 4). `Quote.reify`, `Term.shift`, `Context.length`, `extend_with_telescope`, `apply_motive`, `specialize_branch_context/value` used with the exact arities from the reference sheet.
