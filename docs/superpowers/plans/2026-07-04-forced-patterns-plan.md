# Forced / Dot Patterns + Forced-Argument Erasure — Implementation Plan (#5)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Cure accept dependent matches where matching a constructor forces an equation between the scrutinee's index variables (Agda's `unifyIndices` Solution step), and add explicit `.e` dot-pattern syntax plus forced-argument erasure.

**Architecture:** Four layers, in dependency order. **K** — teach the kernel index unifier (`bind_index`/`unify_one` in `kernel.ex`) to *resolve-before-bind* a same-key conflict into a forced scrutinee-variable substitution instead of silently dropping it as `:undecided`. **E** — verify (and, only if the oracle shows a real gap, route) that forced substitution into branch context+goal before body elaboration (this is what flips the reach probes — Task 3's Step 1 empirically determines whether Task 2 alone already suffices, since the elaborator's own `replace_branch_vars` already applies `subst` unconditionally with no arity filter), elaborate `{:forced_pattern,…}` dot patterns by special-casing `constructor_pattern/1`, and anonymize forced-argument bindings via a side-table consulted by both `Cure.Elab.Erase` and `Cure.Elab.Emit`'s `branch_clause/3` (the actual runtime-pattern-binding site). **P** — add a leading-`:dot` prefix case to the shared expression parser producing `{:forced_pattern,…}`, guarded by a semantic check in `elaborate_expr_typed/4` (there is no separate pattern-position grammar to hook into). Verified by the differential oracle (cluster `dotpat`) plus kernel/parser/erase unit tests and the mandatory Antigen TCB gate.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel (`lib/cure/core/*`) + parser (`lib/cure/compiler/parser.ex`); differential oracle (`mix cure.oracle`, `idris2 --check`); Antigen (`lib/antigen/*`, `test/antigen/*`).

## Global Constraints

- **Source of truth:** the hardened spec `docs/superpowers/specs/antigen/2026-07-04-forced-patterns-design.md`. Read it before Task 2.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`; NEVER `git add -A`/`git add .` (a concurrent agent may share this worktree).
- **One build at a time:** never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; run the full suite once, alone, only at the gates (Task 4, Task 8).
- **TCB HARD-STOP:** the K change (Task 2) touches `lib/cure/core/kernel.ex`. It is pre-approved *only because it aligns `unify_indices` with Agda's Solution step* and *only conditional on passing Task 4's full gate* (new Antigen antibody + full Antigen suite + full test suite). If Task 4 fails, STOP and report — do not paper over.
- **Tests immutable once green.** Behavioral, not implementation-coupled.
- **Branch:** stay on `autopilot/lean-shape-matching` in this worktree.
- **`dp01`/`dp02` are blocked** by the independent auto-generalization defect (spec §1.2) — they are committed to the cluster marked `cure_stricter` with a reason and are NOT expected to flip in this plan. `dp01b` is the primary reach probe.
- **macOS has no `timeout`.** To bound a possibly-hanging elaboration, wrap it in `Task.async`/`Task.yield(t, ms)` + `Task.shutdown(t, :brutal_kill)` (never a shell `timeout`).

---

### Task 1: `dotpat` oracle cluster — red baseline

Author the probe fixtures and freeze today's (pre-fix) verdicts, establishing the red baseline. No production code changes.

**Files:**
- Create: `test/oracle/dotpat/dp01b_forced_eq_min.cure` + `.idr` (primary reach probe)
- Create: `test/oracle/dotpat/dp03_vect_head.cure` + `.idr` (reach probe, monomorphic)
- Create: `test/oracle/dotpat/dp04_absurd_distinct.cure` + `.idr` (regression guard — already passes)
- Create: `test/oracle/dotpat/dp01_forced_eq.cure` + `.idr`, `dp02_explicit_dot.cure` + `.idr` (blocked — kept as `cure_stricter`)
- Generated: `test/oracle/dotpat/verdicts.json` (via `mix cure.oracle dotpat`)

**Interfaces:**
- Produces: the `dotpat` cluster consumed by `test/oracle_replay_test.exs` (auto-discovered) and by later tasks' re-runs.

- [ ] **Step 1: Write `dp01b` (the non-confounded reach probe).**

`test/oracle/dotpat/dp01b_forced_eq_min.cure`:
```cure
mod Dp01b
  type Nat = Z | S(Nat)
  type SameLen indices (n: Nat, m: Nat)
    same : SameLen(k, k)
  fn cong({a: Nat}, {b: Nat}, p: SameLen(a, b)) -> SameLen(S(a), S(b)) = match p
    same() -> same()
end
```

`test/oracle/dotpat/dp01b_forced_eq_min.idr` — **faithful** form (spec §1.2 caveat: keep `a`/`b` implicit; do NOT spell them as separately-named top-level LHS patterns, which Idris rejects for an unrelated naming quirk):
```idris
%default total

data Nat2 = Z | S Nat2

data SameLen : Nat2 -> Nat2 -> Type where
  Same : SameLen k k

cong : {a : Nat2} -> {b : Nat2} -> SameLen a b -> SameLen (S a) (S b)
cong Same = Same
```

- [ ] **Step 2: Write `dp03` (Vec head — length index forces `S n`).**

`test/oracle/dotpat/dp03_vect_head.cure`:
```cure
mod Dp03
  type Nat = Z | S(Nat)
  type Vec(t: Type) indices (n: Nat)
    vnil : Vec(t, Z)
    vcons : (h: t) -> (r: Vec(t, k)) -> Vec(t, S(k))
  fn vhead({n: Nat}, v: Vec(Nat, S(n))) -> Nat = match v
    vcons(h, r) -> h
end
```
`test/oracle/dotpat/dp03_vect_head.idr`:
```idris
%default total

data Nat2 = Z | S Nat2

data Vec : Nat2 -> Type -> Type where
  VNil : Vec Z a
  VCons : a -> Vec k a -> Vec (S k) a

vhead : {n : Nat2} -> Vec (S n) Nat2 -> Nat2
vhead (VCons h r) = h
```
> Note: `Type`-param family, but `vhead` matches only `vcons` (non-empty). If `dp03` trips the auto-generalization defect at *declaration* time (Vec's `vcons` repeats no free index var, so it should be fine — `vcons`'s result index `S(k)` uses `k` once), keep it; if it unexpectedly fails at declaration, downgrade it to a monomorphic `Vec` over a fixed element type in Step 6 triage and note it.

- [ ] **Step 3: Write `dp04` (absurd/distinct — regression guard, already passing).**

`test/oracle/dotpat/dp04_absurd_distinct.cure`: a total function matching a `Vec` known to be non-empty (`Vec(Nat, S(n))`) that only lists the `vcons` branch and omits `vnil` — the `vnil` branch's result index `Z` clashes with the scrutinee index `S(n)`, so coverage accepts without a `vnil` arm via the existing Conflict clause:
```cure
mod Dp04
  type Nat = Z | S(Nat)
  type Vec(t: Type) indices (n: Nat)
    vnil : Vec(t, Z)
    vcons : (h: t) -> (r: Vec(t, k)) -> Vec(t, S(k))
  fn total_head({n: Nat}, v: Vec(Nat, S(n))) -> Nat = match v
    vcons(h, r) -> h
end
```
`.idr` analogue with `vhead (VCons h r) = h` and no `VNil` clause (Idris accepts by impossibility).
> `dp04` and `dp03` may be structurally identical; if so, keep only `dp03` and drop `dp04`, recording in the commit message that the Conflict-clause guard is already covered by `dp03`. Decide during Step 6 based on the actual verdicts.

- [ ] **Step 4: Write `dp01`/`dp02` (blocked) fixtures.**

`dp01_forced_eq.cure` = the spec §1.1 `Dp01` source verbatim. `dp02_explicit_dot.cure` = same but the forced index written as a dot pattern once §4.2 lands (for now, a copy of `dp01` with a comment `# TODO: dot syntax after Task 5`). Both `.idr` files use the faithful implicit form. These are expected `reject`(cure)/`accept`(idris) today.

- [ ] **Step 5: Run the oracle to generate verdicts.**

Run: `mix cure.oracle dotpat`
Expected: `dp01b` `cure=reject` (`{:unsolved_metavariables, _}`) / `idris=accept`; `dp03` `cure=reject`/`idris=accept`; `dp04` `cure=accept`/`idris=accept`; `dp01`/`dp02` `cure=reject`/`idris=accept`.

- [ ] **Step 6: Triage + set relations in `verdicts.json`.**

For each `reject`/`accept` divergence, set `relation: "cure_stricter"` with an honest `reason`:
- `dp01b`: `"forced-pattern gap (#5): matching `same` should force b:=a but the elaborator drops the equation; fixed by Task 2+3"`.
- `dp03`: `"forced-index gap (#5): vcons match should force the length index; fixed by Task 2+3"`.
- `dp01`/`dp02`: `"blocked by the independent auto-generalization defect (spec §1.2), NOT by forced patterns; do not flip in #5"`.
- `dp04` (if kept): `relation: "same"` (already `accept`/`accept`).

Confirm no `cure=accept`/`idris=reject` anywhere (that would be a soundness surprise — STOP and report if seen).

- [ ] **Step 7: Replay green, then commit.**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS (the `cure_stricter` entries are consistent because each has a reason + `cure=reject`).
```bash
git add -- test/oracle/dotpat/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(oracle): dotpat cluster — forced-pattern reach probes (red baseline) (#5)" -- test/oracle/dotpat/
```

---

### Task 2: K — resolve-before-bind Solution step in the kernel unifier (TCB)

Teach `bind_index` to resolve a same-key conflict by unifying old-vs-new instead of degrading to `:undecided`, producing a forced scrutinee-variable substitution. Kernel unit tests are the red-green here (the oracle probe does not flip until Task 3).

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`bind_index/3` → `/4` at kernel.ex:846-859, and its two call sites in `unify_one`'s first two clauses at kernel.ex:811,814. `reduce_index_pairs`/`unify_spine` already thread `arity` through to `unify_one` today and need no changes — they are unaffected callers, not additional edit sites.)
- Test: `test/cure/core/unify_indices_test.exs` (create)

**Interfaces:**
- Consumes: nothing new.
- Produces: `unify_indices/4` verdict `{:solved, subst}` where `subst` may now contain **scrutinee-var keys** (`key >= arity`) mapping to a forced term, in addition to the existing ctor-arg keys (`key < arity`). Contract otherwise unchanged (`:trivial`/`:impossible` cases preserved).

- [ ] **Step 1: Write the failing kernel unit test.**

`test/cure/core/unify_indices_test.exs`. `unify_indices/4` is private; test it through the public `branch_unify/4` (`kernel.ex:770`), which reuses it. Build a context and a `SameLen`-shaped signature via `Cure.Elab.Program.elaborate/1` of the `Dp01b` module (returns the `Core.Env`), then call `Kernel.branch_unify(ctx, :SameLen, :same, scrut_index_values)` where the scrutinee indices are two distinct outer neutral vars `a`,`b`.

```elixir
defmodule Cure.Core.UnifyIndicesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context}
  alias Cure.Elab.Program

  @src "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"

  defp sig, do: (fn -> {:ok, s} = Program.elaborate(@src); s end).()

  test "matching `same : SameLen(k,k)` against SameLen(a,b) forces b := a" do
    s = sig()
    # `Context.empty/1` (NOT `Context.new/1` — that function does not exist) takes
    # the Env/signature; `Context.extend/2` (NOT `push_var/2` — that function does
    # not exist either) pushes ONE variable of a given *value*-space type, mirroring
    # `test/antigen/lazy_unfold_antibody_test.exs`'s `Context.extend(Context.empty(env()), {:vdata, :Nat, []})`.
    # Two `Context.extend` calls give two outer vars: `a` (extended first, hence
    # LESS recent) at de Bruijn index 1, level 0; `b` (extended second, most
    # recent) at index 0, level 1 — per Context's own doc comment ("index 0 is
    # most-recently-bound" / `env/1`: "index 0 ... bound to the highest de Bruijn
    # level"). `branch_unify`'s `scrut_indices` are VALUES (levels, not indices —
    # `unify_indices` itself reifies them to indices via `Quote.reify`), so `a`'s
    # value is level 0 and `b`'s is level 1.
    ctx =
      Context.empty(s)
      |> Context.extend({:vdata, :Nat, []})
      |> Context.extend({:vdata, :Nat, []})

    # scrutinee index VALUES for [a, b] (SameLen(a, b) — a's index position first).
    scrut = [{:vneutral, {:nvar, 0}}, {:vneutral, {:nvar, 1}}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, :SameLen, :same, scrut)
    # `same` has arity 1 (the implicit `k`); the forced entry keys the OUTER var (>= arity).
    # Exactly one of a/b is forced to the other; assert a forced scrutinee-var entry exists.
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced != []
    assert {_k, {:var, _}} = hd(forced)   # forced to the other scrutinee var
  end
end
```
> If `:Nat` (declared locally inside `mod M … end`) is not the bare atom name `Inductive`/`Env` registers it under, adjust to whatever `Env.get_def`/`Inductive.get_ctor` on `s` actually shows for the locally-declared `Nat` family (print/inspect `s` if needed) — the executor must confirm this against the real signature, not assume. The behavioral assertion — a forced `key >= arity` entry appears — is the immutable contract; the exact context-building calls above are now pinned to real, existing `Context` functions (verified against `lib/cure/core/context.ex`, which exposes `empty/0`, `empty/1`, `extend/2`, `lookup/2`, `length/1`, `env/1` — no `new/1` or `push_var/2`).

- [ ] **Step 2: Run it — verify RED.**

Run: `mix test test/cure/core/unify_indices_test.exs`
Expected: FAIL — today `bind_index(0, b, %{0 => a})` returns `:undecided` (kernel.ex:855), so `subst = %{0 => a}` has no `key >= arity` forced entry.

- [ ] **Step 3: Implement resolve-before-bind.**

Thread `arity` into `bind_index` (rename to `bind_index/4`) and replace the `true -> :undecided` same-key branch (kernel.ex:855) with a recursive resolve:

```elixir
defp unify_one({:var, i}, s, arity, subst) when i < arity, do: bind_index(i, s, arity, subst)
defp unify_one(r, {:var, j}, arity, subst) when j >= arity, do: bind_index(j, r, arity, subst)
# ... other unify_one clauses unchanged ...

defp bind_index(key, term, arity, subst) do
  cond do
    occurs_index?(key, term) -> :undecided
    Map.has_key?(subst, key) ->
      old = Map.get(subst, key)
      cond do
        old == term -> {:ok, subst}
        rigid_index?(old) and rigid_index?(term) and head_key(old) != head_key(term) -> :impossible
        true ->
          # Resolve-before-bind (Agda Solution step): the key is already pinned to
          # `old`, so this pair really asserts `old =? term`. Re-unify them; for two
          # distinct scrutinee vars this routes through unify_one clause 2 and binds
          # the outer var (a forced equation). Terminates: see Task 4 measure (b).
          unify_one(old, term, arity, subst)
      end
    true -> {:ok, Map.put(subst, key, term)}
  end
end
```
> All existing `bind_index(k, t, subst)` call sites become `bind_index(k, t, arity, subst)`. No other clause changes. `unify_one(old, term, arity, subst)` for `old={:var,ja}` (ja>=arity), `term={:var,jb}` (jb>=arity) matches clause 2 → `bind_index(jb, {:var,ja}, arity, subst)` → fresh key → `{:ok, put jb=>a}` = forced `b ↦ a`.

- [ ] **Step 4: Run the unit test — verify GREEN.**

Run: `mix test test/cure/core/unify_indices_test.exs`
Expected: PASS.

- [ ] **Step 5: Add guard tests (occurs-cycle + injectivity + no-regression).**

Add to the same file: (a) an occurs-cycle case (`same : SameLen(k, S(k))`-style if expressible; else a hand-built index vector) asserting the verdict stays `{:solved,_}`-without-cycle or `:undecided`, never a cyclic bind; (b) a same-constructor injectivity case still decomposes; (c) a case with a genuine rigid-head clash still returns `:impossible`; (d) a plain ctor-arg-only match (e.g. `vcons`) still returns the same `{:solved, %{ctor-arg => term}}` as before (no forced entries when none are induced). Run the file; all PASS.

- [ ] **Step 6: Run the kernel + core test directory (scoped regression).**

Run: `mix test test/cure/core/`
Expected: PASS (no kernel regression). If any pre-existing core test changed verdict, STOP — the K change altered established behavior; investigate before proceeding.

- [ ] **Step 7: Commit.**
```bash
git add -- lib/cure/core/kernel.ex test/cure/core/unify_indices_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(kernel): resolve-before-bind forced-equation Solution step in unify_indices (#5)" -- lib/cure/core/kernel.ex test/cure/core/unify_indices_test.exs
```

---

### Task 3: E — route the forced substitution into branch context + goal

Make the elaborator apply forced scrutinee-var (`key >= arity`) substitution entries to the branch context and goal *before* elaborating the branch body, so the body's implicit-argument solve succeeds. This is the task that flips `dp01b`/`dp03`.

**Files:**
- Possibly: `lib/cure/elab/elaborator.ex` (`specialize_branch_context_subst/2` at line 1287, and `refine_branch_goal/6` at line 3074, both of which reach the elaborator's own private `replace_branch_vars/2` — its `{:var, i}` clause is at line 3123, NOT 3149 (3149 is that same function's later `{:case,…}` clause; the earlier draft of this correction cited the wrong clause of the same function)) — **conditional on Step 1's empirical finding, see below.**

**Correction (this review):** verified by direct reading of the current code, not assumed: `specialize_branch_context_subst/2` (elaborator.ex:1287-1300) and `refine_branch_goal/6` (elaborator.ex:3074-3094) both funnel through the elaborator's own `replace_branch_vars/2`, whose `{:var, i}` clause (elaborator.ex:3123) is `Map.get(subst, i, {:var, i})` — **an unconditional lookup with no `key < arity` filter of any kind.** This is the *exact same* no-filter shape as the kernel-side `specialize_branch_context/2` (`kernel.ex:885-897`, via kernel's own `replace_branch_vars/2` at `kernel.ex:911`) that this task's own prior draft already correctly hedged ("if it already keys uniformly on `{:var, i}` it needs no change") — but that hedge was, inconsistently, not extended to the elaborator-side copy. Given both copies are structurally identical unconditional lookups, **the most likely outcome is that Task 2 alone already flips `dp01b`/`dp03`, and Task 3 requires zero `elaborator.ex` changes** — but this must be confirmed empirically (Step 1), not asserted from either direction, since a static read cannot rule out some other gap (e.g. a goal-shape or reification mismatch this review did not find). Do NOT write speculative elaborator.ex code to "fix" a gap the oracle does not actually demonstrate.

**Interfaces:**
- Consumes: `{:solved, subst}` from Task 2 (now with forced `key >= arity` entries).
- Produces: branch bodies elaborated against a goal/context with the forced equation applied (whether that requires a code change or was already true).

- [ ] **Step 1: Re-run the oracle immediately after Task 2 lands — determine whether `dp01b`/`dp03` already flip GREEN.**

Run: `mix cure.oracle dotpat`
Two possible, equally acceptable outcomes — branch on the actual result, do not assume either in advance:
- **(A) Both already `cure=accept`/`idris=accept`:** the no-filter `replace_branch_vars` already routes the forced entry correctly. Skip Steps 2-3 entirely (no `elaborator.ex` diff). Go straight to Step 5 (set `relation: "same"`, replay, scoped regression) and Step 6 (commit — but the pathspec becomes `test/oracle/dotpat/verdicts.json` only; do not `git add` an unmodified `elaborator.ex`). Record in the commit message that Task 2 alone was sufficient and cite the no-filter `replace_branch_vars` finding.
- **(B) Either still `cure=reject`:** capture the exact current error for `dp01b` with the bounded-`Task` harness (Global Constraints) — this is the RED marker. Proceed to Steps 2-3 to find and fix the actual gap (which is NOT the `specialize_branch_context_subst`/`refine_branch_goal` filter this task's earlier draft assumed, since that has already been read and shown to have no filter — look instead at reification depth, goal shift arithmetic, or where `branch_unify`'s verdict fails to reach these functions at all for this call path).

- [ ] **Step 2 (only if outcome B): Locate the actual gap.**

Since `specialize_branch_context_subst`/`refine_branch_goal` are confirmed (by direct code reading, this review) to already apply `subst` unconditionally with no arity filter, re-read `elaborate_matched_branch/10` (elaborator.ex:2662-2726) end-to-end to find where the forced entry is dropped, filtered, or never reaches these functions for this specific call path (candidates: `carried != nil` branch takes a different path via `elaborate_carried_eq_branch/10` (elaborator.ex:2734) instead of `refine_branch_goal`; the body's OWN implicit-arg solve inside `elaborate_expr_typed` might not re-read the (already-refined) goal correctly; or a depth/shift mismatch in how `outer_depth`/`Context.length(ctx)` line up between `unify_indices`'s pre-shift and `extend_context`'s post-extension indexing). Name the exact function and line found.

- [ ] **Step 3 (only if outcome B): Implement the routing fix at the located gap.**

Whatever the concrete shape, the outcome must be: in the `same()`/`vcons` branch, the goal `SameLen(S(a), S(b))` is refined to `SameLen(S(a), S(a))` (forced `b ↦ a`) so the body `same()` type-checks.

- [ ] **Step 4 (only if outcome B): Run the oracle — verify GREEN flip.**

Run: `mix cure.oracle dotpat`
Expected: `dp01b` `cure=accept`/`idris=accept`; `dp03` `cure=accept`/`idris=accept`. `dp01`/`dp02` still `reject` (blocked — unchanged). No `cure=accept`/`idris=reject`.

- [ ] **Step 5: Set relations `same`, replay, scoped elab regression.**

Edit `verdicts.json`: `dp01b`/`dp03` → `relation: "same"`, empty `reason`. Keep `dp01`/`dp02` as `cure_stricter` (blocked).
Run: `mix test test/oracle_replay_test.exs test/cure/elab/`
Expected: PASS — the flip holds AND no other cluster/elaborator test regresses. (`test/cure/elab/` covers the whnf/miller/dependent-match suites; a regression here means either outcome-B's fix, or (outcome A) nothing at all, broke an existing match — if outcome A, this run is a pure regression check with zero expected diff-related risk.)

- [ ] **Step 6: Commit.**

**Outcome A (Task 2 alone sufficed, no `elaborator.ex` diff):**
```bash
git add -- test/oracle/dotpat/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(oracle): confirm kernel resolve-before-bind alone routes forced subst into branch goal (#5)" -- test/oracle/dotpat/verdicts.json
```

**Outcome B (a real elaborator.ex fix was needed at the Step 2-located gap):**
```bash
git add -- lib/cure/elab/elaborator.ex test/oracle/dotpat/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): route forced scrutinee-var substitution into branch goal (#5)" -- lib/cure/elab/elaborator.ex test/oracle/dotpat/verdicts.json
```

---

### Task 4: TCB GATE — Antigen antibody + full Antigen + full suite

The K change (Task 2) is soundness-critical. This gate must pass before the feature is considered sound. **Run suites one at a time.**

**Files:**
- Create: a standalone antibody test file under `test/antigen/` (e.g. `test/antigen/unify_indices_antibody_test.exs`) targeting the refined `unify_indices` — follow `test/antigen/lazy_unfold_antibody_test.exs`'s pattern (hand-constructed `ExUnit.Case`, direct `Kernel`/`Context`/`Inductive` fixtures). **Correction (this review): not `lib/antigen/`** — that directory hosts the separate, heavier catalog+generator+corpus "Assay" framework (`lib/antigen/assays/`, `lib/antigen/generators/`, wired through `lib/antigen/runner.ex`), a different idiom not used by any single-kernel-change antibody in this codebase; do not wire this gate into it.

**Interfaces:**
- Consumes: the refined `unify_indices` from Task 2.

- [ ] **Step 1: Write the antibody.**

The antibody must witness the spec §4.1 obligations:
- **Termination of the resolve-before-bind chase** — construct **chained** forced bindings (a scrutinee var forced through ≥2 intermediate already-bound keys in one branch), asserting `unify_indices` returns (does not loop). Use the bounded-`Task` harness to assert termination within a time budget.
- **No multi-key binding cycle** — construct two pairs that could mutually bind (`i ↦ {:var,j}` and a chase proposing `j ↦ {:var,i}`) and assert the verdict is not a cyclic substitution (either resolves consistently or `:undecided`/`:impossible`, never a subst with `i↦j` and `j↦i`). The spec (§4.1) requires the plan to EITHER state why this cannot arise given Cure's ctor-signature shape OR add an explicit multi-key cycle check to `bind_index` — this plan does the former, so the antibody test file's moduledoc must record the argument, not just assert the property: every RAW pair `reduce_index_pairs` feeds to `unify_one` has its ctor-scope side (`< arity`, from `result_indices`, which is always written over the ctor's OWN telescope) on the left and its outer/scrutinee side (`>= arity`, from the shifted `scrut_indices`) on the right (kernel.ex:790-794's pre-shift + the disjoint `i < arity`/`j >= arity` guards on `unify_one`'s first two clauses); the resolve-before-bind chase inside `bind_index` therefore only ever plants a NEW outer key's value from an EXISTING ctor-arg-key's (or an already-chased outer-key's) value — never the reverse — so newly-bound outer keys form a tree rooted at ctor-arg keys, not a graph that can point back into itself. If the antibody nonetheless finds a construction that produces `i↦j`/`j↦i`, that falsifies this argument — STOP, do not weaken the antibody, and add the explicit multi-key check instead (this would mean Task 2's implementation is unsound as written and needs a follow-up TCB fix, not a plan/test adjustment).
- **No normal-form collapse** — assert that a forced entry is produced ONLY when the two indices are the same ctor-scope variable's image: for each hand-constructed index-vector pair used in this antibody (mirroring `lazy_unfold_antibody_test.exs`'s concrete `plus_body`/`ctx1`/`neutral_n`-style fixtures — direct `Kernel`/`Context` construction, not a Cure source string), if `unify_indices` (via `branch_unify`) returns a forced `key >= arity` entry `k ↦ t`, assert that substituting `t` for `k` in the original two index vectors makes them convertible (`Conv.conv?` or the kernel's own conversion helper). **Correction (this review):** `test/antigen/lazy_unfold_antibody_test.exs` — the exact template this step names — is a hand-constructed `ExUnit.Case` test (`use ExUnit.Case, async: true`) with concrete fixtures, NOT a StreamData/`ExUnitProperties` property test; no antibody in `test/antigen/` targeting a specific kernel-TCB change uses StreamData (StreamData/`ExUnitProperties` only appears in the separate, heavier catalog+corpus+mutation "Assay" framework under `lib/antigen/assays/` + `test/antigen/generators/`, e.g. `mutation_health_gate_test.exs` — a different idiom, not wired for a single scoped kernel change, and out of scope here). Follow `lazy_unfold_antibody_test.exs`'s actual idiom: a handful of concrete, deliberately-constructed index-vector scenarios (including the chained and mutual-cycle cases below), not a generator/shrinker. If genuine randomized generation is wanted later, that is a separate follow-up wiring into the Assay framework, not this gate.

- [ ] **Step 2: Run the antibody.**

Run: `mix test test/antigen/<new_antibody>_test.exs` (exact path per the file created)
Expected: PASS.

- [ ] **Step 3: Run the full Antigen suite (alone).**

Run: `mix test test/antigen/`
Expected: PASS. A failure here means the kernel change broke a metatheory invariant — STOP and report; do not proceed to surface layers.

- [ ] **Step 4: Run the full test suite (alone).**

Run: `mix test`
Expected: PASS (all prior green tests + the new ones). If any regression, STOP and diagnose before Task 5.

- [ ] **Step 5: Commit.**
```bash
git add -- test/antigen/<new_antibody>_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): antibody for forced-equation unify_indices (TCB gate) (#5)" -- test/antigen/<new_antibody>_test.exs
```

---

### Task 5: P — explicit `.e` dot-pattern syntax

Add a leading-`:dot` prefix case to the shared expression parser producing `{:forced_pattern, meta, expr}`, plus a semantic check rejecting it outside pattern positions.

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_prefix` `case token.type do` at ~203-338: add a `:dot ->` clause)
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_expr_typed/4`, new clause for `{:forced_pattern,…}` — the semantic guard named in Step 3; this is a real, required code change for THIS task, not deferred to Task 6)
- Test: `test/cure/compiler/dot_pattern_parse_test.exs` (create — exercises both files: (a)/(b)/(d) are parser-only, (c) drives through elaboration too, see Step 1)

**Interfaces:**
- Produces: `{:forced_pattern, meta, expr_ast}` AST node in pattern position, consumed by Task 6.

- [ ] **Step 1: Write failing parser tests.**

`test/cure/compiler/dot_pattern_parse_test.exs`: (a) parsing a match arm `same(.a) -> ...` yields an arm whose pattern arg is `{:forced_pattern, _, {:variable, _meta, "a"}}` — `{:variable, meta, name}` is the confirmed surface-AST shape for a bare identifier used as a pattern (per `constructor_pattern/1`'s own `{:variable, _m, _v}` match, elaborator.ex:2926-2941 — not a guess); (b) `.(S(k))` parses the parenthesised compound form (`{:forced_pattern, _, {:function_call, _, [{:variable,_,"k"}]}}`-shaped, matching how `S(k)` itself already parses as a constructor-application pattern); (c) **negative**: a bare `.x` used as an ordinary *expression* (e.g. `let y = .x`) is rejected with `{:forced_pattern_not_in_pattern, _}` (the error Task 5 Step 3's `elaborate_expr_typed/4` clause returns — note this is an ELABORATION-time rejection, so this specific sub-case of the parser test must drive the fixture through elaboration, not the parser alone, since parsing `.x` in ANY position succeeds by design; the parser-only tests are (a)/(b)/(d)); (d) **non-regression**: `Std.String.from_int(5)` still parses to the existing `{:attribute_access,…}` chain, unaffected.

- [ ] **Step 2: Run — verify RED.**

Run: `mix test test/cure/compiler/dot_pattern_parse_test.exs`
Expected: FAIL — today a leading `.` hits the `parse_prefix` catch-all `{:unexpected_token,…}` (parser.ex:333-336).

- [ ] **Step 3: Implement the `:dot` prefix clause + semantic guard.**

Add to `parse_prefix`'s `case token.type do`:
```elixir
:dot ->
  {inner, state} = parse_forced_inner(advance(state))   # `.x` → var; `.(expr)` → parenthesised expr
  {{:forced_pattern, meta(token), inner}, state}
```
`parse_forced_inner` reads either a parenthesised `parse_expr` (`.(…)`) or a single primary (identifier/literal). Then add the **semantic** guard, at the exact site the spec (§4.2) requires this plan to name (it does not exist yet): `elaborate_expr_typed/4` (`lib/cure/elab/elaborator.ex`, a multi-clause public function starting at line 49, dispatching on the surface AST's tag — `{:variable,…}` at 52, `{:function_call,…}` at 69, `{:conditional,…}` at 327, etc.). Add a new clause `def elaborate_expr_typed({:forced_pattern, meta, _expr}, _names, _ctx, _env), do: {:error, {:forced_pattern_not_in_pattern, meta}}` — placed so it fires whenever a `{:forced_pattern,…}` node reaches ORDINARY expression elaboration (a `let` RHS, a function argument, any non-pattern position), since every such position ultimately calls `elaborate_expr_typed`. This is deliberately **only** the negative-guard half (`.x` rejected as an expression); the positive half — accepting `{:forced_pattern,…}` specifically as a constructor-argument **pattern** — is a separate, different call path (`constructor_pattern/1`, elaborator.ex:2926) and belongs to Task 6, not here; do not special-case pattern-position acceptance in this clause. Infix `.` (module paths) is untouched — it is handled in `parse_infix`'s `handle_infix_op` `:dot ->` (parser.ex:477-482) and never reaches this prefix clause.

- [ ] **Step 4: Run — verify GREEN.**

Run: `mix test test/cure/compiler/dot_pattern_parse_test.exs`
Expected: PASS (all four cases).

- [ ] **Step 5: Scoped parser regression + commit.**

Run: `mix test test/cure/compiler/`
Expected: PASS.
```bash
git add -- lib/cure/compiler/parser.ex lib/cure/elab/elaborator.ex test/cure/compiler/dot_pattern_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): leading-dot forced-pattern syntax + expression-position guard (#5)" -- lib/cure/compiler/parser.ex lib/cure/elab/elaborator.ex test/cure/compiler/dot_pattern_parse_test.exs
```

---

### Task 6: E — elaborate `{:forced_pattern,…}` dot patterns

Elaborate a dot pattern at a constructor-argument position: elaborate its expression and assert convertibility with the value index-unification determined; reject on mismatch; bind no new variable; record the forced Core term.

**Files:**
- Modify: `lib/cure/core/inductive.ex` (`Cure.Core.Env`'s defstruct, line 12 — add a `forced: %{}` field, default `%{}`, holding `%{{cname, branch_index} => MapSet.t(non_neg_integer())}`; see Interfaces below for why this task, not Task 7, owns the write)
- Modify: `lib/cure/elab/elaborator.ex` — **`constructor_pattern/1` (elaborator.ex:2926-2941), not a new/undiscovered site;** plus writing the accepted forced positions into `env.forced` at `{cname, branch_index}` from within `elaborate_matched_branch`/`elaborate_rematch_branch` (`branch_index` = this branch's position in `elaborate_branches`/`elaborate_rematch_branches`'s ctor-order accumulation — the same order the final `{:case,…}` branch list, and later `emit.ex`'s iteration over it, preserves). **Correction (this review):** read directly, `constructor_pattern/1` today enforces `Enum.all?(args, &match?({:variable, _m, _v}, &1))` — i.e. it hard-rejects ANY non-bare-variable constructor argument (including a future `{:forced_pattern,…}`) as `{:error, {:unsupported_pattern, :nested_constructor_arg}}`, the same catch-all used for genuine (not-yet-implemented, parity #3) nested constructor sub-patterns. This step must special-case `{:forced_pattern,…}` as an EXCEPTION to that all-variables rule without loosening it for actual nested constructor patterns (which must stay rejected). Its return shape `{:ok, {cname, vars}}` (a flat list of bindable names, one per ctor-arg position) must also change to distinguish a forced position from a bound-variable position per index — e.g. `{:ok, {cname, [{:var, name} | {:forced, expr}]}}` — and **every current call site that pattern-matches `{:ok, {cname, vars}}` / `{:ok, {^cname, pattern_vars}}` and treats the list as flat bindable names must be updated for the new per-position shape**: elaborator.ex:1187 (`partition_rematch_arms`), 1243 (`elaborate_rematch_branch`, feeds `branch_scope`), 1394 (`elaborate_matched_branch`, feeds `branch_scope`), 2590, 2653 (`ctor_arity`/`elaborate_matched_branch`'s other read). `branch_scope/2` (consumer of `pattern_vars`) must also be checked: a forced position contributes NO name to the branch's bound-variable list.
- Create: `test/oracle/dotpat/dp02b_explicit_dot.cure` + `.idr` (positive, non-blocked `SameLen` shape with an explicit correct dot), `test/oracle/dotpat/dp06_dot_mismatch_neg.cure` + `.idr` (negative)

**Interfaces:**
- Consumes: `{:forced_pattern,…}` from Task 5; the forced value from Task 2's subst.
- Produces: `{:forced_pattern_mismatch, written, determined}` error on disagreement; a persisted `Env.forced` entry per accepted forced position (see Step 3 — this task, not Task 7, must do the writing, since it is the only point in the pipeline where the raw `{:forced_pattern,…}` vs. bound-variable distinction is still visible; by the time a branch is fully elaborated into a plain Core `{cname, arity, body}` triple, that distinction is gone unless recorded now).

**Note on ownership (this review):** it is tempting to defer all `Env.forced` bookkeeping to Task 7 (since that is the task that actually NEEDS it for erasure), but that does not work — Task 7 runs during `Erase.erase`/`Emit`, long after Task 6's branch elaboration has already produced a plain, position-blind `{cname, arity, body}` Core term. Task 6 must add the `Env.forced` field (`lib/cure/core/inductive.ex:12`, `forced: %{}`) and write into it — at `{cname, branch_index}` — whenever `constructor_pattern/1`'s new per-position tags mark a position `{:forced, expr}` and the convertibility check accepts it. `branch_index` is available for free: `elaborate_branches`/`elaborate_rematch_branches` already iterate `Inductive.ctors_of(dname)` in a fixed, deterministic order and accumulate `acc ++ [branch]`, which is exactly the order the resulting `{:case,…}` term's branch list — and later `emit.ex`'s `lower/3` iteration over it — will preserve; the position in that accumulation IS `branch_index`. Task 7 then only *reads* `env.forced` in `emit.ex`; it does not populate it.

- [ ] **Step 1: Write the probes (RED).**

**Correction (this review):** neither `SameLen`'s `same` (arity 0 — its only var `k` is auto-generalized/implicit, never a written ctor argument) nor `Vec`'s `vcons` (explicit args are only `h`, `r`; the length index `S(k)` is a type-level index of the result, not a third written argument) actually exposes the forced index as something a surface pattern could dot-annotate — `vcons(.(S(k)), h, r)` from the earlier draft does not correspond to any real argument slot of `vcons` and cannot be written. Use a purpose-built family whose constructor declares the forced quantity as a genuine **explicit** argument instead:
```cure
mod Dp02b
  type Nat = Z | S(Nat)
  type Vec2(t: Type) indices (n: Nat)
    vnil2 : Vec2(t, Z)
    vcons2 : (k: Nat) -> (h: t) -> (r: Vec2(t, k)) -> Vec2(t, S(k))
  fn vhead2({n: Nat}, v: Vec2(Nat, S(n))) -> Nat = match v
    vcons2(.(n), h, r) -> h
end
```
Here `k` is an **explicit** (not auto-generalized) constructor argument, so matching `vcons2` against the scrutinee's index `S(n)` forces `k := n` — the user may write that position as the dot pattern `.(n)`, referencing the already-in-scope outer `n`. `.idr` counterpart uses an Idris dot pattern on the corresponding explicit argument (`vhead2 (VCons2 .(n) h r) = h`, `n` implicit-bound as today). `dp06_dot_mismatch_neg.cure`: same family, but the dot writes a value that unification does NOT determine — `vcons2(.(Z), h, r)` where the position must be `n` (a free variable), not the literal `Z` — expected `reject`; `.idr` counterpart uses the analogous mismatched dot (or Idris's own rejection of it).
Run `mix cure.oracle dotpat`; `dp02b` `reject` today (elaborator does not yet handle the `{:forced_pattern,…}` node — `constructor_pattern/1` currently rejects any non-bare-variable argument outright, see Task 6 Files), `dp06` `reject`.

- [ ] **Step 2: Verify RED.**
Run: `mix cure.oracle dotpat` and inspect the output directly: `dp02b` `cure=reject`/`idris=accept`, `dp06` `cure=reject`/`idris=reject` (both reject today, for different reasons — cure because the node isn't handled yet, idris because the design intent is unimplemented — so `dp06`'s CURRENT agreement is coincidental, not yet meaningful; Step 4 re-confirms it for the right reason). Do not run the full `oracle_replay_test.exs`/edit `verdicts.json` yet — that happens after Step 4's implementation, in Step 5.

- [ ] **Step 3: Implement dot-pattern elaboration.**

First, add `forced: %{}` to `Cure.Core.Env`'s defstruct (`lib/cure/core/inductive.ex:12`). In `constructor_pattern/1` (elaborator.ex:2926), change the arg-validation predicate to accept `{:variable,…}` (existing) OR `{:forced_pattern, _, expr}` (new) per argument, still rejecting any other nested shape; change the success return to carry per-position tags as described above. Then, in each of the five call sites listed above, for each `{:forced, expr}`-tagged position: elaborate `expr` to a Core term `t` in the branch context; obtain the value `d` that index unification determined for that position (from the branch subst / the ctor's result-index at that position after applying subst); assert `Conv.conv?` (or the elaborator's convertibility helper) between `t` and `d`. Equal ⇒ accept, bind no variable, and record the position by updating `env.forced` at key `{cname, branch_index}` (adding this position's index to that entry's `MapSet`; `branch_index` is this branch's position in `elaborate_branches`/`elaborate_rematch_branches`'s ctor-order accumulation) — this write is what makes the forced position visible to Task 7's erasure pass later. Unequal ⇒ `{:error, {:forced_pattern_mismatch, t, d}}`. `branch_scope/2`'s name-list construction must skip forced positions entirely (they contribute no bound name at any de Bruijn slot the body could reference).

- [ ] **Step 4: Verify GREEN.**
Run: `mix cure.oracle dotpat`
Expected: `dp02b` `cure=accept`/`idris=accept`; `dp06` `cure=reject`/`idris=reject`. Set `dp02b` → `same`, `dp06` → `same` (both agree). No `cure=accept`/`idris=reject`.

- [ ] **Step 5: Replay + scoped elab regression + commit.**
Run: `mix test test/oracle_replay_test.exs test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/cure/elab/elaborator.ex lib/cure/core/inductive.ex test/oracle/dotpat/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): elaborate forced (dot) patterns with convertibility check (#5)" -- lib/cure/elab/elaborator.ex lib/cure/core/inductive.ex test/oracle/dotpat/
```

---

### Task 7: E — forced-argument erasure in `Cure.Elab.Erase`

Ensure a forced constructor-argument position in a match branch is not bound to a fresh name in that branch's compiled clause. Per-branch, not via the ctor's static `quantities`.

**Correction (this review) — two load-bearing fixes to the earlier draft of this task:**

1. **Wildcard only; arity reduction is unsound here and must be explicitly ruled out.** `Cure.Elab.Erase.erase/2`'s existing `{:ctor,…}` clause (erase.ex:20-30) drops `:erased`-quantity args at **every construction site** of a constructor, uniformly, via the ctor's static, global `Inductive.ctor_quantities/2` — the runtime tuple representation for a given constructor is therefore a **fixed shape everywhere in the program** (same field count at every construction and every match). A forced position, by contrast, is `:present` in the ctor's static quantities (it is genuinely stored by OTHER, unrelated constructions of the same ctor) and only happens to be *derivable* in THIS ONE branch from an index equation already established by matching the scrutinee. Actually shrinking this branch's pattern arity (dropping the tuple slot from the pattern) would make the pattern's field count disagree with the constructor's actual, globally-`:present` runtime tuple shape — an Erlang tuple-pattern arity mismatch, i.e. this branch would then never match any real value of that shape. The only safe representation is a **true wildcard**: the tuple slot count in the pattern is unchanged, the forced position gets an anonymous/unused binding (`_`-prefixed name) instead of a fresh named variable. The plan's earlier "pin the exact representation… reduced arity or wildcard marker" phrasing incorrectly presented these as equivalent options — they are not; only the wildcard is sound, given the codebase's existing ctor-global erasure model. Do not implement arity reduction.
2. **The relevant runtime binding decision is made in `lib/cure/elab/emit.ex`, not `erase.ex`.** Read `emit.ex`'s `branch_clause/3` (emit.ex:255-276): it is the function that actually builds the compiled clause's tuple **pattern** and its per-field variable names (`V#{base+i}` for `:present`, `_f#{base+i}` for `:erased`), driven today *solely* by the ctor's static, global `Inductive.ctor_quantities/2` — it has no notion of "forced in this branch" at all. `Erase.erase/2`'s `{:case,…}` clause (erase.ex:75-77) only recurses into each branch's **body**; it does not touch pattern/binding construction and therefore, by itself, cannot make a forced position stop being bound to a named variable in the compiled output — that decision is emit.ex's alone. This task's own diff is therefore `emit.ex`'s `branch_clause/3` only, reading the per-branch forced-position set that **Task 6** already wrote into `env.forced` (see Task 6's Files/Interfaces) — for a position that is `:present` per `Inductive.ctor_quantities/2` **but** forced for this specific branch, emit the `_f#{base+i}`-style anonymous name instead of `V#{base+i}`, exactly mirroring the existing `:erased`-quantity naming branch, without touching `present`/`pattern` (the tuple shape stays as `Inductive.ctor_quantities/2` dictates). `erase.ex` needs no logic change (see point 3 and the Files list below) — it already threads `env` through unmodified.
3. **Mandatory representation choice: a side-table, not a widened Core term shape.** The branch triple `{cname, arity, body}` (Core's own `:case` representation) is destructured in well over a dozen places across **trusted-kernel** modules (`lib/cure/core/kernel.ex:704,940`, `lib/cure/core/term.ex` shift/subst/to_external/from_external, `lib/cure/core/eval.ex:73`) and untrusted-but-load-bearing modules (`lib/cure/elab/elaborator.ex:1670,3152`, `lib/cure/elab/subst.ex`, `lib/cure/elab/relevance.ex:138`, `lib/cure/elab/totality_closure.ex`, `lib/cure/elab/unify.ex`, `lib/cure/core/certificate.ex`, `lib/cure/core/serialize.ex`, `lib/cure/elab/emit.ex:255`). Widening this shared triple to a 4-tuple (`{cname, arity, body, forced_positions}`) would require touching **every one of these sites** just to keep them compiling/matching, including `kernel.ex`/`term.ex` — i.e. an undeclared, unscoped change to the TRUSTED KERNEL's core term representation, which is exactly the kind of TCB-scope creep the Global Constraints' TCB HARD-STOP is meant to prevent (only Task 2's kernel.ex change is pre-approved). **This task must therefore use a side-table keyed by a stable per-branch identity** (`{cname, branch_index}` within one `{:case,…}`), carried as a new field on `Cure.Core.Env` (see the Step 3 carrier below, confirmed by reading `lib/cure/compiler.ex`'s `dependent_codegen/1`: `env` is threaded unchanged, in one call, from elaboration straight into `Emit.compile_forms`) — NOT the shared Core term shape — so the Core `:case` triple itself never changes and none of the sites above need modification.

**Files:**
- Verify, do not expect to modify: `lib/cure/elab/erase.ex` (`erase/2`'s `{:case, s, m, branches}` clause, erase.ex:75-77 — `env` already passes through unmodified; this task's own diff is `emit.ex` only, per the correction above — but confirm this in the implementation rather than assuming, and modify here only if that confirmation surfaces a real gap)
- Modify: `lib/cure/elab/emit.ex` (`branch_clause/3`, emit.ex:255-276 — read `env.forced` (added and populated by Task 6, not this task); emit an anonymous name for a forced-but-`:present` position, unchanged tuple shape; `lower/3`'s `{:case,…}` clause, emit.ex:152-153, needs the branch index threaded to `branch_clause/3` via `Enum.with_index`)
- Test: `test/cure/elab/forced_erasure_test.exs` (create)

**Interfaces:**
- Consumes: the per-branch forced-position set recorded in Task 6.
- Produces: a compiled `:case` clause (post-`emit.ex` lowering) whose forced argument positions are bound to anonymous/unused names instead of fresh named variables; tuple pattern shape unchanged.

- [ ] **Step 1: Write the failing erasure test.**

`test/cure/elab/forced_erasure_test.exs`: elaborate a program with a forced constructor argument, run it through `Cure.Elab.Erase.erase/2` then `Cure.Elab.Emit`'s lowering (mirroring `Emit.function_form/2`'s own `Erase.erase` → `lower` pipeline), and assert the resulting compiled clause's pattern **binds an anonymous (`_`-prefixed) name at the forced position**, not a name the branch body could reference — while the pattern's **tuple arity is unchanged** (same field count as an equivalent non-forced branch of the same constructor). Behavioral assertion, driven through the public `Erase.erase/2` + `Emit` pipeline (not private helpers): the compiled clause for the forced branch does not reference a real (non-anonymous) variable at that position anywhere in its body, and matching it against an actual runtime value of that constructor (built via the ordinary, unrelated construction path) still succeeds — i.e. this is also a regression guard against the arity-reduction mistake ruled out above.

- [ ] **Step 2: Verify RED.**
Run: `mix test test/cure/elab/forced_erasure_test.exs`
Expected: FAIL — today `emit.ex`'s `branch_clause/3` (emit.ex:255-276) names every `:present`-quantity position `V#{base+i}` regardless of forcedness, so the forced position is bound to a real, referenceable name.

- [ ] **Step 3: Implement per-branch forced erasure via the side-table (mandatory — see the correction above; do NOT widen the Core `:case` branch triple).**

**Concrete, verified carrier (confirmed by reading the pipeline, not left open):** `Cure.Core.Env` (defined in `lib/cure/core/inductive.ex:1-12`, `defstruct families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: nil, builtins: %{}`) is the SAME single value threaded, unmodified, from elaboration all the way to emission — `lib/cure/compiler.ex`'s `dependent_codegen/1` calls `Cure.Elab.Program.check_ast_with_locals(ast)` to get `{:ok, env, local_defs}`, then passes that exact `env` directly into `Cure.Elab.Emit.compile_forms(env, module, local_defs)` in the same call, no serialization boundary in between. Task 6 has already added `forced: %{}` to `Env`'s defstruct and populated it as `%{{cname, branch_index} => MapSet.t(non_neg_integer())}` (forced argument positions per constructor + branch) — this task only *reads* `env.forced`, in `emit.ex`'s `branch_clause/3`. In `erase.ex`'s `{:case,…}` clause (erase.ex:75-77), confirm no logic change is needed beyond passing `env` through as it already does (the Core term itself stays a 3-tuple `{cname, arity, body}` — no destructure site anywhere else needs updating, since the shape never changes). In `emit.ex`'s `branch_clause/3` (emit.ex:255-276), thread `env` (already a parameter — `branch_clause(env, {cname, arity, body}, ctx)`) and a `branch_index` (the position of this branch within its `{:case,…}`'s branch list, obtainable from `lower/3`'s `Enum.map(branches, &branch_clause(env, &1, ctx))` via `Enum.with_index`) to look up `Map.get(env.forced, {cname, branch_index}, MapSet.new())`; for each position `i`: if `Inductive.ctor_quantities/2` says `:present` AND that set contains `i`, emit the field as `{:erased, :"_f#{base+i}"}` (reusing the EXISTING erased-field naming branch) instead of `{:present, :"V#{base+i}"}` — leaving `present`/`pattern` (hence tuple arity) computed exactly as today. Keep it **conservative**: only anonymize positions in the forced set; never touch a non-forced argument.

- [ ] **Step 4: Verify GREEN.**
Run: `mix test test/cure/elab/forced_erasure_test.exs`
Expected: PASS.

- [ ] **Step 5: End-to-end run-on-unix check (optional but preferred).**

If a forced-argument program can be made executable, build+run it on generic-unix AtomVM (`phase35/run-on-unix.sh` or `phase1/cure-avm run`) and confirm correct output with the arg erased. If not readily executable, note it and rely on the Core-level assertion in Step 1.

- [ ] **Step 6: Scoped regression + commit.**
Run: `mix test test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/cure/elab/erase.ex lib/cure/elab/emit.ex test/cure/elab/forced_erasure_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): anonymize forced constructor-argument bindings per match branch (#5)" -- lib/cure/elab/erase.ex lib/cure/elab/emit.ex test/cure/elab/forced_erasure_test.exs
```
(`Env.forced`'s field and its population were already committed in Task 6 — nothing in `lib/cure/core/inductive.ex` or the `constructor_pattern/1`-adjacent part of `lib/cure/elab/elaborator.ex` should be un-committed or pending by this point; if it is, that's a sign Task 6 wasn't actually completed and this task cannot proceed.)

---

### Task 8: Roadmap update + final full-suite gate

**Files:**
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§2 row #5)

- [ ] **Step 1: Confirm no unintended TCB spread.**

Run: `git diff --stat cd80b49 HEAD -- lib/cure/core/`
Expected: exactly two files — `lib/cure/core/kernel.ex` (the Task 2 `unify_indices` change, the only TCB-semantics-relevant diff) and `lib/cure/core/inductive.ex` (Task 6's purely additive `forced: %{}` field on `Cure.Core.Env`, consulted only by elaboration/emission bookkeeping — `Inductive`/`kernel.ex`'s own type-checking logic never reads it, so it does not extend the TCB gate's scope). If any file OTHER than these two changed under `lib/cure/core/`, investigate — that would be unintended spread.

- [ ] **Step 2: Update roadmap row #5.**

Mark #5 with a landed banner (mirror #11's style): summarize the K Solution-step fix, the E routing/dot-elaboration/erasure, and the P syntax; record that `dp01`/`dp02` remain **blocked** on the separately-tracked auto-generalization defect (so #5's `Type`-polymorphic-family coverage is partial pending that fix); set the status cell to ✅ (or 🟡 with a note if the blocked probes make you prefer "partial").

- [ ] **Step 3: Final full suite (alone).**

Run: `mix test`
Expected: PASS (2585+ prior tests plus all new ones, 0 failures).

- [ ] **Step 4: Commit.**
```bash
git add -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "docs(spec): #5 forced/dot patterns landed — roadmap update" -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
```

---

## Self-review notes (coverage against spec)

- Spec §4.1 (K Solution step) → Task 2 + Task 4 (soundness gate). Termination measures (a)/(b) and multi-key cycle → Task 4 Step 1 antibody obligations.
- Spec §4.2 (P dot syntax) → Task 5, incl. the semantic (not syntactic) guard — pinned, per the spec's own mandate, to `elaborate_expr_typed/4` (elaborator.ex:49+), not left for the executor to locate — + `Std.String` non-regression + bare-`.x`-as-expression negative.
- Spec §4.3 (E routing + dot elaboration) → Task 3 (empirical check first — Task 2 alone may already suffice, since `replace_branch_vars` has no arity filter; code change only if the oracle shows a real gap) + Task 6 (dot elaboration via `constructor_pattern/1`'s exception case + mismatch reject).
- Spec §4.4 (E erasure via `Cure.Elab.Erase`, per-branch not `quantities`) → Task 7, corrected to span **both** `erase.ex` (threads the side-table) and `emit.ex`'s `branch_clause/3` (the actual runtime-binding-name site), wildcard-only (arity reduction ruled out as unsound against the ctor-global ​runtime tuple shape), side-table-only (no Core `:case` triple widening, to avoid undeclared TCB/kernel.ex/term.ex blast radius).
- Spec §5.1 probes: `dp01b`/`dp03` (reach, Task 1→3), `dp04` (guard, Task 1), `dp02b`/`dp06` (dot, Task 6), `dp01`/`dp02` (blocked, Task 1). `dp05` occurs-cycle → Task 2 Step 5 kernel guard test (oracle form pinned only if expressible).
- Spec §6 non-goals respected: no higher-dimensional injectivity engine; auto-generalization defect explicitly NOT fixed here (Task 8 Step 2 records it as blocking dp01/dp02).
- Spec §7 risks: subst-key-overlap regression test → Task 2 Step 5(d)/Task 3; parser scope leak → Task 5 Step 1(c); erasure over-eagerness → Task 7 conservative rule (now also covering the arity-reduction-vs-wildcard distinction and the emit.ex binding site).
- **This review's additional findings (not in the original spec, found by direct code reading):** Task 3's "filter to remove" premise was empirically false for the elaborator-side `replace_branch_vars` (matches the kernel-side hedge that was already present but inconsistently applied); Task 4's "StreamData-backed" claim contradicted its own named template (`lazy_unfold_antibody_test.exs` is hand-constructed); Task 6's target function (`constructor_pattern/1`) has a hard-coded "all args must be bare variables" gate and five call sites assuming a flat name list, none named in the original draft; Task 7's erasure fix, as originally scoped to `erase.ex` alone, could not have had any runtime effect (the binding-name decision lives in `emit.ex`'s `branch_clause/3`), and its "reduced arity or wildcard" framing offered an actually-unsound option as if equivalent to the sound one.
