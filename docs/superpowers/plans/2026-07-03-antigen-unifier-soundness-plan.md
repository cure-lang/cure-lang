# Antigen V2 — Unifier Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** four new Antigen assays testing the two untrusted unification engines — `Cure.Elab.Unify` (Core terms + metavars, differential against trusted `Conv`) and `Cure.Types.Unify` (surface types, intrinsic + fixpoint self-consistency, no external oracle).

**Architecture:** A new `Antigen.Assays.Unifier` (4 assay ids) re-checks each engine's output through an injectable op-map seam. A new `Antigen.Generators.UnifyProblem` produces fixed catalogs of `%{t1, t2, ctx, sig, meta_ids}` / `%{t1, t2, expect}` challenges. Wired via `assay_module/1` + a dedicated test — the elab/normalizer fixed-catalog pattern, no Corpus/Coverage surgery.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` / `Cure.Elab.*` / `Cure.Types.*` edits.** All three reached read-only through the assay's op-map. No `:meck`, no new dependency.
- **StreamData quarantine:** the assay (`lib/antigen/assays/unifier.ex`) must contain NO literal `StreamData` token — including moduledoc/comments (the `architecture_test.exs` guard is a literal grep; V1 tripped on a comment mention). The generator (`lib/antigen/generators/unify_problem.ex`) may use it but this plan does not.
- **Assay `run/1,2` returns only `:ok | {:violation, term()}`** — no third outcome kind (`Runner.explore/1` has no catch-all; `@spec` forbids it). A `{:error,…}` rejection from either engine is NOT a violation (incompleteness/reach-gap is out of scope) → maps to `:ok`.
- **Fuel floor** `@assay_fuel 500_000`, wrapping every `Conv` call in `Cure.Core.Normalise.with_fuel/2`; treat `false`/`:fuel_exhausted` alike as non-agreement (`== true` guard).
- **One build/test run at any moment.** Tests immutable once written (sole exception: a test proven to encode wrong behavior, argued first). Run mix from the worktree root.

## Reconciliations with the spec (resolved deviations, for the reviewer)

1. **Split `tu_unify` op into `tu_unify` (solve) + `tu_reunify` (re-check).** The
   spec §4 op-map has a single `tu_unify` used for both the initial solve and the
   fixpoint re-unification. But a *systematically*-buggy unifier used for BOTH
   calls is self-consistent — its bug is "stable" — so the fixpoint negative
   control (a stub weakening the solve) would slip through when the same stub also
   runs the re-check. Splitting the op so the negative control weakens only the
   **solve** (`tu_unify`) while the **re-check** (`tu_reunify`) stays real makes
   the property load-bearing: the real re-unify discovers the binding the buggy
   solve dropped, `s' != s`, violation fires. Both default to `&Types.Unify.unify/3`.
2. **Occurs-check helper reads `eu_solution` single-level, then walks
   structurally.** Spec §5-open-item-#5 requires the V2a occurs helper to read
   solutions through the op-map's `eu_solution` (so the cyclic-`eu_solution`
   negative control is observed). But *following* solutions recursively during the
   structural walk would infinite-loop on the cyclic stub (`eu_solution(id) →
   S(?id) → eu_solution(id) → …`). Resolution: read `eu_solution(ctx, id)` **once**
   for the solved id, then check whether `{:meta, id}` occurs in that term
   **structurally without further `eu_solution` reads** (`occurs_raw?/2`). A
   well-formed solution is already fully forced, so one read suffices; the cyclic
   stub's returned term literally contains `{:meta, id}`, caught in the raw walk.
3. **Fixed catalog, no Corpus surgery** (same as V1/V3). `Challenge.new/1` uses
   `struct!` (no `kind` validation) and `Runner.replay_one/1` dispatches by assay
   only (never `to_pieces`/`Coverage`), so a lightweight `:unify_problem` kind
   (typespec entry only) runs as a fixed catalog via a dedicated test. Not added
   to `default_gen`; no `to_pieces`/`Coverage`/corpus-banking clauses.
4. **Every violation branch gets its own negative control, not just one per
   assay** (found in plan review). The spec's §4 negative-control list gives one
   representative stub per assay, but several `run/2` clauses branch into more
   than one distinct violation tag: Task 1's soundness clause produces both
   `{:meta_survived,…}` and the general `{:unify_unsound,…}`; Task 2's intrinsic
   clause produces `:occurs`, `:zonk_not_idempotent`, and `:meta_not_eliminated`;
   Task 4's intrinsic general clause produces `:apply_not_idempotent` and
   `:var_not_eliminated`. A branch no stub ever reaches is unverified dead
   code — an inverted condition or wrong tag there would go undetected, which is
   exactly the failure mode this whole op-map-seam architecture exists to catch.
   The plan adds one negative control per previously-untested branch: Task 1
   gains a no-op `eu_unify` stub (`{:ok, ctx}` returned unchanged — claims
   success without solving, so `zonk(t1)` is still the bare `{:meta,_}`) proving
   `{:meta_survived,…}`; Task 2 gains an `eu_zonk` stub that composes an
   `:ExtraWrap` ctor around the real zonk (so re-zonking a zonked term is never a
   fixed point) proving `:zonk_not_idempotent`, and an identity `eu_zonk` stub
   (trivially idempotent, never substitutes the solved meta away) proving
   `:meta_not_eliminated`; Task 4 gains a `tu_apply` stub that composes a
   `:tuple` wrapper around the real substitution (never a fixed point) proving
   `:apply_not_idempotent`.

## File structure

- **New** `lib/antigen/assays/unifier.ex` — `Antigen.Assays.Unifier`; `run/1`+`run/2` for the 4 ids; `@real` op-map; `@assay_fuel`; local `meta_free?/1`, `occurs_raw?/2`, `has_solved_var?/2`.
- **New** `lib/antigen/generators/unify_problem.ex` — `elab_soundness_challenges/0`, `elab_intrinsic_challenges/0`, `types_fixpoint_challenges/0`, `types_intrinsic_challenges/0`; Core/surface term helpers.
- **Modify** `lib/antigen/runner.ex` — 4 `assay_module/1` clauses → `Antigen.Assays.Unifier`.
- **Modify** `lib/antigen/challenge.ex` — add `:unify_problem` to `@type kind`.
- **New** `test/antigen/assays/unifier_test.exs` — all tests.

## Interfaces (verified against source; file:line where load-bearing)

- `Cure.Elab.Unify.unify(t1, t2, ctx, sig \\ nil) :: {:ok, MetaCtx.t()} | {:error, term()}` — capture as `&…/4`.
- `Cure.Elab.Unify.zonk(t, ctx) :: uterm()` — substitutes solutions away.
- `Cure.Elab.MetaCtx`: `new/0`, `solution/2 :: term | nil`, `put_solution/3` (public, `@doc false` — used only in a negative-control stub in the test). Metavar form `{:meta, id}`.
- `Cure.Core.Conv.conv?(t1, t2, env, depth, sig \\ nil) :: boolean` — call `conv?(z1, z2, [], 0, sig)`; this is exactly the δ-fallback's own call (`unify.ex:171`), gated on `Term.closed?` (`unify.ex:170`) — so every V2a catalog term MUST be closed (ctor-only, no `{:var,_}`).
- `Cure.Types.Unify.unify(t1, t2, subst) :: {:ok, subst, trace} | {:error, reason, trace}` — 3-tuple; the fixpoint compares the **subst** element, not the trace. `unify/3` with `subst=%{}` ≡ `unify/2`.
- `Cure.Types.Unify.apply_subst(type, subst) :: type`. Flex vars `{:type_var, name}` (string).

## Shared term helpers (test + generator)

Core (V2a), closed ctor-only so `Conv.conv?(_,_,[],0,_)` is valid:
`z0 = {:ctor, :Z, []}`; `s(x) = {:ctor, :S, [x]}`; `pair(a,b) = {:ctor, :Pair, [a, b]}`; `m(n) = {:meta, n}`; `ctx0 = Cure.Elab.MetaCtx.new()`.

Surface (V2b): `tv(n) = {:type_var, n}` (string `n`).

---

### Task 1: `Antigen.Assays.Unifier` — `unify/soundness` (V2a differential)

**Files:** Create `lib/antigen/assays/unifier.ex`; Create `test/antigen/assays/unifier_test.exs`.

- [ ] **Step 1: Write failing tests**

```elixir
defmodule Antigen.Assays.UnifierTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Unifier, Challenge}
  alias Antigen.Generators.UnifyProblem
  alias Cure.Elab.MetaCtx

  defp z0, do: {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}
  defp pair(a, b), do: {:ctor, :Pair, [a, b]}
  defp m(n), do: {:meta, n}

  defp sound_ch(t1, t2, meta_ids) do
    Challenge.new(kind: :unify_problem, assay: "unify/soundness", label: :translatable,
      payload: %{t1: t1, t2: t2, ctx: MetaCtx.new(), sig: nil, meta_ids: meta_ids}, seed: 1)
  end

  test "V2a soundness baseline: ?0 vs S Z solves and zonked sides are Conv-equal" do
    assert Unifier.run(sound_ch(m(0), s(z0()), [0])) == :ok
  end

  test "V2a soundness structural: Pair(?0, Z) vs Pair(S Z, ?1) — nested solve, Conv-equal" do
    assert Unifier.run(sound_ch(pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1])) == :ok
  end

  test "V2a soundness negative control: an eu_unify stub that solves ?0 to the WRONG ctor infects" do
    ch = sound_ch(m(0), s(z0()), [0])
    # claims success but solves ?0 := Z, not S Z -> zonked sides Z vs S Z, not Conv-equal
    k = %{Unifier.__real__() | eu_unify: fn _t1, _t2, ctx, _sig -> {:ok, MetaCtx.put_solution(ctx, 0, z0())} end}
    assert {:violation, {:unify_unsound, _, _}} = Unifier.run(ch, k)
  end

  test "V2a soundness negative control: an eu_unify stub that claims success without solving anything leaves a meta behind" do
    ch = sound_ch(m(0), s(z0()), [0])
    # claims success but stores no solution at all -> zonk(?0) is still {:meta,0},
    # not meta-free -> distinct branch from the wrong-ctor control above
    k = %{Unifier.__real__() | eu_unify: fn _t1, _t2, ctx, _sig -> {:ok, ctx} end}
    assert {:violation, {:unify_unsound, {:meta_survived, _}, _}} = Unifier.run(ch, k)
  end
end
```

- [ ] **Step 2: RED** — `MIX_ENV=test mix test test/antigen/assays/unifier_test.exs` → FAIL (Unifier undefined).

- [ ] **Step 3: Implement** — Create `lib/antigen/assays/unifier.ex`:

```elixir
defmodule Antigen.Assays.Unifier do
  @moduledoc """
  Property tests for the two untrusted unification engines against the trusted
  kernel (spec: antigen-unifier-soundness).

    * unify/soundness       — Elab.Unify: zonked sides are Conv-convertible (V2a).
    * unify/intrinsic       — Elab.Unify: occurs / idempotent-zonk / meta-closed.
    * unify_types/fixpoint  — Types.Unify: re-unifying the substituted sides needs
                              no new bindings (self-consistency; no external oracle).
    * unify_types/intrinsic — Types.Unify: occurs / idempotent-apply / var-elim.

  Every engine op goes through an injectable @real map (run/2) so negative controls
  weaken the code-under-test without touching the engines or using :meck. The
  re-check op (tu_reunify) is split from the solve op (tu_unify) so a systematically
  buggy solve is caught by a real re-check.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Unify, MetaCtx}
  alias Cure.Types.Unify, as: TUnify
  alias Cure.Core.{Conv, Normalise}

  @assay_fuel 500_000
  @real %{
    eu_unify: &Unify.unify/4,
    eu_zonk: &Unify.zonk/2,
    eu_solution: &MetaCtx.solution/2,
    conv: &Conv.conv?/5,
    tu_unify: &TUnify.unify/3,
    tu_reunify: &TUnify.unify/3,
    tu_apply: &TUnify.apply_subst/2
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :unify_problem} = c), do: run(c, @real)

  def run(%Challenge{kind: :unify_problem, assay: "unify/soundness", payload: p}, k) do
    case k.eu_unify.(p.t1, p.t2, p.ctx, p.sig) do
      {:error, _} ->
        :ok

      {:ok, ctx2} ->
        z1 = k.eu_zonk.(p.t1, ctx2)
        z2 = k.eu_zonk.(p.t2, ctx2)

        cond do
          not (meta_free?(z1) and meta_free?(z2)) ->
            {:violation, {:unify_unsound, {:meta_survived, p.t1}, p.t2}}

          Normalise.with_fuel(@assay_fuel, fn -> k.conv.(z1, z2, [], 0, p.sig) end) == true ->
            :ok

          true ->
            {:violation, {:unify_unsound, p.t1, p.t2}}
        end
    end
  end

  # local, independent of Elab.Unify's private meta_free?/1
  defp meta_free?({:meta, _}), do: false
  defp meta_free?({:data, _f, ps, is}), do: Enum.all?(ps ++ is, &meta_free?/1)
  defp meta_free?({:ctor, _c, args}), do: Enum.all?(args, &meta_free?/1)
  defp meta_free?({:app, f, x}), do: meta_free?(f) and meta_free?(x)
  defp meta_free?({:pi, d, c}), do: meta_free?(d) and meta_free?(c)
  defp meta_free?({:lam, d, b}), do: meta_free?(d) and meta_free?(b)
  defp meta_free?({:sigma, d, c}), do: meta_free?(d) and meta_free?(c)
  defp meta_free?(_), do: true
end
```

- [ ] **Step 4: GREEN** — `MIX_ENV=test mix test test/antigen/assays/unifier_test.exs` → PASS (4).

- [ ] **Step 5: Commit** — `feat(antigen): unify/soundness assay — Elab.Unify differential vs kernel Conv`

---

### Task 2: `unify/intrinsic` (V2a — occurs / idempotent-zonk / meta-closed)

**Files:** Modify `lib/antigen/assays/unifier.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "unify/intrinsic (V2a)" do
  defp intr_ch(t1, t2, meta_ids) do
    Challenge.new(kind: :unify_problem, assay: "unify/intrinsic", label: :translatable,
      payload: %{t1: t1, t2: t2, ctx: MetaCtx.new(), sig: nil, meta_ids: meta_ids}, seed: 1)
  end

  test "baseline: occurs-clean, zonk idempotent, metas eliminated" do
    assert Unifier.run(intr_ch(m(0), s(z0()), [0])) == :ok
    assert Unifier.run(intr_ch(pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1])) == :ok
  end

  test "occurs negative control: a cyclic eu_solution stub infects" do
    ch = intr_ch(m(0), s(z0()), [0])
    # id 0's 'solution' contains {:meta, 0} -> cyclic
    k = %{Unifier.__real__() | eu_solution: fn _ctx, 0 -> s(m(0)); _ctx, _ -> nil end}
    assert {:violation, {:occurs, _}} = Unifier.run(ch, k)
  end

  test "zonk-idempotence negative control: an eu_zonk stub that re-wraps its output each call infects" do
    ch = intr_ch(m(0), s(z0()), [0])
    # always adds another ExtraWrap layer on top of the real zonk -> re-zonking a
    # zonked term is never a fixed point
    k = %{Unifier.__real__() | eu_zonk: fn t, ctx -> {:ctor, :ExtraWrap, [Cure.Elab.Unify.zonk(t, ctx)]} end}
    assert {:violation, {:zonk_not_idempotent, _}} = Unifier.run(ch, k)
  end

  test "meta-closed negative control: an identity eu_zonk stub that never substitutes solutions away infects" do
    ch = intr_ch(m(0), s(z0()), [0])
    # identity is trivially idempotent (passes the zonk-idempotence check above)
    # but leaves the solved metavariable ?0 in place -> not meta-free
    k = %{Unifier.__real__() | eu_zonk: fn t, _ctx -> t end}
    assert {:violation, {:meta_not_eliminated, _}} = Unifier.run(ch, k)
  end
end
```

- [ ] **Step 2: RED** — the `unify/intrinsic` clause is undefined.

- [ ] **Step 3: Implement** — add to `unifier.ex`:

```elixir
def run(%Challenge{kind: :unify_problem, assay: "unify/intrinsic", payload: p}, k) do
  case k.eu_unify.(p.t1, p.t2, p.ctx, p.sig) do
    {:error, _} ->
      :ok

    {:ok, ctx2} ->
      z1 = k.eu_zonk.(p.t1, ctx2)
      z2 = k.eu_zonk.(p.t2, ctx2)

      cond do
        Enum.any?(p.meta_ids, fn id -> cyclic_solution?(id, ctx2, k) end) ->
          {:violation, {:occurs, p.meta_ids}}

        k.eu_zonk.(z1, ctx2) != z1 or k.eu_zonk.(z2, ctx2) != z2 ->
          {:violation, {:zonk_not_idempotent, p.t1}}

        not (meta_free?(z1) and meta_free?(z2)) ->
          {:violation, {:meta_not_eliminated, p.t1}}

        true ->
          :ok
      end
  end
end

# Read the solution for `id` ONCE through the op-map, then check structurally
# whether {:meta, id} occurs in it — WITHOUT following further solutions (a cyclic
# eu_solution stub would otherwise loop forever). nil solution = unsolved = clean.
defp cyclic_solution?(id, ctx, k) do
  case k.eu_solution.(ctx, id) do
    nil -> false
    sol -> occurs_raw?(id, sol)
  end
end

defp occurs_raw?(id, {:meta, id}), do: true
defp occurs_raw?(_id, {:meta, _}), do: false
defp occurs_raw?(id, {:ctor, _c, args}), do: Enum.any?(args, &occurs_raw?(id, &1))
defp occurs_raw?(id, {:data, _f, ps, is}), do: Enum.any?(ps ++ is, &occurs_raw?(id, &1))
defp occurs_raw?(id, {:app, f, x}), do: occurs_raw?(id, f) or occurs_raw?(id, x)
defp occurs_raw?(id, {:pi, d, c}), do: occurs_raw?(id, d) or occurs_raw?(id, c)
defp occurs_raw?(id, {:lam, d, b}), do: occurs_raw?(id, d) or occurs_raw?(id, b)
defp occurs_raw?(_id, _), do: false
```

> `occurs_raw?(id, {:meta, id})` repeats `id` across the two arguments of one
> clause head — empirically confirmed to compile and match correctly in Elixir
> (a repeated variable is scoped over the whole head, not just one argument, so
> this enforces equality exactly like `def eq(x, x), do: true`). The equivalent
> `defp occurs_raw?(id, {:meta, mid}) when mid == id, do: true` form is also
> valid and slightly more explicit if preferred; either is fine to implement.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): unify/intrinsic assay — occurs / idempotent-zonk / meta-closed`

---

### Task 3: `unify_types/fixpoint` (V2b — self-consistency, split op-map)

**Files:** Modify `lib/antigen/assays/unifier.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "unify_types/fixpoint (V2b)" do
  defp tv(n), do: {:type_var, n}
  defp fix_ch(t1, t2) do
    Challenge.new(kind: :unify_problem, assay: "unify_types/fixpoint", label: :translatable,
      payload: %{t1: t1, t2: t2}, seed: 1)
  end

  test "baseline: substituted sides re-unify with no new bindings" do
    assert Unifier.run(fix_ch(tv("T"), :int)) == :ok
    assert Unifier.run(fix_ch({:list, tv("T")}, {:list, :int})) == :ok
    assert Unifier.run(fix_ch(:int, :float)) == :ok  # widening; note the (:int,:float) direction
    assert Unifier.run(fix_ch({:named, "foo"}, {:record, :foo, []})) == :ok
  end

  test "negative control: a tu_unify solve that drops a needed binding infects (real re-check catches it)" do
    ch = fix_ch(tv("T"), :int)
    # solve stub deletes T; the REAL tu_reunify rediscovers T:=int, so s' != s
    k = %{Unifier.__real__() | tu_unify: fn t1, t2, s ->
      case Cure.Types.Unify.unify(t1, t2, s) do
        {:ok, sub, tr} -> {:ok, Map.delete(sub, "T"), tr}
        other -> other
      end
    end}
    assert {:violation, {:solution_unstable, _, _}} = Unifier.run(ch, k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `unifier.ex`:

```elixir
def run(%Challenge{kind: :unify_problem, assay: "unify_types/fixpoint", payload: p}, k) do
  case k.tu_unify.(p.t1, p.t2, %{}) do
    {:error, _, _} ->
      :ok

    {:ok, s, _} ->
      a = k.tu_apply.(p.t1, s)
      b = k.tu_apply.(p.t2, s)

      case k.tu_reunify.(a, b, s) do
        {:ok, s2, _} when s2 == s -> :ok
        _ -> {:violation, {:solution_unstable, p.t1, p.t2}}
      end
  end
end
```

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): unify_types/fixpoint assay — Types.Unify solution self-consistency`

---

### Task 4: `unify_types/intrinsic` (V2b — occurs / idempotent-apply / var-elim)

**Files:** Modify `lib/antigen/assays/unifier.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "unify_types/intrinsic (V2b)" do
  defp itc(t1, t2, expect) do
    Challenge.new(kind: :unify_problem, assay: "unify_types/intrinsic", label: :translatable,
      payload: %{t1: t1, t2: t2, expect: expect}, seed: 1)
  end

  test "baseline: occurs rejects cyclic; apply idempotent; solved var eliminated" do
    assert Unifier.run(itc(tv("T"), :int, :ok)) == :ok
    assert Unifier.run(itc({:list, tv("T")}, {:list, :int}, :ok)) == :ok
    assert Unifier.run(itc(tv("a"), {:list, tv("a")}, :error)) == :ok  # occurs -> engine errors
  end

  test "occurs negative control: a tu_unify stub that ACCEPTS a cyclic constraint infects" do
    ch = itc(tv("a"), {:list, tv("a")}, :error)
    k = %{Unifier.__real__() | tu_unify: fn _t1, _t2, s -> {:ok, s, []} end}  # wrongly accepts
    assert {:violation, {:occurs_not_detected, _, _}} = Unifier.run(ch, k)
  end

  test "var-elim negative control: a leaky tu_apply stub leaves a solved var in place" do
    ch = itc(tv("T"), :int, :ok)
    k = %{Unifier.__real__() | tu_apply: fn type, _s -> type end}  # identity: never substitutes
    assert {:violation, {:var_not_eliminated, _}} = Unifier.run(ch, k)
  end

  test "apply-idempotence negative control: a tu_apply stub that re-wraps its output each call infects" do
    ch = itc(tv("T"), :int, :ok)
    # always adds another tuple layer on top of the real substitution -> never a fixed point
    k = %{Unifier.__real__() | tu_apply: fn type, s -> {:tuple, [Cure.Types.Unify.apply_subst(type, s)]} end}
    assert {:violation, {:apply_not_idempotent, _}} = Unifier.run(ch, k)
  end
end
```

- [ ] **Step 2: RED.**

- [ ] **Step 3: Implement** — add to `unifier.ex` two clauses (cyclic-expected first) + `has_solved_var?/2`:

```elixir
def run(%Challenge{kind: :unify_problem, assay: "unify_types/intrinsic", payload: %{expect: :error} = p}, k) do
  case k.tu_unify.(p.t1, p.t2, %{}) do
    {:error, _, _} -> :ok
    {:ok, _, _} -> {:violation, {:occurs_not_detected, p.t1, p.t2}}
  end
end

def run(%Challenge{kind: :unify_problem, assay: "unify_types/intrinsic", payload: p}, k) do
  case k.tu_unify.(p.t1, p.t2, %{}) do
    {:error, _, _} ->
      :ok

    {:ok, s, _} ->
      a = k.tu_apply.(p.t1, s)
      keys = Map.keys(s)

      cond do
        k.tu_apply.(a, s) != a -> {:violation, {:apply_not_idempotent, p.t1}}
        has_solved_var?(a, keys) -> {:violation, {:var_not_eliminated, p.t1}}
        true -> :ok
      end
  end
end

defp has_solved_var?({:type_var, n}, keys), do: n in keys
defp has_solved_var?({:list, a}, keys), do: has_solved_var?(a, keys)
defp has_solved_var?({:tuple, ts}, keys), do: Enum.any?(ts, &has_solved_var?(&1, keys))
defp has_solved_var?({:fun, ps, r}, keys), do: Enum.any?(ps, &has_solved_var?(&1, keys)) or has_solved_var?(r, keys)
defp has_solved_var?({:adt, _n, ps}, keys), do: Enum.any?(ps, &has_solved_var?(&1, keys))
defp has_solved_var?({:map, kk, v}, keys), do: has_solved_var?(kk, keys) or has_solved_var?(v, keys)
defp has_solved_var?({:refinement, base, _, _}, keys), do: has_solved_var?(base, keys)
defp has_solved_var?(_, _keys), do: false
```

> Clause order matters: the `%{expect: :error}` head must precede the general `payload: p` head (Elixir tries clauses top-down; a bare `p` map would match a payload that also has `:expect`). Keep them adjacent in this order.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): unify_types/intrinsic assay — occurs / idempotent-apply / var-elim`

---

### Task 5: `UnifyProblem` catalogs + runner wiring

**Files:** Create `lib/antigen/generators/unify_problem.ex`; Modify `lib/antigen/runner.ex`, `lib/antigen/challenge.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "generator + runner wiring" do
  alias Antigen.Runner

  test "each catalog is non-empty and correctly tagged" do
    # non-emptiness asserted for all four explicitly: `Enum.all?/2` on `[]` is
    # vacuously true, so the tagging asserts below would silently pass even if a
    # catalog function returned no entries at all
    assert UnifyProblem.elab_soundness_challenges() != []
    assert UnifyProblem.elab_intrinsic_challenges() != []
    assert UnifyProblem.types_fixpoint_challenges() != []
    assert UnifyProblem.types_intrinsic_challenges() != []
    assert Enum.all?(UnifyProblem.elab_soundness_challenges(), & &1.assay == "unify/soundness")
    assert Enum.all?(UnifyProblem.elab_intrinsic_challenges(), & &1.assay == "unify/intrinsic")
    assert Enum.all?(UnifyProblem.types_fixpoint_challenges(), & &1.assay == "unify_types/fixpoint")
    assert Enum.all?(UnifyProblem.types_intrinsic_challenges(), & &1.assay == "unify_types/intrinsic")
  end

  test "runner dispatches every unify*/ id and the whole clean catalog is :ok under real ops" do
    all = UnifyProblem.elab_soundness_challenges() ++ UnifyProblem.elab_intrinsic_challenges() ++
          UnifyProblem.types_fixpoint_challenges() ++ UnifyProblem.types_intrinsic_challenges()
    assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
  end
end
```

- [ ] **Step 2: RED** — `UnifyProblem` undefined; `assay_module("unify/soundness")` has no clause.

- [ ] **Step 3: Implement** —

Create `lib/antigen/generators/unify_problem.ex` with the Core/surface helpers and four catalog functions. Elab payloads: `%{t1, t2, ctx: MetaCtx.new(), sig: nil, meta_ids: […]}` — closed ctor-only terms (bare solve `m(0)` vs `s(z0)`; structural `pair(m(0), z0)` vs `pair(s(z0), m(1))`; binder `{:pi, z0, m(0)}` vs `{:pi, z0, s(z0)}`; and — for soundness only, NOT intrinsic — a no-metavar reflexive `s(z0)` vs `s(z0)`). Types fixpoint payloads: `%{t1, t2}` covering `tv("T")` vs `:int`, `{:list, tv("T")}` vs `{:list, :int}`, `{:tuple,[tv("A"),tv("B")]}` vs `{:tuple,[:int,:string]}`, a refinement-stripped pair, an `:any`-widening pair, `:int` vs `:float` (that direction only), and `{:named,"foo"}` vs `{:record,:foo,[]}`. Types intrinsic payloads: `%{t1, t2, expect}` — the `:ok` entries plus one `expect: :error` cyclic entry (`tv("a")` vs `{:list, tv("a")}`).

In `lib/antigen/runner.ex` add four `assay_module/1` clauses → `Antigen.Assays.Unifier`. In `lib/antigen/challenge.ex` add `| :unify_problem` to the `@type kind` union.

- [ ] **Step 4: GREEN.** If a catalog entry legitimately fails under real ops, that is a REAL infection in an engine — STOP and report (do not weaken the test).

- [ ] **Step 5: Commit** — `feat(antigen): UnifyProblem catalogs + unify/* runner dispatch`

---

### Task 6: Full-suite verification

- [ ] **Step 1:** `MIX_ENV=test mix test test/antigen/assays/unifier_test.exs` — all green.
- [ ] **Step 2:** `MIX_ENV=test mix test test/antigen/architecture_test.exs` — quarantine green (no `StreamData` token in the assay).
- [ ] **Step 3:** `MIX_ENV=test mix test` (single authorized run) — all pass; count = prior + unifier_test rows.
- [ ] **Step 4:** `git status --short`; revert `test/antigen/seeds.sexp` if the run touched it; confirm clean. No commit (verification).

## Self-review

**Spec coverage:** §3 V2a soundness → Task 1; V2a intrinsic (occurs/idempotent-zonk/meta-closed) → Task 2; §3 V2b fixpoint → Task 3; V2b intrinsic (occurs/idempotent-apply/var-elim) → Task 4; §4 op-map seam → Task 1 `@real` (reconciled: split `tu_reunify`); §4 negative controls → each task's control test; §5 catalogs → Task 5 (fixed-catalog reconciliation); §6 invariants pinned (no engine edits, no StreamData token, `:ok|{:violation}` only, closed V2a terms); §7 non-goals respected (no fixes, no HOU, no determinism assay, no SMT); §9 tests 1-10 distributed across Tasks 1-5.

**Placeholder scan:** none — concrete code/commands throughout. One clause-ordering note flagged (`%{expect: :error}` must precede the general `payload: p` clause); the `occurs_raw?` repeated-var head was checked empirically and compiles as written, no fallback needed.

**Type consistency:** op-map keys `eu_unify/eu_zonk/eu_solution/conv/tu_unify/tu_reunify/tu_apply` identical in `@real` and every negative control. Infection tags `{:unify_unsound,…}`, `{:occurs,…}`, `{:zonk_not_idempotent,…}`, `{:meta_not_eliminated,…}`, `{:solution_unstable,…}`, `{:occurs_not_detected,…}`, `{:apply_not_idempotent,…}`, `{:var_not_eliminated,…}` consistent code↔tests. Payload shapes: elab `%{t1,t2,ctx,sig,meta_ids}`, types-fixpoint `%{t1,t2}`, types-intrinsic `%{t1,t2,expect}` — each produced by its catalog and consumed by its `run` clause.
