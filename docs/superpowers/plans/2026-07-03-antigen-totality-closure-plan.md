# Antigen V5 — Totality-Closure Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** two new Antigen assays testing the untrusted totality-closure driver `Cure.Elab.TotalityClosure` — end-to-end certification soundness (a diverging function in a type position must be rejected) and closure completeness (`type_level_fns ⊇` an independent type-position reachability walk).

**Architecture:** A new `Antigen.Assays.TotalityClosureAssay` (2 assay ids) re-checks the driver through an injectable op-map seam. A new `Antigen.Generators.ClosureEnv` produces fixed catalogs of pre-built `%Env{}` challenges. Wired via `assay_module/1` + a dedicated test — the elab/normalizer/unifier fixed-catalog pattern, no Corpus/Coverage surgery.

**Tech Stack:** Elixir; ExUnit (`async: true`); no new deps; `MIX_ENV=test` for all mix invocations (dev env crashes).

## Global Constraints

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NEVER a `Co-Authored-By` trailer.
- **Branch:** stay on `autopilot/antigen-tier-b` (no new worktree).
- **No `Cure.Core.*` / `Cure.Elab.*` edits.** The driver reached read-only through the assay's op-map. No `:meck`, no new dependency.
- **StreamData quarantine:** the assay (`lib/antigen/assays/totality_closure_assay.ex`) must contain NO literal `StreamData` token — moduledoc/comments included (the `architecture_test.exs` grep; V1 tripped on a comment).
- **Assay `run/1,2` returns only `:ok | {:violation, term()}`** — no third outcome kind. V5's incompleteness direction is out of scope.
- **No `@assay_fuel`/`Conv`** — `certify_type_level`/`type_level_fns` are static structural walks; the diverging function is never run (rejected structurally by `Certificate.terminating?`).
- **One build/test run at any moment.** Tests immutable once written. Run mix from the worktree root.

## Reconciliations with the spec (resolved deviations, for the reviewer)

1. **`{:int_type}`-only env construction** (spec §5, §8-1/§8-2). Every env under
   test builds from `Env.empty()` (NOT a raw `%Env{}` literal — `Env.empty/0` is the
   only place `certified: MapSet.new()` is set; the bare `defstruct` default is
   `nil`, and the accept-control's success path calls `Env.certify/2` →
   `MapSet.put(nil, …)` would crash). The def under test (`:loop` / `:total_id`) has
   an `{:int_type}`-only signature so `check_def` needs no family registration — no
   `{:unknown_family, …}` masking of the divergence check. The *vessel*
   family/ctor placing `{:global, :loop}` in a type position is a bare map patched
   into `env.families`/`env.ctors` (never kernel-checked — `certify_type_level`
   only calls `validate_certificate` on `type_level_fns`'s members, never
   `check_family`/`check_ctor`).
2. **Independent V5b walk uses the FULL `Cure.Core.Term` taxonomy, including
   `{:prim, op, args}`** (spec §8-3). `TotalityClosure.collect/1` has no `:prim`
   clause; the independent walk MUST recurse into `:prim`'s `args` so it does not
   inherit that blind spot. The clean completeness catalog deliberately does NOT
   nest a global inside a `:prim` (that would surface `collect/1`'s `:prim`
   omission as a real finding under real ops — out of V5's scope to adjudicate
   whether that omission is by-design); the `:prim` clause is exercised by an
   isolated unit test of the walk (`__reachable__/1`), not through the real closure.
3. **`expect: :reject | :accept` in the soundness payload.** The soundness assay
   handles both a diverging-in-type-position env (`:reject` — real certify must
   error) and an all-total control env (`:accept` — real certify must `{:ok}`). The
   accept case is a construction-sanity assertion (its failure means a malformed
   env per spec §8-2(a), not an engine soundness bug), surfaced as
   `{:total_env_not_certified,…}` so the whole-catalog-clean gate still catches it.
4. **Fixed catalog + new `:closure_env` kind** (spec §8-4). The `:def_group`
   payload (`%{focus: …}` + `Generators.Totality.env_of`) cannot carry a full
   pre-built `%Env{}`, so add a `:closure_env` kind (typespec-only). Every atom the
   generator names (`:loop`, `:total_id`, `:callee`, `:Vessel`, `:Wrap`, `:i`) must
   be a member of `Challenge.@known_atoms` (spec §8-5) — verified against source
   (`lib/antigen/challenge.ex`): `:total_id` (already listed, line 44) and `:i`
   (already listed, line 54) are **already interned**; only `:loop`, `:callee`,
   `:Vessel`, `:Wrap` are actually new additions. (Re-adding `:total_id`/`:i` would
   not be a compile error — Elixir tolerates a duplicate atom literal in a list —
   but Task 3 Step 3 should add only the 4 genuinely-new atoms, not all 6, to keep
   the list accurate.) No `to_pieces`/`from_pieces` clause is added (the catalog is
   replayed from the generator function, not banked — same as
   `surface_expr`/`unify_problem`), so no `String.to_existing_atom` decode path is
   introduced — confirmed via `test/antigen/corpus_atoms_test.exs`, which only
   scans the *committed corpus files* (`seeds.sexp`/`corpus.sexp`/`reach.sexp`/
   `reach_reify_split.sexp`) for hazard-strings; since `:closure_env` challenges are
   never `Corpus.append`ed, this addition is genuinely belt-and-suspenders, not
   load-bearing for any existing test.

## File structure

- **New** `lib/antigen/assays/totality_closure_assay.ex` — `Antigen.Assays.TotalityClosureAssay`; `run/1`+`run/2` for the 2 ids; `@real` op-map; the independent `__reachable__/1` walk (full taxonomy).
- **New** `lib/antigen/generators/closure_env.ex` — `soundness_challenges/0`, `completeness_challenges/0`; `%Env{}` builders + vessel-patch helpers.
- **Modify** `lib/antigen/runner.ex` — 2 `assay_module/1` clauses.
- **Modify** `lib/antigen/challenge.ex` — add `:closure_env` to `@type kind`; add the new atoms to `@known_atoms`.
- **New** `test/antigen/assays/totality_closure_assay_test.exs` — all tests.

## Interfaces (verified against source)

- `Cure.Elab.TotalityClosure.certify_type_level(%Env{}) :: {:ok, Env.t()} | {:error, {:totality_required, atom()}}`.
- `Cure.Elab.TotalityClosure.type_level_fns(%Env{}) :: MapSet.t(atom())`.
- `Cure.Core.Env`: `empty/0` (`%Env{families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: MapSet.new(), builtins: %{}}`); `add_def(env, name, type_term, body_term)`; `get_def(env, name) :: %{body: …} | nil`. `families :: %{atom => %{name, params, indices, level}}`, `ctors :: %{atom => %{name, args, result_indices, result_params, quantities}}`; telescopes are `[{name, type_term}]`; `result_indices` is a bare `[term]` list.
- `Cure.Core.Certificate.terminating?(name, body, env) :: boolean` — fast path `not calls?(name, body) -> true`; a bare self-call `λx. name x` is rejected (`decreasing?` sees `{:var,0}` not in the empty `smaller` set).
- `Cure.Core.Term` node taxonomy (for the independent walk): globals can nest in `:pi/:lam/:app/:sigma/:pair/:fst/:snd/:data/:ctor/:case/:eq/:refl/:rewrite/:prim`; leaves `:type/:var/:int_type/:int_lit/:float_type/:float_lit/:global`.

## Shared env helpers (test + generator)

```elixir
# Int -> Int
defp int_arrow, do: {:pi, {:int_type}, {:int_type}}
# diverging: loop = λx. loop x   (bare unconditional self-call)
defp loop_def(env), do: Cure.Core.Env.add_def(env, :loop, int_arrow(), {:lam, {:int_type}, {:app, {:global, :loop}, {:var, 0}}})
# total: total_id = λx. x   (no self-call -> terminating? fast path)
defp total_def(env), do: Cure.Core.Env.add_def(env, :total_id, int_arrow(), {:lam, {:int_type}, {:var, 0}})
# patch a vessel family whose index telescope mentions {:global, g}
defp with_family_index(env, fam, g),
  do: %{env | families: Map.put(env.families, fam, %{name: fam, params: [], indices: [{:i, {:app, {:global, g}, {:int_lit, 0}}}], level: 0})}
# patch a vessel ctor whose result_indices mention {:global, g}
defp with_ctor_index(env, ct, g),
  do: %{env | ctors: Map.put(env.ctors, ct, %{name: ct, args: [], result_indices: [{:app, {:global, g}, {:int_lit, 0}}], result_params: [], quantities: []})}
```

---

### Task 1: `TotalityClosureAssay` — `totality_closure/soundness` (V5a)

**Files:** Create `lib/antigen/assays/totality_closure_assay.ex`; Create `test/antigen/assays/totality_closure_assay_test.exs`.

- [ ] **Step 1: Write failing tests**

```elixir
defmodule Antigen.Assays.TotalityClosureAssayTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.TotalityClosureAssay, Challenge}
  alias Antigen.Generators.ClosureEnv
  alias Cure.Core.Env

  defp int_arrow, do: {:pi, {:int_type}, {:int_type}}
  defp loop_def(env), do: Env.add_def(env, :loop, int_arrow(), {:lam, {:int_type}, {:app, {:global, :loop}, {:var, 0}}})
  defp total_def(env), do: Env.add_def(env, :total_id, int_arrow(), {:lam, {:int_type}, {:var, 0}})
  defp with_family_index(env, fam, g),
    do: %{env | families: Map.put(env.families, fam, %{name: fam, params: [], indices: [{:i, {:app, {:global, g}, {:int_lit, 0}}}], level: 0})}
  defp with_ctor_index(env, ct, g),
    do: %{env | ctors: Map.put(env.ctors, ct, %{name: ct, args: [], result_indices: [{:app, {:global, g}, {:int_lit, 0}}], result_params: [], quantities: []})}

  defp snd_ch(env, expect) do
    Challenge.new(kind: :closure_env, assay: "totality_closure/soundness", label: :diverging,
      payload: %{env: env, expect: expect}, seed: 1)
  end

  test "reject baseline: diverging :loop in a family index — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "reject baseline: diverging :loop in a ctor result_indices — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_ctor_index(:Wrap, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "accept control: an all-total type-level env certifies (rejection is divergence-specific)" do
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    assert TotalityClosureAssay.run(snd_ch(env, :accept)) == :ok
  end

  test "negative control: an unconditional-{:ok} certify stub certifies the diverger" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    k = %{TotalityClosureAssay.__real__() | certify: fn e -> {:ok, e} end}
    assert {:violation, {:diverging_certified, _}} = TotalityClosureAssay.run(snd_ch(env, :reject), k)
  end

  test "negative control: a certify stub that errors on the all-total env is caught (:accept branch)" do
    # Every violation branch needs a negative control (V2 plan-review lesson).
    # :total_env_not_certified's `other` case is reachable under REAL ops — it is
    # exactly what a malformed accept-control env (spec §8-2(a)) or a driver
    # false-rejection would produce — unlike :unexpected_certify_result (see the
    # note after Step 3), so it gets its own dedicated stub here rather than being
    # exercised only implicitly by the accept-control test passing.
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    k = %{TotalityClosureAssay.__real__() | certify: fn _e -> {:error, {:totality_required, :total_id}} end}
    assert TotalityClosureAssay.run(snd_ch(env, :accept), k) ==
             {:violation, {:total_env_not_certified, {:error, {:totality_required, :total_id}}}}
  end
end
```

**Note on `:unexpected_certify_result` (no dedicated test):** this branch fires only
when `k.certify.(env)` returns something other than `{:ok, _}` or
`{:error, {:totality_required, _}}` — outside `certify_type_level/1`'s documented
`@spec` (verified: `lib/cure/elab/totality_closure.ex`), so it is structurally
unreachable under real ops for any input; only a custom, contract-violating stub
could trigger it. This matches existing codebase precedent — the analogous
`other -> {:error, {:unexpected, other}}` catch-alls in `lib/antigen/assays/elab.ex`
(lines 111, 172) are likewise untested. No new test is added for it; the branch
stays as defensive dead code under the real op-map, consistent with V1–V3.

- [ ] **Step 2: RED** — `MIX_ENV=test mix test test/antigen/assays/totality_closure_assay_test.exs` → FAIL (module undefined).

- [ ] **Step 3: Implement** — Create `lib/antigen/assays/totality_closure_assay.ex`:

```elixir
defmodule Antigen.Assays.TotalityClosureAssay do
  @moduledoc """
  Property tests for the untrusted totality-closure driver
  `Cure.Elab.TotalityClosure` (spec: antigen-totality-closure).

    * totality_closure/soundness    — a diverging function reachable from a type
      position must be REJECTED by `certify_type_level` (V5a). An all-total env
      must certify (`:accept` control).
    * totality_closure/completeness — `type_level_fns(env)` is a superset of an
      independent type-position reachability walk (V5b).

  The driver ops go through an injectable @real map (run/2); negative controls
  weaken them without touching `Cure.Elab`/`Cure.Core` or using :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.TotalityClosure
  alias Cure.Core.Env

  @real %{
    certify: &TotalityClosure.certify_type_level/1,
    type_level_fns: &TotalityClosure.type_level_fns/1
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :closure_env} = c), do: run(c, @real)

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :reject}}, k) do
    case k.certify.(env) do
      {:error, {:totality_required, _}} -> :ok
      {:ok, _} -> {:violation, {:diverging_certified, env}}
      other -> {:violation, {:unexpected_certify_result, other}}
    end
  end

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :accept}}, k) do
    case k.certify.(env) do
      {:ok, _} -> :ok
      other -> {:violation, {:total_env_not_certified, other}}
    end
  end
end
```

- [ ] **Step 4: GREEN** — `MIX_ENV=test mix test test/antigen/assays/totality_closure_assay_test.exs` → PASS (5). If a `:reject` baseline does NOT return `:ok`, trace `certify_type_level(env)` and `Kernel.validate_certificate(env, :loop)` manually (spec §8-2): confirm `check_def` returns `:ok` first and the rejection is `Certificate.terminating?` → `false`, not an unrelated `{:unknown_family, …}`. If the closure genuinely fails to reject a real diverger, STOP — that is a V5a soundness finding to report.

- [ ] **Step 5: Commit** — `feat(antigen): totality_closure/soundness assay — diverging-in-type-position rejection`

---

### Task 2: `totality_closure/completeness` (V5b) + independent walk

**Files:** Modify `lib/antigen/assays/totality_closure_assay.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "totality_closure/completeness (V5b)" do
  defp cmp_ch(env) do
    Challenge.new(kind: :closure_env, assay: "totality_closure/completeness", label: :positive,
      payload: %{env: env}, seed: 1)
  end

  # direct: :loop in a family index. transitive: :loop's body calls :callee, both must be reached.
  defp callee_def(env), do: Env.add_def(env, :callee, int_arrow(), {:lam, {:int_type}, {:var, 0}})
  defp loop_calls_callee(env),
    do: Env.add_def(env, :loop, int_arrow(), {:lam, {:int_type}, {:app, {:global, :callee}, {:var, 0}}})

  test "baseline: direct type-position global is in type_level_fns" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    assert TotalityClosureAssay.run(cmp_ch(env)) == :ok
  end

  test "baseline: transitive-callee global is in type_level_fns" do
    env = Env.empty() |> callee_def() |> loop_calls_callee() |> with_family_index(:Vessel, :loop)
    assert TotalityClosureAssay.run(cmp_ch(env)) == :ok
  end

  test "negative control: an empty type_level_fns stub misses everything" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    k = %{TotalityClosureAssay.__real__() | type_level_fns: fn _e -> MapSet.new() end}
    assert {:violation, {:closure_missed, _}} = TotalityClosureAssay.run(cmp_ch(env), k)
  end

  test "negative control: a type_level_fns stub dropping the transitive callee" do
    env = Env.empty() |> callee_def() |> loop_calls_callee() |> with_family_index(:Vessel, :loop)
    k = %{TotalityClosureAssay.__real__() | type_level_fns: fn _e -> MapSet.new([:loop]) end}  # drops :callee
    assert {:violation, {:closure_missed, missing}} = TotalityClosureAssay.run(cmp_ch(env), k)
    assert :callee in missing
  end

  test "independent walk recurses into :prim args (the clause collect/1 lacks)" do
    # a global nested in a :prim's args must be found by the independent walk;
    # this exercises reconciliation #2 in isolation, without the real closure.
    env = %{Env.empty() | families: %{P: %{name: :P, params: [], indices: [{:i, {:prim, :eq, [{:global, :buried}, {:int_lit, 0}]}}], level: 0}}}
    assert :buried in TotalityClosureAssay.__reachable__(env)
  end
end
```

- [ ] **Step 2: RED** — the `completeness` clause and `__reachable__/1` are undefined.

- [ ] **Step 3: Implement** — add to `totality_closure_assay.ex`:

```elixir
def run(%Challenge{kind: :closure_env, assay: "totality_closure/completeness", payload: %{env: env}}, k) do
  independent = __reachable__(env)
  closure = k.type_level_fns.(env)
  missing = MapSet.difference(independent, closure)

  if MapSet.size(missing) == 0 do
    :ok
  else
    {:violation, {:closure_missed, MapSet.to_list(missing)}}
  end
end

@doc false
# Independent re-derivation of type-position reachability (spec §3 V5b), over the
# FULL Cure.Core.Term taxonomy — crucially INCLUDING {:prim, op, args}, which
# TotalityClosure.collect/1 omits (spec §8-3). Returns a MapSet of global names.
def __reachable__(%Env{} = env) do
  seeds = reach_seeds(env)
  reach_close(env, MapSet.to_list(seeds), seeds)
end

defp reach_seeds(%Env{families: fams, ctors: cts}) do
  from_fams = fams |> Map.values() |> Enum.flat_map(fn f -> tele(f.params) ++ tele(f.indices) end)
  from_cts = cts |> Map.values() |> Enum.flat_map(fn c -> tele(c.args) ++ Enum.flat_map(c.result_indices, &globals/1) end)
  MapSet.new(from_fams ++ from_cts)
end

defp tele(t), do: Enum.flat_map(t, fn {_n, ty} -> globals(ty) end)

defp reach_close(_env, [], acc), do: acc
defp reach_close(env, [n | rest], acc) do
  case Env.get_def(env, n) do
    nil -> reach_close(env, rest, acc)
    %{body: b} ->
      fresh = b |> globals() |> Enum.reject(&MapSet.member?(acc, &1))
      reach_close(env, rest ++ fresh, Enum.reduce(fresh, acc, &MapSet.put(&2, &1)))
  end
end

defp globals({:global, n}), do: [n]
defp globals({:pi, d, c}), do: globals(d) ++ globals(c)
defp globals({:lam, d, b}), do: globals(d) ++ globals(b)
defp globals({:sigma, a, b}), do: globals(a) ++ globals(b)
defp globals({:app, f, a}), do: globals(f) ++ globals(a)
defp globals({:pair, a, b}), do: globals(a) ++ globals(b)
defp globals({:fst, p}), do: globals(p)
defp globals({:snd, p}), do: globals(p)
defp globals({:data, _n, ps, is}), do: Enum.flat_map(ps, &globals/1) ++ Enum.flat_map(is, &globals/1)
defp globals({:ctor, _n, args}), do: Enum.flat_map(args, &globals/1)
defp globals({:case, s, m, brs}), do: globals(s) ++ globals(m) ++ Enum.flat_map(brs, fn {_c, _ar, b} -> globals(b) end)
defp globals({:eq, t, a, b}), do: globals(t) ++ globals(a) ++ globals(b)
defp globals({:refl, a}), do: globals(a)
defp globals({:rewrite, p, m, b}), do: globals(p) ++ globals(m) ++ globals(b)
defp globals({:prim, _op, args}), do: Enum.flat_map(args, &globals/1)  # <- the clause collect/1 lacks
defp globals(_), do: []
```

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): totality_closure/completeness assay — independent type-position reachability walk`

---

### Task 3: `ClosureEnv` catalogs + runner wiring + atom interning

**Files:** Create `lib/antigen/generators/closure_env.ex`; Modify `lib/antigen/runner.ex`, `lib/antigen/challenge.ex`; append tests.

- [ ] **Step 1: Write failing tests**

```elixir
describe "generator + runner wiring" do
  alias Antigen.Runner

  test "each catalog is non-empty and correctly tagged" do
    assert ClosureEnv.soundness_challenges() != []
    assert ClosureEnv.completeness_challenges() != []
    assert Enum.all?(ClosureEnv.soundness_challenges(), & &1.assay == "totality_closure/soundness")
    assert Enum.all?(ClosureEnv.completeness_challenges(), & &1.assay == "totality_closure/completeness")
  end

  test "runner dispatches both totality_closure/ ids and the whole clean catalog is :ok" do
    all = ClosureEnv.soundness_challenges() ++ ClosureEnv.completeness_challenges()
    assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
  end
end
```

- [ ] **Step 2: RED** — `ClosureEnv` undefined; `assay_module("totality_closure/soundness")` has no clause.

- [ ] **Step 3: Implement** —

Create `lib/antigen/generators/closure_env.ex` with the env helpers (from "Shared env helpers", as private defs) and two catalog functions: `soundness_challenges/0` returns the family-index reject env, the ctor-index reject env, and the all-total accept env (each `Challenge.new(kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: …}, …)`); `completeness_challenges/0` returns the direct and transitive-callee envs (`payload: %{env: env}`).

In `lib/antigen/runner.ex` add `assay_module("totality_closure/soundness")` and `assay_module("totality_closure/completeness")` → `Antigen.Assays.TotalityClosureAssay`. In `lib/antigen/challenge.ex` add `| :closure_env` to `@type kind`, and add `:loop`, `:callee`, `:Vessel`, `:Wrap` to `@known_atoms` (spec §8-5 — every literal name the generator produces; `:total_id` and `:i` are already interned, verified against source — do not re-add).

- [ ] **Step 4: GREEN.** If a catalog entry fails under real ops, that is a REAL V5 finding — STOP and report (do not weaken the test).

- [ ] **Step 5: Commit** — `feat(antigen): ClosureEnv catalogs + totality_closure/* runner dispatch`

---

### Task 4: Full-suite verification

- [ ] **Step 1:** `MIX_ENV=test mix test test/antigen/assays/totality_closure_assay_test.exs` — all green.
- [ ] **Step 2:** `MIX_ENV=test mix test test/antigen/architecture_test.exs` — quarantine green.
- [ ] **Step 3:** `MIX_ENV=test mix test` (single authorized run) — all pass; count = prior + new rows.
- [ ] **Step 4:** `git status --short`; revert `test/antigen/seeds.sexp` if touched; confirm clean. No commit.

## Self-review

**Spec coverage:** §3 V5a soundness (reject + accept control) → Task 1; §3 V5b completeness → Task 2; §4 op-map seam → Task 1 `@real`; §4 negative controls → each task's control tests, including the two violation-branch checks (`:diverging_certified`, `:total_env_not_certified`) added in Task 1 — every `run/2` violation branch reachable under real ops now has a dedicated negative control, except the structurally-unreachable `:unexpected_certify_result` (justified inline after Task 1 Step 1, matching existing `elab.ex` precedent); §5 catalogs + §8-1 env construction → Task 3 (+ shared helpers); §6 invariants pinned (no engine edits, no StreamData token, `:ok|{:violation}` only, whole-catalog-clean STOP rule); §7 non-goals respected (no fix, no `totality/*` duplication, no `validate_certificate` test, no SMT); §8-2 masking guard (Task 1 Step 4 trace note); §8-3 full-taxonomy walk incl. `:prim` (Task 2 + isolated unit test); §8-4/§8-5 `:closure_env` kind + `@known_atoms` → Task 3 (only the 4 genuinely-new atoms — `:total_id`/`:i` already interned, verified against source).

**Test count reconciliation (corrects an undercount in the spec's §9 catalog, which lists 9 items):** Task 1 has 5 tests (V5a baselines ×2, accept control, `:diverging_certified` negative control, `:total_env_not_certified` negative control — one more than spec §9 items 1-4, per the fix above). Task 2 has 5 tests (V5b baselines ×2, `:closure_missed` negative controls ×2, plus the `:prim`-isolated `__reachable__/1` unit test that spec §5/§8-3 requires but §9 does not itemize separately). Task 3 has 2 tests (catalog shape, runner dispatch + whole-catalog-clean). Total: 12 tests across the three tasks.

**Placeholder scan:** none — concrete code/commands throughout. The one execution risk (real certify rejecting the diverger for the right reason) is a named Task-1-Step-4 trace with an explicit STOP-and-report fallback.

**Type consistency:** op-map keys `certify`/`type_level_fns` identical in `@real` and every control. Infection tags `{:diverging_certified,…}`, `{:total_env_not_certified,…}`, `{:closure_missed,…}`, `{:unexpected_certify_result,…}` consistent code↔tests. Payload shapes: soundness `%{env, expect}`, completeness `%{env}` — each produced by its catalog and consumed by its `run` clause. Env field shapes (`families`/`ctors`/`defs`) match `Cure.Core.Env` verbatim; `result_indices` is a bare `[term]` (walked with `globals/1` directly), telescopes are `[{name, ty}]` (walked with `tele/1`).
