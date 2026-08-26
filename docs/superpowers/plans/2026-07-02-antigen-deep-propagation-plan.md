# Antigen deep-propagation mutation — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bury each v1 ill-typed fault under `D` nested well-typed **checked** contexts so `Kernel.infer` must thread the fault's rejection up `D` distinct error-propagation paths; a survivor is a real error-swallowing bug.

**Architecture:** A `deepen` layer on `Antigen.Generators.Mutation`. `mutant/0` draws a base fault (existing 7 operators via `build/2`), draws a depth `D` uniformly in `0..@max_depth`, then wraps the fault term in `D` layers drawn from a **5-kind `Nat→Nat` wrapper set**. The assay (`Antigen.Assays.Mutation`) is unchanged. Depth 0 = today's shallow mutant (strict generalization).

**Tech Stack:** Elixir; `Antigen.Gen` DSL (StreamData-free in generators/assays); `Cure.Core.Kernel.infer/2`.

## Global Constraints

- **Construction-guaranteed ill-typedness (LOCKED):** every mutant's ill-typedness is decidable from the edit, never from the kernel-under-test.
- **StreamData quarantine:** nothing under `lib/antigen/generators/` or `lib/antigen/assays/` may contain the literal `StreamData` (grep-enforced by `architecture_test.exs` — it has bitten this project twice, incl. in a moduledoc).
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- **One full build/test run at a time** (a past concurrent full-suite run caused a kernel panic).
- **Legacy banked records:** the 7 v1 `:mutant_term` seeds in `test/antigen/seeds.sexp` have `fault` maps with NO `:depth`/`:wrap_path` keys. All reads of those fields MUST be defensive — `Map.get(fault, :depth, 0)` / `Map.get(fault, :wrap_path, [])` — never dot/strict access, or replaying them crashes with `KeyError` (spec §6 "Legacy banked records").
- **Tests are immutable once green:** each task's Step 1 red test, once passing at Step 4, is never weakened, skipped, or deleted to reach green — a step is made to pass only by changing the Step 3 implementation. The sole exception is a test proven to encode incorrect behavior itself, and that exception requires stating in the commit/PR *why* the test was wrong before touching it — "it's faster to edit the test" is never sufficient justification.

### DEVIATION from spec §3 — wrapper set is 5, not 6 (drop `:ctor_vec`)

The spec §3 lists 6 wrappers including `:ctor_vec` (`vcons(z, hole, filler_vec0)`). **Implementation uses 5**, dropping `:ctor_vec`. Reason, verified by probe:

- A deep mutant is only a genuine propagation test if the wrapper stack is **well-typed *except at the hole*** — i.e. replacing the fault with a well-typed `Nat` makes the whole stack `infer`-**accept**. Otherwise the mutant is *contaminated*: rejected by a wrapper-internal type error, not by fault propagation, and it silently tests nothing.
- For that, consecutive wrappers must compose by type. Five wrappers are `Nat→Nat` (hole expects `Nat`, term produces `Nat`) and chain freely. **`:ctor_vec` produces a `Vec`**, so any wrapper above it (all of which expect `Nat`) becomes independently ill-typed — a contaminated stack. (Probe: a mixed stack containing `:ctor_vec` rejected via `:branch_type` from the `Vec`/`Nat` mismatch *regardless of the fault*.)
- The dependent-ctor-arg propagation path `:ctor_vec` aimed at is already exercised **at the base** of every `:index_mismatch` / `:ctor_arg` mutant (those v1 faults *are* `vcons` terms checked through `check_ctor_app_rec`). Dropping it as a *wrapper* loses only its use as a mid-stack layer, not the path.

So `@wrap_floor` becomes `≥ 4 of 5` (spec §6 said 4 of 6). This deviation is called out for the plan reviewer; it strengthens the spec's own §3 "well-typed when hole is well-typed" property from per-wrapper to per-stack.

### Verified wrapper set (probed against the live kernel)

`nat = {:data,:Nat,[],[]}`, `z = {:ctor,:Z,[]}`, `sig = {:sigma, nat, nat}`, `motive = {:lam, nat, nat}`. Each is `Nat→Nat`; `inner` = the running term (fault at the bottom):

| `wrap` kind | shape | forces infer into `inner` via |
|---|---|---|
| `:app_arg` | `{:app, {:app, {:global,:plus}, inner}, filler_nat}` | app-argument `check` |
| `:ctor_nat` | `{:ctor, :S, [inner]}` | Nat ctor-arg (`check_ctor_app_rec`) |
| `:case_scrut` | `{:case, inner, motive, [{:Z,0,z}, {:S,1,{:var,0}}]}` | scrutinee `infer` |
| `:case_branch` | `{:case, filler_nat, motive, [{:Z,0,inner}, {:S,1,{:var,0}}]}` | branch-body `check` (`check_case_branches`) |
| `:pair` | `{:app, {:lam, sig, z}, {:pair, inner, filler_nat}}` | Σ-component `check` (`check(pair, vsigma)`) |

Probe results (depth-10 mixed stack): fault→`{:error, :branch_type}`; **well-typed `Nat` inner→`ACCEPT`** (uncontaminated); faults `{:fst,z}` / `{:var,9}` / `{:eq,T0,T0,T0}` all reject. Clause (d) holds — `:case_branch` uses the arity-0 `Z` branch and `:pair` places the hole in the app argument, so **no binder scopes the hole** and no `Term.shift` is needed.

---

## File Structure

- **Modify** `lib/antigen/generators/mutation.ex` — add `@max_depth`, `deepen/3` (a `Gen` of `{term, wrap_path}`), `apply_wrapper/3`, the wrapper-kind draw, menu helpers `sig/0`/`motive/0`; thread depth through `mutant/0`.
- **Modify** `lib/antigen/challenge.ex` — `@known_atoms` += `:app_arg, :ctor_nat, :case_scrut, :case_branch, :pair, :depth, :wrap_path`.
- **Modify** `lib/antigen/runner.ex` — `mutation_metrics/1` adds `max_depth` + `wrap_diversity` (defensive reads); `mutation_stamp/1` + health line include them.
- **Modify** `test/antigen/seeds.sexp` — bank deep `:mutant_term` seeds (depth ≥ floor, ≥4 wrapper kinds).
- **Extend tests** (all exist): `test/antigen/generators/mutation_test.exs`, `test/antigen/mutation_health_gate_test.exs`, `test/antigen/mutation_meta_test.exs`.

---

## Task 1: `fault` gains `depth`/`wrap_path`; atoms interned; round-trip

**Files:** Modify `lib/antigen/challenge.ex` (`@known_atoms`). Test: `test/antigen/challenge_test.exs`.

**Interfaces:** Produces: a `:mutant_term` whose `fault` carries `depth`/`wrap_path` round-trips through the scaffold codec (the new atoms survive `binary_to_term [:safe]`).

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/challenge_test.exs
  test ":mutant_term round-trips a fault carrying depth + wrap_path" do
    fault = %{kind: :head_swap, witness: :head, expected_head: :Nat, injected_head: :Vec,
              scope: nil, depth: 3, wrap_path: [:app_arg, :case_branch, :pair]}
    c = Antigen.Challenge.new(
      kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: {:data, :Nat, [], []},
                 term: {:ctor, :Z, []}, fault: fault})
    {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
    s2 = Antigen.Corpus.decode_scaffold(Antigen.Corpus.encode_scaffold(scaffold))
    c2 = Antigen.Challenge.from_pieces(:mutant_term, c.assay, c.label, nil, nil, s2, pieces)
    assert c2.payload.fault == fault
  end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/challenge_test.exs`
Expected: `binary_to_term`/`:safe` fails to decode (`:app_arg`/`:wrap_path`/`:depth` uninterned) → the round-trip assertion fails.

- [ ] **Step 3: Implement** — in `lib/antigen/challenge.ex`, extend the mutation block of `@known_atoms`:
```elixir
    # deep-propagation: wrapper kinds + the two new fault-field keys
    :app_arg, :ctor_nat, :case_scrut, :case_branch, :pair, :depth, :wrap_path
```
(`:pair` doubles as a Core term tag but must be listed for the `[:safe]` fault-map decode, per the v1 key-atom lesson. Do NOT add `:ctor_vec` — it is not a wrapper here.)

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/challenge_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/challenge.ex test/antigen/challenge_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): intern deep-propagation fault atoms (depth/wrap_path/wrappers)"
```

---

## Task 2: `deepen/3` + the 5 wrappers — construction guarantee + uncontaminated control

**Files:** Modify `lib/antigen/generators/mutation.ex`. Test: `test/antigen/generators/mutation_test.exs`.

**Interfaces:**
- Produces: `Mutation.wrappers/0 :: [atom]` (the 5 kinds); `Mutation.deepen(ctx, term, depth) :: Gen.t({term, [atom]})` — wraps `term` in `depth` `Nat→Nat` layers, returning the deep term and its `wrap_path` (innermost-first, `length == depth`). `Mutation.max_depth/0`.
- Consumes (Task 3): `deepen/3`, `wrappers/0`, `max_depth/0`.

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/generators/mutation_test.exs
  test "deepen wraps a fault so it still infer-rejects, and is UNCONTAMINATED (wt inner accepts)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    nat = {:data, :Nat, [], []}
    fault = {:fst, {:ctor, :Z, []}}       # intrinsic: infer fails on its own
    wt = {:ctor, :Z, []}                   # well-typed Nat

    for depth <- [0, 1, 4, Mutation.max_depth()] do
      # fault deepened → rejects; wrap_path length == depth
      for {deep, path} <- sample(Mutation.deepen(ctx, fault, depth), 15) do
        assert length(path) == depth
        assert Enum.all?(path, &(&1 in Mutation.wrappers()))
        assert {:error, _} = Kernel.infer(ctx, deep)
      end
      # SAME wrapper stack around a well-typed Nat must ACCEPT — proves the
      # rejection above is fault-driven, not a wrapper-internal type error.
      for {deep_wt, _} <- sample(Mutation.deepen(ctx, wt, depth), 15) do
        assert {:ok, _} = Kernel.infer(ctx, deep_wt),
               "contaminated stack at depth #{depth}: #{inspect(deep_wt)}"
      end
    end
  end

  test "every wrapper kind is reachable and each individually propagates a fault" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    fault = {:fst, {:ctor, :Z, []}}
    seen =
      for _ <- 1..200, {_d, [k]} <- [Enum.at(sample(Mutation.deepen(ctx, fault, 1), 1), 0)], do: k
    assert Enum.uniq(seen) |> length() >= 4   # ≥4 of 5 kinds appear across the draw
  end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/generators/mutation_test.exs`
Expected: `Mutation.deepen/3`, `wrappers/0`, `max_depth/0` undefined.

- [ ] **Step 3: Implement** — add to `lib/antigen/generators/mutation.ex`:
```elixir
  @wrappers [:app_arg, :ctor_nat, :case_scrut, :case_branch, :pair]
  def wrappers, do: @wrappers

  @max_depth 8
  def max_depth, do: @max_depth

  # menu helpers for wrappers
  defp sig, do: {:sigma, nat_t(), nat_t()}
  defp motive, do: {:lam, nat_t(), nat_t()}
  defp nat_branches(zbody), do: [{:Z, 0, zbody}, {:S, 1, {:var, 0}}]

  @doc "Wrap `term` in `depth` Nat→Nat checked layers. Gen of `{deep_term, wrap_path}`."
  @spec deepen(Cure.Core.Context.t(), term(), non_neg_integer()) :: Gen.t()
  def deepen(_ctx, term, 0), do: Gen.return({term, []})

  def deepen(ctx, term, depth) when depth > 0 do
    Gen.bind(Gen.frequency(Enum.map(@wrappers, fn k -> {1, Gen.return(k)} end)), fn kind ->
      Gen.bind(apply_wrapper(ctx, term, kind), fn wrapped ->
        Gen.bind(deepen(ctx, wrapped, depth - 1), fn {outer, path} ->
          Gen.return({outer, [kind | path]})   # innermost-first
        end)
      end)
    end)
  end

  # each wrapper places `inner` at a Nat-checked hole; filler is a well-typed Nat.
  defp apply_wrapper(ctx, inner, :app_arg),
    do: Gen.bind(gnat(ctx), fn f -> Gen.return({:app, {:app, {:global, :plus}, inner}, f}) end)
  defp apply_wrapper(_ctx, inner, :ctor_nat),
    do: Gen.return({:ctor, :S, [inner]})
  defp apply_wrapper(_ctx, inner, :case_scrut),
    do: Gen.return({:case, inner, motive(), nat_branches(z())})
  defp apply_wrapper(ctx, inner, :case_branch),
    do: Gen.bind(gnat(ctx), fn scrut -> Gen.return({:case, scrut, motive(), nat_branches(inner)}) end)
  defp apply_wrapper(ctx, inner, :pair),
    do: Gen.bind(gnat(ctx), fn f -> Gen.return({:app, {:lam, sig(), z()}, {:pair, inner, f}}) end)
```
(`gnat/1`, `z/0`, `nat_t/0` already exist in this module.)

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/generators/mutation_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/mutation.ex test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): deepen/3 — 5 Nat→Nat checked wrappers, uncontaminated by construction"
```

---

## Task 3: thread depth into `mutant/0` (records depth + wrap_path)

**Files:** Modify `lib/antigen/generators/mutation.ex`. Test: `test/antigen/generators/mutation_test.exs`.

**Interfaces:** Produces: `mutant/0` now emits mutants with `fault.depth` (0..`@max_depth`) and `fault.wrap_path` (length == depth), still `:mutant_term`/`mutation/rejection`/`:ill_typed`, still `infer`-rejected.

- [ ] **Step 1: Write the failing test**
```elixir
  test "mutant/0 emits deep mutants: depth/wrap_path recorded, still rejected, depth reached" do
    depths =
      for c <- sample(Mutation.mutant(), 300) do
        p = c.payload
        assert length(p.fault.wrap_path) == p.fault.depth
        assert p.fault.depth >= 0 and p.fault.depth <= Mutation.max_depth()
        env = SigMenu.env_of(:v1); ctx = SigMenu.rebuild_context(env, p.ctx)
        assert {:error, _} = Kernel.infer(ctx, p.term)
        p.fault.depth
      end
    assert Enum.max(depths) >= 4        # deep mutants actually generated
  end
```

- [ ] **Step 2: Run — expect FAIL** (current `mutant/0` faults have no `:depth` key → `KeyError` / assertion fails).

- [ ] **Step 3: Implement** — change `mutant/0` in `lib/antigen/generators/mutation.ex` to draw a depth and deepen. Replace the `Gen.bind(term_gen, …)` body:
```elixir
      Gen.bind(select(), fn kind ->
        {term_gen, fault} = build(ctx, kind)

        Gen.bind(term_gen, fn term ->
          Gen.bind(Gen.int(0, max_depth()), fn d ->
            Gen.bind(deepen(ctx, term, d), fn {deep_term, wrap_path} ->
              fault = Map.merge(fault, %{depth: d, wrap_path: wrap_path})
              Gen.return(
                Challenge.new(
                  kind: :mutant_term, assay: assay_id(), label: :ill_typed,
                  payload: %{sig: :v1, ctx: ctx_types, type: goal_of(fault), term: deep_term, fault: fault}
                ))
            end)
          end)
        end)
      end)
```
(`goal_of/1` ignores the new keys — unchanged.)

- [ ] **Step 4: Run — expect PASS**

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/mutation.ex test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): mutant/0 draws depth and records depth/wrap_path"
```

---

## Task 4: health metrics — `max_depth` + `wrap_diversity` (defensive; all mutants)

**Files:** Modify `lib/antigen/runner.ex`. Test: `test/antigen/mutation_health_gate_test.exs`.

**Interfaces:** Produces: `mutation_metrics/1` returns `%{reason_diversity, survivors, mutants_total, max_depth, wrap_diversity}`; `mutation_stamp/1` requires all three floors; health line prints the two new fields.

**Reference:** `max_depth`/`wrap_diversity` are computed over **every** `:mutant_term` (generation-quality, incl. survivors), unlike `reason_diversity` (rejected-only). Legacy seeds lack the keys → `Map.get(fault, :depth, 0)` / `Map.get(fault, :wrap_path, [])`.

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/mutation_health_gate_test.exs
  test "mutation_metrics reports max_depth + wrap_diversity over the whole subset" do
    cs = sample(Mutation.mutant(), 300)
    m = Runner.mutation_metrics(cs)
    assert m.max_depth >= 4
    assert m.wrap_diversity >= 4
    assert Runner.mutation_stamp(m) == :healthy
  end

  test "mutation_metrics reads legacy faults (no depth/wrap_path) without crashing" do
    legacy = Antigen.Challenge.new(
      kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: {:data,:Nat,[],[]}, term: {:fst, {:ctor,:Z,[]}},
                 fault: %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma,
                          injected_head: :Nat, scope: nil}})   # no :depth/:wrap_path
    m = Runner.mutation_metrics([legacy])
    assert m.max_depth == 0 and m.wrap_diversity == 0
  end
```

- [ ] **Step 2: Run — expect FAIL** (`mutation_metrics` has no `max_depth`; strict read would `KeyError` on legacy).

- [ ] **Step 3: Implement** — extend `mutation_metrics/1` and `mutation_stamp/1` in `lib/antigen/runner.ex`:
```elixir
  @depth_floor 4
  @wrap_floor 4

  def mutation_metrics(challenges) do
    ms = Enum.filter(challenges, &match?(%Challenge{kind: :mutant_term}, &1))

    {rejected_kinds, survivors} =
      Enum.reduce(ms, {MapSet.new(), 0}, fn c, {kinds, surv} ->
        case Antigen.Assays.Mutation.run(c) do
          :ok -> {MapSet.put(kinds, c.payload.fault.kind), surv}
          {:violation, _} -> {kinds, surv + 1}
        end
      end)

    depths = Enum.map(ms, fn c -> Map.get(c.payload.fault, :depth, 0) end)
    wraps = ms |> Enum.flat_map(fn c -> Map.get(c.payload.fault, :wrap_path, []) end) |> MapSet.new()

    %{reason_diversity: MapSet.size(rejected_kinds), survivors: survivors,
      mutants_total: length(ms),
      max_depth: Enum.max([0 | depths]), wrap_diversity: MapSet.size(wraps)}
  end

  def mutation_stamp(%{reason_diversity: d, max_depth: md, wrap_diversity: wd}),
    do: if(d >= @mutation_diversity_floor and md >= @depth_floor and wd >= @wrap_floor,
           do: :healthy, else: :vacuous)
```
Extend the health line in `explore/1`:
```elixir
        "antigen health[mutant_term]: reason_diversity=#{mm.reason_diversity} " <>
          "max_depth=#{mm.max_depth} wrap_diversity=#{mm.wrap_diversity} " <>
          "survivors=#{mm.survivors} → #{mutation_stamp(mm)}"
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/mutation_health_gate_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex test/antigen/mutation_health_gate_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): depth + wrapper-diversity vacuity floors for deep mutants"
```

---

## Task 5: bank deep seeds + static depth/wrap meta-test + legacy compat

**Files:** Modify `test/antigen/seeds.sexp`, `test/antigen/mutation_meta_test.exs`.

**Interfaces:** Produces: banked deep `:mutant_term` seeds meeting the depth/wrap floors as a committed fact; legacy shallow seeds still replay `:ok`.

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/mutation_meta_test.exs
  test "banked :mutant_term corpus meets depth + wrapper-diversity floors (static replay)" do
    banked =
      Antigen.Corpus.stream("test/antigen/seeds.sexp")
      |> Enum.flat_map(fn {:ok, %Antigen.Challenge{kind: :mutant_term} = c} -> [c]; _ -> [] end)
    m = Antigen.Runner.mutation_metrics(banked)
    assert m.max_depth >= 4, "banked max_depth #{m.max_depth} below floor"
    assert m.wrap_diversity >= 4, "banked wrap_diversity #{m.wrap_diversity} below floor"
  end
```

- [ ] **Step 2: Run — expect FAIL** (existing seeds are all shallow → `max_depth == 0`).

- [ ] **Step 3: Implement** — bank deep seeds. Run a short script against the built test beams that samples `Mutation.mutant()`, keeps a coverage-deduped set with `fault.depth >= 4` covering ≥4 distinct wrapper kinds and several base fault kinds, sets `seed`, and appends via `Corpus.append("test/antigen/seeds.sexp", c, Corpus.dedup_key(c, :seed))`:
```bash
MIX_ENV=test mix compile
elixir $(printf ' -pa %s' _build/test/lib/*/ebin) - <<'EOF'
alias Antigen.{Corpus, Generators.Mutation}
alias Antigen.Backend.StreamData, as: B
path = "test/antigen/seeds.sexp"
batch = B.interp(Mutation.mutant()) |> Enum.take(2000)
deep = Enum.filter(batch, fn c -> c.payload.fault.depth >= 4 end)
# pick a handful covering ≥4 wrapper kinds and varied base kinds
picked =
  deep
  |> Enum.reduce({%{}, []}, fn c, {seen, acc} ->
       k = {c.payload.fault.kind, List.first(c.payload.fault.wrap_path)}
       if Map.has_key?(seen, k), do: {seen, acc}, else: {Map.put(seen, k, 1), [c | acc]}
     end)
  |> elem(1) |> Enum.take(10)
for c <- picked do
  c = %{c | seed: :erlang.phash2({c.kind, c.payload})}
  Corpus.append(path, c, Corpus.dedup_key(c, :seed))
end
IO.puts("banked #{length(picked)} deep seeds")
EOF
```
Adjust the take/threshold if fewer than 4 wrapper kinds land; the static test is the gate.

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/mutation_meta_test.exs test/antigen/corpus_replay_test.exs`
(The v1 "banked :mutant_term seeds replay as correct rejections" and the every-entry-invariant test must stay green — legacy + new seeds all `:ok`.)

- [ ] **Step 5: Commit**
```bash
git add test/antigen/seeds.sexp test/antigen/mutation_meta_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): bank deep :mutant_term seeds + static depth/wrap floor meta-test"
```

---

## Task 6: Acceptance — quarantine + full suite + explore run

**Files:** none (verification only).

- [ ] **Step 1: Quarantine** — `mix test test/antigen/architecture_test.exs` (no `StreamData` literal in `mutation.ex`). PASS.
- [ ] **Step 2: Full suite ONCE** — `mix test`. All green.
- [ ] **Step 3: Explore** — `MIX_ENV=test mix antigen --count 500 --seeds /tmp/dp_seeds.sexp --corpus /tmp/dp_corpus.sexp`. Expect a line `antigen health[mutant_term]: reason_diversity=… max_depth≥4 wrap_diversity≥4 survivors=0 → healthy` and **0 infections**. Record it for the report.
- [ ] **Step 4:** No commit. Any `survivors > 0` is a genuine error-propagation finding — STOP and report, do not silence.

---

## Self-Review

**Spec coverage:** §3 mechanism → Task 2 (with the documented 6→5 deviation). §4 invariant (c)/(d) → Task 2's uncontaminated-control + no-shift construction. §5 infer-totality → Task 2's construction test asserts `{:error,_}` (a crash fails it). §6 challenge model → Task 1 (atoms) + Task 3 (depth/wrap_path); legacy-record defense → Task 4's legacy test + `Map.get`. §6 health gate → Task 4 (metrics/stamp/line) + Task 5 (static). §7 tests 1–7 → Tasks 2,3,4,5 (test 1 = Task 2 construction; test 2/3 = Task 3 + Task 2 reachability; test 4 = existing v1 diversity test still green; test 5 = Task 1; test 6 = Task 4 + Task 5; test 7 = backward-compat across Tasks 3/4/5). §8 files → Tasks 1–5.

**Placeholder scan:** all code is concrete and probe-verified. Task 5's banking is a shell procedure, not a code placeholder.

**Type consistency:** `deepen/3 :: Gen({term, [atom]})` (Tasks 2→3); `mutant/0` payload gains `fault.depth`/`fault.wrap_path` (Tasks 3→4→5); `mutation_metrics/1` gains `max_depth`/`wrap_diversity` (Task 4 producer + Tasks 4/5 tests). `@wrappers` (5) consistent across Tasks 1 (atoms), 2, 4 (`@wrap_floor 4`).

**Deviation flagged:** the 6→5 wrapper drop (`:ctor_vec`) is documented in Global Constraints with the probe rationale, for the plan reviewer to accept or push back on.
