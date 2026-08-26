# Antigen directed generation — Implementation Plan (Run A)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use `- [ ]` checkboxes.

**Goal:** Make Antigen generation reach deeper/more-diverse shapes without touching the kernel — via an enriched coverage key, corpus-backed fillers, and health-adaptive round-based biasing.

**Architecture:** Three independent, pure-Antigen changes. Part 1 folds new structural signals into `Coverage`'s existing 4-tuple key (arity-preserving). Part 2 adds a `SeedPool` that reuses closed banked `typed_term`s as well-typed fillers. Part 3 restructures `Runner.explore/1` into an opt-in round loop that reweights `default_gen`'s 11-branch mix by challenge-KIND group.

**Tech Stack:** Elixir; `Antigen.{Coverage, Corpus, Runner, Gen}`; `Antigen.Generators.{Term, Mutation, SeedPool}`; `Cure.Core.Term`.

## Global Constraints

- Ghost-authored commits: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- `MIX_ENV=test mix test …`; macOS has no `timeout`; one build/test run at a time.
- **No `Cure.Core.*` (TCB) edits. No `StreamData` literal** in anything under `lib/antigen/generators/` or `assays/` (grep-enforced by `architecture_test.exs`) — `SeedPool` uses `Antigen.Corpus` + `Antigen.Gen` only.
- **`Coverage.key/1` stays a 4-tuple** `{ctors, bucket, flags, label}` — new signals fold into the `flags` `MapSet` (spec §2), so `Runner.coverage_flags/1`'s positional destructure keeps working.
- **`bias: false` (default) must issue exactly one undivided `draw(opts[:gen], count)`** — `Backend.StreamData.interp |> Enum.take` is not composable (spec §4). The round loop runs only under `bias: true`.
- Tests immutable once correct (change impl, not the test; sole exception is a proven-wrong test, stated explicitly).

---

## Task 1: Coverage-vector enrichment (spec §2)

**Files:** Modify `lib/antigen/coverage.ex`; Test `test/antigen/coverage_test.exs`.

**Interfaces:** Produces enriched `flags` (extra atoms `:former_<class>_<0|1|many>`, `:binder_depth_<bucket>`) inside the same 4-tuple; `key_string/1` renders them via the existing `flags` join.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/antigen/coverage_test.exs
  alias Antigen.{Coverage, Challenge}

  defp tt(term), do: Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
                                   payload: %{sig: :v1, ctx: [], type: {:data, :Nat, [], []}, term: term})

  test "coverage key distinguishes terms that collide under the coarse key" do
    # IMPORTANT: `Coverage.constructors/1` (private) does NOT extract literal data-
    # constructor names (`:Z`/`:S`/...) — it folds `tag(node) = elem(node, 0)` over
    # EVERY subterm via the module's existing `fold/3`, so `ctors` is really "the set
    # of Core AST former-tags present anywhere in the term" (`:lam`/`:app`/`:var`/...).
    # A `:lam`-only term and an `:app`-only term therefore ALREADY have different
    # `ctors` sets today (verified directly against `Coverage.key/1`) — they are not
    # a genuine collision. To get a genuine pre-change collision we need two terms
    # built from the exact SAME set of former-tags (only :app/:global/:var here),
    # differing only in the *count* of one former — same ctors, same depth bucket
    # (both fold_depth 1 and 2 bucket to :b0_2), same flags (both trip only
    # `:app_present`, neither has a `:lam`/`:pi`/`:sigma` so `has_shadowing?` is
    # false for both), same label — confirmed by hand-tracing `Coverage.key/1`.
    a = tt({:app, {:global, :plus}, {:var, 0}})                              # one :app
    b = tt({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}})           # two :app
    refute Coverage.key(a) == Coverage.key(b)
    # spec §5 item 1 also expects `key_string/1` to round-trip the new fields —
    # `key_string/1` itself is unchanged (it generically sorts+joins whatever is in
    # the `flags` MapSet), so this is a thin confirmation that the new atoms really
    # do flow through it as plain flags, not a full round-trip parser test.
    assert Coverage.key_string(Coverage.key(b)) =~ "former_app_nm"
  end

  test "enriched key still plateaus (bounded distinct keys over many terms)" do
    terms = for d <- 0..40 do
      Enum.reduce(0..rem(d, 6), {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end)
    end
    keys = terms |> Enum.map(&Coverage.key(tt(&1))) |> Enum.uniq()
    assert length(keys) <= 12, "key space must saturate, got #{length(keys)}"
  end
```

- [ ] **Step 2: Run — expect FAIL** (`mix test test/antigen/coverage_test.exs`) — the first test fails: both terms currently key equal (same `ctors={:data,:app,:global,:var}` — NOT empty, `constructors/1` folds the tag of every subterm, not just `:ctor`-headed nodes — same `:b0_2` depth bucket, same `flags={:app_present}`, same label).

- [ ] **Step 3: Implement** — in `lib/antigen/coverage.ex`, extend `flags/3` to fold in the two signal families, and add the helpers:

```elixir
  defp flags(%Challenge{kind: kind}, terms, ctors) do
    base = for {c, flag} <- @elim_flags, MapSet.member?(ctors, c), into: MapSet.new(), do: flag
    base = if kind in [:def_group, :forcing_pair], do: MapSet.put(base, :has_mutual_group), else: base
    base = if Enum.any?(terms, &has_shadowing?/1), do: MapSet.put(base, :has_shadowing), else: base
    base = MapSet.union(base, former_flags(terms))
    MapSet.put(base, binder_depth_flag(terms))
  end

  @former_classes [:lam, :pi, :app, :case, :ctor, :data, :eq, :rewrite, :prim]
  defp former_flags(terms) do
    # Reuse the module's EXISTING `fold/3` (already used by `constructors/1`/`depth/1`
    # above) rather than hand-rolling a second tuple/list walk — `fold/3` already
    # visits every subterm exactly once via `is_tuple(t)`/`is_list(t)` dispatch, and
    # its callback only ever receives tuple nodes, so plain `tag/1` (also already
    # defined below) is safe to call directly, with no new helper needed.
    counts =
      Enum.reduce(terms, %{}, fn t, acc ->
        fold(t, acc, fn node, a ->
          case tag(node) do
            cls when cls in @former_classes -> Map.update(a, cls, 1, &(&1 + 1))
            _ -> a
          end
        end)
      end)

    for cls <- @former_classes, into: MapSet.new() do
      :"former_#{cls}_#{count_bucket(Map.get(counts, cls, 0))}"
    end
  end

  defp count_bucket(0), do: :n0
  defp count_bucket(1), do: :n1
  defp count_bucket(_), do: :nm

  # binder nesting depth (lam/pi/sigma body, case-branch body increment)
  defp binder_depth_flag(terms) do
    d = terms |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
    :"binder_depth_#{bucket(d)}"
  end

  defp binder_depth({t, _dom, body}) when t in [:lam, :pi, :sigma], do: 1 + binder_depth(body)
  defp binder_depth({:case, s, m, brs}) do
    Enum.max([binder_depth(s), binder_depth(m) |
              Enum.map(brs, fn {_c, ar, b} -> (if ar > 0, do: 1, else: 0) + binder_depth(b) end)])
  end
  defp binder_depth(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
  defp binder_depth(l) when is_list(l), do: l |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
  defp binder_depth(_), do: 0
```

No new tuple/list-walk helper is needed: `former_flags/1` reuses the module's existing `fold/3` + `tag/1` (confirmed present at `lib/antigen/coverage.ex:90-96` and `:87-88`) instead of a hand-rolled `child_terms/1`. `bucket/1` already exists and is reused for the binder-depth bucket. `key_string/1` needs no change (it already sorts+joins the `flags` set).

- [ ] **Step 4: Run — expect PASS.** Also run `mix test test/antigen/coverage_test.exs test/antigen/runner_test.exs` to confirm `Runner.coverage_flags/1`'s positional destructure still holds (arity unchanged).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/coverage.ex test/antigen/coverage_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): enrich coverage key with former-histogram + binder-depth flags"
```

---

## Task 2: SeedPool — corpus-backed fillers (spec §3)

**Files:** Create `lib/antigen/generators/seed_pool.ex`, `test/antigen/generators/seed_pool_test.exs`; Modify `lib/antigen/generators/mutation.ex` (route `gnat` through a pooled branch). Spec §3 says the low-frequency branch may land in `Term.gen_term/2` "and/or" the mutation fillers (`gnat`/`gvec0`/`gvec_sz`) — this run wires only `gnat`; `lib/antigen/generators/term.ex` and the other two mutation fillers are untouched (narrower than the spec's "and/or" ceiling, not a violation of it — no step below edits `term.ex`).

**Interfaces:**
- Produces `SeedPool.load(path) :: %{Term.t() => [Term.t()]}` (type → closed terms), `SeedPool.pool_gen(pool, goal) :: Gen.t() | :none`. **Deviates from spec §3/§5's literal `SeedPool.pool_term(goal)` (single-arg)** — deliberately, not an oversight: the spec's 1-arg framing implicitly requires the loaded pool to live in hidden state (a GenServer, `Process` dictionary, or module-level closure) for `SeedPool` itself to look it up by `goal` alone. Taking `pool` as an explicit argument keeps `SeedPool` a pure, stateless module (`load/1` → data, `pool_gen/2` → data in, `Gen.t()` out) with zero hidden state of its own; the ONE piece of process-scoped state this run introduces (`Process.get(:antigen_seed_pool)`) lives at the `gnat/1` call site instead (Task 2's `mutation.ex` edit below), not inside `SeedPool`. Same behavior, cleaner module boundary — but the implementer must use `pool_gen/2` everywhere below, not `pool_term/1`, despite what the spec prose says.
- Consumes `Antigen.Corpus.stream/1`, `Antigen.Gen.member_of/1` (confirmed present, `lib/antigen/gen.ex:15`), and — for closedness — **`Cure.Core.Term.closed?/1`** (confirmed present, `lib/cure/core/term.ex:158-159`, public, accepts a bare term). `Antigen.Shrink.closed?/1` was considered but does NOT accept a bare term — it takes a whole `%Challenge{payload: p}` and closed-checks `term`/`type`/`ctx` together (`lib/antigen/shrink.ex:212`), the wrong shape here. `Cure.Core.Term.closed?/1` is the kernel's own trusted implementation (kept in lockstep with `shift/3`/`subst/3` per its own doc comment) — reuse it directly rather than hand-rolling a third de-Bruijn walk; this is a read-only call into the TCB's public API (the same pattern `Antigen.Generators.Term` already uses for `Term.gen_term`/`Term.term?` throughout), not a TCB edit.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/seed_pool_test.exs
defmodule Antigen.Generators.SeedPoolTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SeedPool
  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.Term

  @tmp "tmp/seedpool_test"
  setup do
    File.rm_rf!(@tmp); File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp bank(path, c), do: Corpus.append(path, c, Corpus.dedup_key(c, :antibody))

  test "pool indexes only closed typed_term seeds, keyed by recorded type" do
    path = Path.join(@tmp, "seeds.sexp")
    nat = {:data, :Nat, [], []}
    bank(path, Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
      payload: %{sig: :v1, ctx: [], type: nat, term: {:ctor, :S, [{:ctor, :Z, []}]}}))
    # a mutant with a nominal type MUST NOT enter the pool
    bank(path, Challenge.new(kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: nat, term: {:fst, {:ctor, :Z, []}}, fault: %{kind: :proj_non_pair}}))

    pool = SeedPool.load(path)
    assert [{:ctor, :S, [{:ctor, :Z, []}]}] = Map.get(pool, nat)
    # `Antigen.Gen` (lib/antigen/gen.ex) has NO `defstruct` — it is a plain tagged-tuple
    # type (`{:member_of, xs}`, `{:frequency, ws}`, ...), so `%Antigen.Gen{}` is not a
    # valid struct pattern (it would not compile: `Antigen.Gen.__struct__/0 is undefined`).
    assert is_tuple(SeedPool.pool_gen(pool, nat))
    assert SeedPool.pool_gen(pool, {:data, :Vec, [], [{:ctor, :Z, []}]}) == :none
    assert Enum.all?(Map.get(pool, nat), &Term.term?/1)
  end

  test "absent file yields an empty pool and :none for every goal" do
    pool = SeedPool.load(Path.join(@tmp, "missing.sexp"))
    assert pool == %{}
    assert SeedPool.pool_gen(pool, {:data, :Nat, [], []}) == :none
  end

  test "an open typed_term (empty ctx, free de-Bruijn var) is excluded from the pool" do
    # Both fixtures in the first test above are already closed (or excluded by
    # KIND), so neither exercises the CLOSEDNESS filter itself (spec §3's other
    # soundness leg, "empty-context, de-Bruijn-closed"). `ctx: []` alone is not
    # sufficient — a term can still carry a free de-Bruijn index despite an empty
    # context (e.g. a malformed/adversarial corpus entry); this must also be
    # excluded, since a spliced free variable would be unbound at any use site.
    path = Path.join(@tmp, "seeds_open.sexp")
    nat = {:data, :Nat, [], []}
    bank(path, Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
      payload: %{sig: :v1, ctx: [], type: nat, term: {:var, 0}}))

    pool = SeedPool.load(path)
    assert pool == %{}
  end
end
```

- [ ] **Step 2: Run — expect FAIL** — `SeedPool` undefined.

- [ ] **Step 3: Implement** — `lib/antigen/generators/seed_pool.ex`:

```elixir
defmodule Antigen.Generators.SeedPool do
  @moduledoc """
  Corpus-backed fillers (spec §3): reuse *closed* banked `:typed_term` seeds as
  well-typed fillers, indexed by their kernel-checked recorded type. Only
  `:typed_term` seeds qualify — a `:mutant_term`'s `type` is a nominal fault-site
  goal its term does NOT actually inhabit. Backend-free (no StreamData literal).
  """
  alias Antigen.{Corpus, Gen}
  alias Cure.Core.Term

  @spec load(String.t()) :: %{Term.t() => [Term.t()]}
  def load(path) do
    Corpus.stream(path)
    |> Enum.flat_map(fn
      {:ok, %{kind: :typed_term, payload: %{ctx: [], type: type, term: term}}} ->
        if Term.closed?(term), do: [{type, term}], else: []
      _ -> []
    end)
    |> Enum.group_by(fn {type, _} -> type end, fn {_, term} -> term end)
  end

  @spec pool_gen(%{Term.t() => [Term.t()]}, Term.t()) :: Gen.t() | :none
  def pool_gen(pool, goal) do
    case Map.get(pool, goal) do
      nil -> :none
      [] -> :none
      terms -> Gen.member_of(terms)
    end
  end
end
```

Then wire a low-frequency pool branch into the Nat filler in `lib/antigen/generators/mutation.ex`. Change `gnat/1` to consult a process-scoped pool if one is installed (kept opt-in so existing tests are unaffected when no pool is set):

```elixir
  # gnat: well-typed Nat filler; occasionally a banked closed Nat (if a pool is installed)
  defp gnat(ctx) do
    fresh = Term.gen_term(ctx, nat_t())
    case Process.get(:antigen_seed_pool) do
      %{} = pool ->
        case Antigen.Generators.SeedPool.pool_gen(pool, nat_t()) do
          :none -> fresh
          g -> Gen.frequency([{4, fresh}, {1, g}])
        end
      _ -> fresh
    end
  end
```

`Mix.Tasks.Antigen` installs the pool once before exploring (`Process.put(:antigen_seed_pool, SeedPool.load(seeds_path))`) — added in Task 3's CLI edit. When no pool is installed (all existing tests), `gnat` is byte-identical to today.

- [ ] **Step 4: Run — expect PASS** (`mix test test/antigen/generators/seed_pool_test.exs test/antigen/generators/mutation_test.exs test/antigen/architecture_test.exs`) — SeedPool tests green, mutation tests still green (no pool installed), quarantine green.

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/seed_pool.ex lib/antigen/generators/mutation.ex test/antigen/generators/seed_pool_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): SeedPool — reuse closed banked typed_terms as fillers (opt-in)"
```

---

## Task 3: Health-adaptive round loop + guard test (spec §4)

**Files:** Modify `lib/antigen/runner.ex` (round loop, `bias:` opt), `lib/mix/tasks/antigen.ex` (`--bias` flag, pool install); Test `test/antigen/runner_test.exs`.

**Interfaces:**
- Produces `Runner.explore(opts)` accepting `bias: boolean` (default `false`) and `round_size: pos_integer` (default 200); `bias: false` ⇒ one undivided `draw`. Reweighting operates at group granularity (T = default_gen branches 4–6,9–11; M = 7–8; F = 1–3 fixed).
- Consumes `default_gen/0`'s literal 11-branch order (position→group table pinned by a guard test).

- [ ] **Step 1: Write the failing tests**

```elixir
# append to test/antigen/runner_test.exs — `runner_test.exs` has no `tmp/1` helper
# today (its existing tests use `@tmp` + `Path.join/2` inline); add one so the new
# tests below can name per-test paths without colliding:
  defp tmp(name), do: Path.join(@tmp, name)

  test "explore(challenges: ...) bypasses the generator entirely (existing override path)" do
    # NOTE: this is a regression guard for the pre-existing `opts[:challenges] ||
    # draw(...)` override, NOT a test of the `bias:false` single-draw invariant —
    # passing `challenges:` takes the FIRST `cond` branch and never reaches `draw`
    # or `opts[:bias]` at all, so it already passes unmodified today. Kept because
    # the restructured `explore/1` head must still preserve this exact behavior.
    cs = [Antigen.Challenge.stub({:type, 0})]
    r = Antigen.Runner.explore(challenges: cs, count: 1, corpus_path: tmp("c.sexp"),
                               seeds_path: tmp("s.sexp"), report_dir: tmp("r"))
    assert r.seeds_banked + r.infections + r.discards == 1
  end

  test "explore(bias: false) draws via `gen` (no challenges override) and processes exactly `count`" do
    # This is the test that actually exercises spec §4's `bias:false` invariant path
    # (the `true -> draw(opts[:gen], count)` branch) — the test above never reaches
    # it. Proving "exactly ONE `Backend.StreamData.interp/1` call" at the object
    # level isn't practically assertable through the public interface (`draw/2` is
    # private and StreamData streams aren't introspectable for call-count without
    # instrumenting the backend itself) — spec §4's non-composability findings were
    # established by direct experimentation, not a unit-testable invariant. What IS
    # asserted here: `bias:false` reaches `draw(opts[:gen], count)` and returns all
    # `count` results from a single logical batch (not re-batched into `round_size`
    # chunks). The "single call" guarantee itself is structural: `explore/1`'s
    # `true ->` branch must stay textually `draw(opts[:gen], count)`, unchanged from
    # today — reviewed at Step 3, not re-derived by a test.
    # `Generators.Stub.gen()` only emits 5 distinct payloads (weight-1 `:boom`,
    # weight-9 uniform over `{:var, 0..3}`), so `seeds_banked + infections` is NOT
    # `count` in general — duplicate seeds (already covered by the existing dedup
    # test above) contribute 0 to `seeds_banked` without incrementing `discards`
    # either. `count: 300` (matching the file's existing `Generators.Stub.gen()`
    # tests above, same rationale) makes the 1-in-10 `:boom` branch land with
    # overwhelming probability (P(never) = 0.9^300 ≈ 10^-14), so this mirrors the
    # already-established, non-flaky assertion pattern rather than inventing a new
    # exact-sum invariant.
    opts = [gen: Generators.Stub.gen(), assay: Assays.Stub, bias: false, count: 300,
            corpus_path: tmp("c3.sexp"), seeds_path: tmp("s3.sexp"), report_dir: tmp("r3")]
    r = Antigen.Runner.explore(opts)
    assert r.infections >= 1
  end

  test "default_gen has exactly 11 branches in the documented group order (guard)" do
    {:frequency, ws} = Mix.Tasks.Antigen.default_gen()
    assert length(ws) == 11
    # groups by challenge kind of a sampled draw are stable at the pinned positions
    assert Antigen.Runner.gen_group_table() ==
             %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
  end

  test "bias:true bumps the vacuous group's total weight, floors hold, Group F unchanged" do
    base = %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
    w0 = List.duplicate(1, 11)
    w_t = Antigen.Runner.reweight(w0, base, %{health_stamp: :vacuous, mutation_stamp: :healthy,
                                              conv_reject_count: 5, conv_accept_count: 5})
    # Group T positions rose, Group F unchanged, nothing dropped to 0
    assert Enum.all?(base.t, fn i -> Enum.at(w_t, i - 1) > 1 end)
    assert Enum.all?(base.f, fn i -> Enum.at(w_t, i - 1) == 1 end)
    assert Enum.all?(w_t, &(&1 >= 1))
  end

  test "explore(bias: true) runs the round loop end-to-end through the real default_gen mix" do
    # No other test drives `bias: true` through `explore/1` itself — `reweight/3`
    # above is a pure-function unit test; this is the integration test that
    # exercises `draw_biased/3` (round-splitting, per-round stamping, gen rebuild)
    # against the real `Mix.Tasks.Antigen.default_gen/0` `{:frequency, ws}` shape
    # `bias: true` requires (see Step 3's precondition note). `count: 12,
    # round_size: 5` forces 3 rounds (5 + 5 + 2) — small enough to stay fast while
    # still exercising a mid-batch reweight.
    opts = [gen: Mix.Tasks.Antigen.default_gen(), bias: true, count: 12, round_size: 5,
            corpus_path: tmp("c5.sexp"), seeds_path: tmp("s5.sexp"), report_dir: tmp("r5")]
    r = Antigen.Runner.explore(opts)
    assert %{infections: _, seeds_banked: _, health: _, health_metrics: _, stamp: _} = r
  end
```

- [ ] **Step 2: Run — expect FAIL** — `gen_group_table/0`/`reweight/3`/`draw_biased/3` undefined (the `bias: true` end-to-end test crashes with `UndefinedFunctionError`); the two `bias: false`-related tests above already pass unmodified (they are behavior-preservation regression guards, not novel-behavior red tests — `bias:false`'s whole point is to be a no-op relative to today).

- [ ] **Step 3: Implement** — in `lib/antigen/runner.ex`:

```elixir
  @round_size 200
  @group_table %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
  def gen_group_table, do: @group_table

  # bump every position in the low-health group(s); floor 1; Group F never bumped.
  def reweight(weights, table \\ @group_table, stamps) do
    bumps =
      []
      |> maybe_bump(table.t, stamps[:health_stamp] == :vacuous or stamps[:conv_accept_count] == 0)
      |> maybe_bump(table.m, stamps[:mutation_stamp] == :vacuous or stamps[:conv_reject_count] == 0)

    weights
    |> Enum.with_index(1)
    |> Enum.map(fn {w, i} -> if i in bumps, do: w + 2, else: max(w, 1) end)
  end

  defp maybe_bump(acc, _positions, false), do: acc
  defp maybe_bump(acc, positions, true), do: acc ++ positions
```

Restructure `explore/1`'s head so `bias: true` runs rounds and `bias: false` keeps the single draw:

```elixir
  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    challenges =
      cond do
        opts[:challenges] -> opts[:challenges]
        opts[:bias] -> draw_biased(opts[:gen], count, Keyword.get(opts, :round_size, @round_size))
        true -> draw(opts[:gen], count)     # exactly one undivided draw (spec §4)
      end
    # … existing reduce body unchanged …
```

`draw_biased/3`, given verbatim (verified to compile and run — hand-run against stand-ins for `reweight/3`/`health_metrics/1`/`mutation_metrics/1`/`conversion_metrics/1`/`draw/2`, at the exact `count: 12, round_size: 5` this task's integration test below uses: confirmed 12 items out across 3 rounds of `5+5+2`, and separately confirmed the `round_size: 0` floor below prevents the hang a naive version has):

```elixir
  # `bias: true`'s documented precondition: `gen` must be the reweightable
  # `{:frequency, ws}` shape (`Mix.Tasks.Antigen.default_gen/0`'s 11 branches) —
  # NOT an arbitrary `Antigen.Gen.t()`. A caller combining `bias: true` with e.g.
  # `Generators.Stub.gen()` (a bare `{:frequency, [...]}` of a DIFFERENT branch
  # count/order, or any non-`:frequency` gen) will hit this `{:frequency, ws0} =
  # gen` match and crash with a clear MatchError rather than silently misbehaving —
  # `bias: true` is a `mix antigen`-CLI-only feature in this run (§7 non-goals);
  # ad-hoc callers (existing `runner_test.exs` fixtures) must stay on `bias: false`.
  defp draw_biased(gen, count, round_size) do
    {:frequency, ws0} = gen
    # `round_size <= 0` would make `n = min(round_size, remaining)` non-positive in
    # `draw_rounds/4` below, so `remaining - n` never decreases — an infinite loop
    # (confirmed by direct probe: `round_size: 0` hangs). `opts[:round_size]` is
    # caller-suppliable (no CLI switch validates it), so floor it here rather than
    # trust every call site.
    draw_rounds(ws0, count, max(round_size, 1), [])
  end

  defp draw_rounds(_ws, 0, _round_size, acc), do: acc |> Enum.reverse() |> List.flatten()

  defp draw_rounds(ws, remaining, round_size, acc) do
    n = min(round_size, remaining)
    batch = draw({:frequency, ws}, n)
    stamps = round_stamps(List.flatten([batch | acc]))
    new_weights = reweight(Enum.map(ws, fn {w, _g} -> w end), gen_group_table(), stamps)
    ws2 = Enum.zip(new_weights, ws) |> Enum.map(fn {w, {_old_w, g}} -> {w, g} end)
    draw_rounds(ws2, remaining - n, round_size, [batch | acc])
  end

  # `discard_rate` isn't knowable during the draw phase (discards are only decided
  # later, in `explore/1`'s reduce body, by `well_formed?/1`) — pass 0.0 so the
  # health stamp used for mid-run biasing is driven by binder_usage/reduction_activity
  # only; the run's real discard-rate is still reported at the end, unaffected.
  defp round_stamps(challenges) do
    %{
      health_stamp: health_stamp(health_metrics(challenges), 0.0),
      mutation_stamp: mutation_stamp(mutation_metrics(challenges)),
      conv_reject_count: conversion_metrics(challenges).conv_reject_count,
      conv_accept_count: conversion_metrics(challenges).conv_accept_count
    }
  end
```

`draw_rounds/4` accumulates each round's batch (prepended, so the terminal clause reverses before flattening — chronological order is preserved in the final challenge list even though `round_stamps` sees rounds in an arbitrary order, which is harmless since none of `health_metrics`/`mutation_metrics`/`conversion_metrics` are order-sensitive). It does NOT re-draw the same gen across rounds; each round is a fresh `draw` of a freshly-reweighted gen, which is the intended adaptive behavior — the non-composability constraint only forbids splitting a *single logical* uniform draw, which is the `bias:false` path (unaffected by this function).

In `lib/mix/tasks/antigen.ex`: add `bias: :boolean` to `@switches` (so `OptionParser.parse(argv, strict: @switches)` recognizes `--bias` instead of rejecting it), pass `bias: opts[:bias]` into the `runner_opts` keyword list, and install the pool **before the `case mode do` dispatch** (so both `mix antigen` and `mix antigen generate` share the same pooled `gnat`, since both run the same underlying generator stack — `default_gen()` feeds both `Runner.explore/1` and `Runner.generate/1`):

```elixir
    runner_opts = [
      gen: default_gen(),
      corpus_path: opts[:corpus] || "test/antigen/corpus.sexp",
      seeds_path: opts[:seeds] || "test/antigen/seeds.sexp",
      report_dir: opts[:report_dir] || "tmp/antigen",
      count: count,
      bias: opts[:bias]
    ]

    if seeds_path = opts[:seeds] || "test/antigen/seeds.sexp",
       do: Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(seeds_path))

    case mode do
      # … unchanged …
```

and note in `@moduledoc` that `--bias` needs `--count` above the 200 round size to have any effect.

**On testing this CLI wiring directly:** a `capture_io`-around-`Mix.Tasks.Antigen.run(["--bias", ...])` test was considered and REJECTED after direct verification — `OptionParser.parse(argv, strict: @switches)` does NOT raise on an unrecognized `--bias`; it silently routes it into the discarded `invalid` list (confirmed directly: `OptionParser.parse(["--bias"], strict: [count: :integer])` returns `{[], [], [{"--bias", nil}]}`, no exception), and `Mix.Tasks.Antigen.run/1` discards that third element (`{opts, rest, _}`). So `mix antigen --bias ...` prints the exact same `"antigen: N infection(s), M seed(s) banked"` output whether or not `:bias` is in `@switches` — a stdout-only test cannot distinguish "wired through" from "silently dropped," so it would already pass today and would not be red. Rather than ship another test that looks like it proves something it doesn't (the same defect this review already found and fixed once in the `bias:false` test above), this thin, mechanical pass-through (`@switches` literal + `bias: opts[:bias]` in a keyword list) is left to the REAL behavioral coverage that already exists one layer down: the `explore(bias: true, ...)` end-to-end integration test (Task 3 Step 1, last test) exercises the identical `bias: true` code path `Runner.explore/1` receives from the CLI, and Stage 5's `mix antigen --count 800 --bias` manual sanity run (§5 item 5) exercises the full CLI path once end-to-end, recording health-line deltas. A future run that wants CLI-layer unit coverage would need a test-only introspection hook (e.g. a public `parse_switches/1`) — out of scope here.

- [ ] **Step 4: Run — expect PASS** (`mix test test/antigen/runner_test.exs`).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex lib/mix/tasks/antigen.ex test/antigen/runner_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): health-adaptive round loop (opt-in --bias) + default_gen group guard"
```

---

## Self-Review

**Spec coverage:** §2 enrichment → Task 1 (arity-preserving flags, plateau test). §3 SeedPool → Task 2 (typed_term-only, closed-only, absent-file inert, quarantine). §4 rounds → Task 3 (bias:false one-draw; group reweight; Group-F-fixed; guard test; --bias doc). §5 tests → Tasks 1–3 + Stage-5 sanity. §6 files match. §7 non-goals respected (no TCB; closed-only; syntactic type-eq; no format change).

**Placeholder scan:** none — every step has concrete code, including `draw_biased/3` (previously prose-only, now given verbatim and compile-checked in Task 3).

**Type consistency:** `SeedPool.{load,pool_gen}` defined Task 2 (closedness delegates to the existing `Cure.Core.Term.closed?/1`, not a local reimplementation), consumed by `gnat` (Task 2) + CLI (Task 3). `Runner.{gen_group_table,reweight,draw_biased,draw_rounds,round_stamps}` defined Task 3. `@group_table` positions match `default_gen/0`'s committed 11-branch order (Totality/Positivity/Forcing = 1–3; typed_term×3 = 4–6; mutant = 7; conv_reject = 8; conv_accept×3 = 9–11) — pinned by the guard test.

**Ordering:** Task 1 (coverage) independent. Task 2 (SeedPool) before Task 3 (CLI installs the pool). Stage 5 runs the full suite once + `mix antigen --count 800 --bias` to a tmp corpus, recording health-line deltas vs baseline.
