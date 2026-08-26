# Antigen conversion-at-depth — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Test the kernel's conversion/NbE checker at depth by placing the discriminating difference in a `Vec` **index behind a `plus` redex** — reject carriers (must `infer`-REJECT, in the mutation corpus) and accept carriers (must be ACCEPTED by all three `term/*` assays, in the typed-term corpus).

**Architecture:** New backend-free generator `Antigen.Generators.Conversion` emitting both `:mutant_term` (reject) and `:typed_term` (accept) challenges over 2 carriers (`:conv_index`, `:conv_motive`). Reuses `Assays.Mutation` and `Assays.Term` **unchanged**; no new assay, no `Cure.Core.Term` seam (carriers are closed, binder-free).

**Tech Stack:** Elixir; `Antigen.Gen` DSL (StreamData-free in generators/assays); `Cure.Core.Kernel.infer/2`; `Antigen.Assays.{Mutation,Term}`.

## Global Constraints

- **Construction-guaranteed typedness (LOCKED, both polarities):** reject = distinct closed numerals `a+b` vs `a+b+1` (non-convertible, decided in Elixir); accept = equal closed numerals (convertible). Never ask the kernel-under-test to decide typedness.
- **StreamData quarantine:** nothing under `lib/antigen/generators/` or `lib/antigen/assays/` may contain the literal `StreamData` (grep-enforced by `architecture_test.exs` — has bitten this project three times, incl. a moduledoc).
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- **One full build/test run at a time** (a past concurrent full-suite run caused a kernel panic).
- **Tests are immutable once green:** a Step-1 red test, once passing, is only made green by changing the implementation — never weakened/skipped/deleted, except a test proven to encode wrong behavior (state why in the commit before touching it).
- **Draw order for uniformity (spec §3):** draw `conv_depth` uniformly in `0..@max_depth` **first**, then `a` in `0..conv_depth`, `b = conv_depth - a`. Independent-uniform `a,b` would sum to a triangular distribution and reintroduce the flakiness A's spec solved.
- **Empty context:** conversion carriers are **closed** terms; the payload `ctx` is `[]` (no `CtxGen` draw needed — context adds nothing to a closed term and keeps dedup keyed on the term).

### Verified carrier set (probed against the live kernel, `conv_depth` 0–6)

`num(k) = Sᵏ Z`, `vec_of(k) : Vec (Sᵏ Z)` = `k==0 → vnil`, else `vcons(num(k-1), Z, vec_of(k-1))`. `d = a+b`.

| carrier | term (reject uses filler `vec_of(d+1)`, accept `vec_of(d)`) | reject `infer` / accept `infer` |
|---|---|---|
| `:conv_index` | `{:ctor, :vcons, [plus(num(a),num(b)), Z, filler]}` | `:error` / `:ok` |
| `:conv_motive` | `{:case, {:ctor,:T,[]}, {:lam, Bd, Vec(plus(num(a),num(b)))}, [{:T,0,filler},{:F,0,filler}]}` | `:error` / `:ok` |

Probe (d∈{1,6}, both carriers): reject → `infer` `:error` **and** `Assays.Mutation.run` `:ok`; accept → `infer` `:ok` **and** all of `term/infer_check`, `term/subject_reduction`, `term/normalization` `:ok`. Accept claimed `type`: `:conv_index → Vec (num(d+1))`, `:conv_motive → Vec (num(d))`. Reject `:mutant_term` `type` (documentation-only, must be a well-formed menu term): `Vec (num(d))` (the site's reduced-expected-index type, mirroring `Mutation.goal_of/1`).

---

## File Structure

- **Create** `lib/antigen/generators/conversion.ex` — carriers, `vec_of/1`, `num/1`, depth-split draw, `conv_reject/0`, `conv_accept/1`, `carriers/0`, `max_depth/0`.
- **Modify** `lib/antigen/challenge.ex` — `@known_atoms` += the 8 conversion atoms.
- **Modify** `lib/antigen/runner.ex` — `conversion_metrics/1` (`conv_carrier_diversity`, `conv_both_polarities`), `conv_carrier_of/1` (structural accept detector), + health line.
- **Modify** `lib/mix/tasks/antigen.ex` — `default_gen` += `conv_reject` (×1) and `conv_accept` (×3, one per `term/*` assay).
- **Modify** `test/antigen/seeds.sexp` — bank reject + accept conversion seeds.
- **Create** `test/antigen/generators/conversion_test.exs`; **Extend** `test/antigen/challenge_test.exs`, `test/antigen/mutation_meta_test.exs`.

---

## Task 1: intern conversion atoms (genuine file-decode red)

**Files:** Modify `lib/antigen/challenge.ex`. Test: `test/antigen/challenge_test.exs`.

**Interfaces:** Produces: a `:conv_*` fault map survives `binary_to_term [:safe]` decode.

- [ ] **Step 1: Generate an out-of-source blob** (atoms live only in bytes, so the red genuinely depends on `@known_atoms` — the in-source round-trip is false-green, per the A Task-1 / v1 key-atom lesson):
```bash
cat > /tmp/mkconvblob.exs <<'EOF'
fault = %{kind: :conv_index, witness: :conv, expected_index: 3, actual_index: 4,
          reduction: :required, depth: 3, carrier: :conv_index}
IO.puts(Base.encode64(:erlang.term_to_binary(fault)))
EOF
elixir $(printf ' -pa %s' _build/test/lib/*/ebin) /tmp/mkconvblob.exs | tail -1
```

- [ ] **Step 2: Write the failing test** (paste the printed base64 into `@conv_fault_blob`; the test source must NOT name `:conv_index`/`:conv`/`:expected_index`/etc. as literals):
```elixir
# append inside test/antigen/challenge_test.exs, before the final `end`
  @conv_fault_blob "<<PASTE_BASE64_FROM_STEP_1>>"
  test "conversion fault atoms are interned for [:safe] file decode" do
    _ = Antigen.Challenge.__known_atoms__()
    decoded = :erlang.binary_to_term(Base.decode64!(@conv_fault_blob), [:safe])
    assert is_map(decoded) and map_size(decoded) == 7
  end
```

- [ ] **Step 3: Run — expect FAIL** `mix test test/antigen/challenge_test.exs`
Expected: `binary_to_term`/`:safe` raises `ArgumentError` (unsafe external representation) on the uninterned `:conv_index`/`:conv`/`:expected_index`/`:actual_index`/`:reduction`/`:required`/`:carrier` atoms.

- [ ] **Step 4: Implement** — in `lib/antigen/challenge.ex`, extend `@known_atoms` (after the deep-propagation block):
```elixir
    # conversion-at-depth: carrier kinds + witness + field keys/values
    :conv_index, :conv_motive, :conv, :expected_index, :actual_index,
    :reduction, :required, :carrier
```

- [ ] **Step 5: Run — expect PASS** `mix test test/antigen/challenge_test.exs`

- [ ] **Step 6: Commit**
```bash
git add lib/antigen/challenge.ex test/antigen/challenge_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): intern conversion-at-depth fault atoms"
```

---

## Task 2: `Conversion` reject carriers (`conv_reject/0` → `:mutant_term`)

**Files:** Create `lib/antigen/generators/conversion.ex`. Test: create `test/antigen/generators/conversion_test.exs`.

**Interfaces:**
- Produces: `Conversion.carriers/0 :: [:conv_index, :conv_motive]`; `Conversion.max_depth/0`; `Conversion.conv_reject/0 :: Gen.t()` emitting `:mutant_term` (assay `mutation/rejection`, label `:ill_typed`) with `fault` carrying `kind/witness/expected_index/actual_index/reduction/depth/carrier`.
- Consumes (later): `conv_reject/0`, `carriers/0`, `max_depth/0`.

- [ ] **Step 1: Write the failing test**
```elixir
defmodule Antigen.Generators.ConversionTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Conversion, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "conv_reject: every carrier at a range of depths infer-REJECTS, with kernel-free witness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    depths =
      for c <- sample(Conversion.conv_reject(), 300) do
        p = c.payload
        assert %Antigen.Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed} = c
        f = p.fault
        assert f.carrier in Conversion.carriers()
        assert f.witness == :conv and f.reduction == :required
        assert f.actual_index == f.expected_index + 1     # kernel-free non-convertibility witness
        assert f.depth == f.expected_index
        # the discriminating index position is a plus REDEX, not a numeral (conversion-at-depth)
        assert redex?(f.carrier, p.term)
        assert {:error, _} = Kernel.infer(ctx, p.term)     # construction guarantee (+ totality)
        f.depth
      end

    assert Enum.member?(depths, 0) and Enum.max(depths) >= 4   # depth reached; d=0 exercised
    assert length(Enum.uniq(depths)) >= 3
  end

  defp redex?(:conv_index, {:ctor, :vcons, [n, _, _]}), do: is_plus(n)
  defp redex?(:conv_motive, {:case, _, {:lam, _, {:data, :Vec, _, [idx]}}, _}), do: is_plus(idx)
  defp is_plus({:app, {:app, {:global, :plus}, _}, _}), do: true
  defp is_plus(_), do: false
end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/generators/conversion_test.exs`
Expected: `Antigen.Generators.Conversion` undefined.

- [ ] **Step 3: Implement** — create `lib/antigen/generators/conversion.ex`:
```elixir
defmodule Antigen.Generators.Conversion do
  @moduledoc """
  Conversion-at-depth carriers (spec B). The discriminating difference sits in a
  `Vec` index behind a `plus` redex, so the kernel must REDUCE to decide. Reject
  carriers (mismatched filler) → `:mutant_term`; accept carriers (matched filler) →
  `:typed_term`. Backend-free: built only via the `Antigen.Gen` DSL.
  """
  alias Antigen.Challenge
  alias Antigen.Gen

  @carriers [:conv_index, :conv_motive]
  def carriers, do: @carriers
  @max_depth 6
  def max_depth, do: @max_depth

  # menu term helpers (closed literals)
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp num(0), do: z()
  defp num(k) when k > 0, do: s(num(k - 1))
  defp vnil, do: {:ctor, :vnil, []}
  defp vec(i), do: {:data, :Vec, [], [i]}
  defp bd, do: {:data, :Bd, [], []}
  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}

  # closed Vec (S^k Z)
  defp vec_of(0), do: vnil()
  defp vec_of(k) when k > 0, do: {:ctor, :vcons, [num(k - 1), z(), vec_of(k - 1)]}

  # carrier term with filler of S-depth `fd` at the hole
  def carrier_term(:conv_index, a, b, fd),
    do: {:ctor, :vcons, [plus(num(a), num(b)), z(), vec_of(fd)]}

  def carrier_term(:conv_motive, a, b, fd),
    do:
      {:case, {:ctor, :T, []}, {:lam, bd(), vec(plus(num(a), num(b)))},
       [{:T, 0, vec_of(fd)}, {:F, 0, vec_of(fd)}]}

  # accept: whole-term type when the filler matches
  def accept_type(:conv_index, d), do: vec(num(d + 1))
  def accept_type(:conv_motive, d), do: vec(num(d))

  # draw conv_depth uniformly FIRST, then split into a+b (spec §3)
  defp depth_split do
    Gen.bind(Gen.int(0, @max_depth), fn d ->
      Gen.bind(Gen.int(0, d), fn a -> Gen.return({d, a, d - a}) end)
    end)
  end

  defp carrier_gen, do: Gen.frequency(Enum.map(@carriers, fn c -> {1, Gen.return(c)} end))

  # Carriers are closed, binder-free terms (spec §4) — no env/context is needed
  # to construct them; the assays independently rebuild their own env from the
  # payload's `sig: :v1` field when they run.
  @spec conv_reject() :: Gen.t()
  def conv_reject do
    Gen.bind(carrier_gen(), fn carrier ->
      Gen.bind(depth_split(), fn {d, a, b} ->
        term = carrier_term(carrier, a, b, d + 1)   # filler one deeper ⇒ mismatch

        fault = %{
          kind: carrier, witness: :conv, expected_index: d, actual_index: d + 1,
          reduction: :required, depth: d, carrier: carrier
        }

        Gen.return(
          Challenge.new(
            kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
            payload: %{sig: :v1, ctx: [], type: vec(num(d)), term: term, fault: fault}
          )
        )
      end)
    end)
  end
end
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/generators/conversion_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/conversion.ex test/antigen/generators/conversion_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): conversion reject carriers (redex-carried index, must infer-reject)"
```

---

## Task 3: accept carriers (`conv_accept/1` → `:typed_term`)

**Files:** Modify `lib/antigen/generators/conversion.ex`, `test/antigen/generators/conversion_test.exs`.

**Interfaces:** Produces: `Conversion.conv_accept(assay) :: Gen.t()` emitting `:typed_term` (label `:well_typed`, given assay) whose term is accepted by every `term/*` assay; the same shape with the reject filler is `infer`-REJECTED (control).

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/generators/conversion_test.exs (before final end)
  test "conv_accept: every carrier at a range of depths is ACCEPTED by all term/* assays" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    assays = ["term/infer_check", "term/subject_reduction", "term/normalization"]

    depths =
      for assay <- assays, c <- sample(Conversion.conv_accept(assay), 60) do
        assert %Antigen.Challenge{kind: :typed_term, label: :well_typed} = c
        assert {:ok, _} = Kernel.infer(ctx, c.payload.term)
        assert Antigen.Assays.Term.run(c) == :ok        # reduces to accept
        # accept term also carries a plus redex at its index (reduction-required)
        assert redex?(detect(c.payload.term), c.payload.term)
        idx_depth(c.payload.term)
      end

    assert Enum.max(depths) >= 4
  end

  test "control: an accept shape with the REJECT filler is infer-rejected (accept is not vacuous)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    # conv_index at d=2: matched filler accepts, one-deeper filler rejects
    ok = Conversion.carrier_term(:conv_index, 1, 1, 2)
    bad = Conversion.carrier_term(:conv_index, 1, 1, 3)
    assert {:ok, _} = Kernel.infer(ctx, ok)
    assert {:error, _} = Kernel.infer(ctx, bad)
  end

  defp detect({:ctor, :vcons, _}), do: :conv_index
  defp detect({:case, _, _, _}), do: :conv_motive
  defp idx_depth({:ctor, :vcons, [{:app,{:app,{:global,:plus},a},b}, _, _]}), do: nat(a) + nat(b)
  defp idx_depth({:case, _, {:lam, _, {:data, :Vec, _, [{:app,{:app,{:global,:plus},a},b}]}}, _}),
    do: nat(a) + nat(b)
  defp nat({:ctor, :Z, []}), do: 0
  defp nat({:ctor, :S, [n]}), do: 1 + nat(n)
```

- [ ] **Step 2: Run — expect FAIL** (`Conversion.conv_accept/1`, `carrier_term/4` may be private) `mix test test/antigen/generators/conversion_test.exs`

- [ ] **Step 3: Implement** — add to `lib/antigen/generators/conversion.ex`:
```elixir
  @spec conv_accept(String.t()) :: Gen.t()
  def conv_accept(assay) do
    Gen.bind(carrier_gen(), fn carrier ->
      Gen.bind(depth_split(), fn {d, a, b} ->
        term = carrier_term(carrier, a, b, d)   # filler matches reduced index ⇒ accept

        Gen.return(
          Challenge.new(
            kind: :typed_term, assay: assay, label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: accept_type(carrier, d), term: term}
          )
        )
      end)
    end)
  end
```
(`carrier_term/4` and `accept_type/2` are already public from Task 2.)

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/generators/conversion_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/conversion.ex test/antigen/generators/conversion_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): conversion accept carriers (convertible only after reduction)"
```

---

## Task 4: wire both polarities into `mix antigen`

**Files:** Modify `lib/mix/tasks/antigen.ex`. Test: `test/antigen/generators/conversion_test.exs`.

**Interfaces:** Produces: `default_gen/0` draws conversion challenges of both polarities.

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/generators/conversion_test.exs
  test "default_gen produces both conversion polarities" do
    cs = sample(Mix.Tasks.Antigen.default_gen(), 800)
    rej = Enum.filter(cs, fn c -> c.kind == :mutant_term and Map.get(c.payload.fault, :witness) == :conv end)
    acc = Enum.filter(cs, fn c -> c.kind == :typed_term and match?({:ctor, :vcons, [{:app,{:app,{:global,:plus},_},_}, _, _]}, c.payload.term) end)
    assert rej != [] and acc != []
  end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/generators/conversion_test.exs`
Expected: `Mix.Tasks.Antigen.default_gen/0` is undefined (it is currently `defp`) — a compile error, not an assertion failure. This is expected; fixed by Step 3's first edit below.

- [ ] **Step 3: Implement** — in `lib/mix/tasks/antigen.ex`, two edits:
  1. Make `default_gen` public (minimal visibility change — it is already called by `run/1`):
```elixir
  defp default_gen do
```
  →
```elixir
  def default_gen do
```
  2. Add the conversion branches to its `Antigen.Gen.frequency([...])` list:
```elixir
      {1, Antigen.Generators.Conversion.conv_reject()},
      {1, Antigen.Generators.Conversion.conv_accept("term/infer_check")},
      {1, Antigen.Generators.Conversion.conv_accept("term/subject_reduction")},
      {1, Antigen.Generators.Conversion.conv_accept("term/normalization")}
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/generators/conversion_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/mix/tasks/antigen.ex test/antigen/generators/conversion_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): wire conversion carriers (both polarities) into mix antigen"
```

---

## Task 5: conversion health metrics (structural accept detection)

**Files:** Modify `lib/antigen/runner.ex`. Test: `test/antigen/generators/conversion_test.exs`.

**Interfaces:** Produces: `Runner.conversion_metrics/1 :: %{conv_carrier_diversity, conv_both_polarities, conv_reject_count, conv_accept_count}`; `Runner.conv_carrier_of/1` (structural accept detector). Health line appended in `explore/1`.

**Reference (spec §6):** reject subset via `fault.carrier`; accept subset via structural detection of `:typed_term` terms — `:conv_index` iff `{:ctor, :vcons, [{:app,{:app,{:global,:plus},_},_}, _, _]}`; `:conv_motive` iff `{:case, _, {:lam, _, {:data, :Vec, _, [{:app,{:app,{:global,:plus},_},_}]}}, _}`. Safe in v1 (ordinary `Term` Vec goals carry only closed-numeral indices, never a `plus`).

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/generators/conversion_test.exs
  test "conversion_metrics: ≥2 carriers, both polarities present" do
    cs = sample(Mix.Tasks.Antigen.default_gen(), 800)
    m = Antigen.Runner.conversion_metrics(cs)
    assert m.conv_carrier_diversity >= 2
    assert m.conv_both_polarities == true
    assert m.conv_reject_count > 0 and m.conv_accept_count > 0
  end

  test "conversion_metrics does NOT misclassify ordinary typed-terms (no plus) as accept carriers" do
    ordinary = sample(Antigen.Generators.Term.typed_term("term/infer_check"), 200)
    m = Antigen.Runner.conversion_metrics(ordinary)
    assert m.conv_accept_count == 0
  end
```

- [ ] **Step 2: Run — expect FAIL** (`Runner.conversion_metrics/1` undefined).

- [ ] **Step 3: Implement** — add to `lib/antigen/runner.ex`:
```elixir
  @conv_carrier_floor 2

  @doc "Structural carrier tag of a typed_term accept carrier, or nil."
  def conv_carrier_of(%Challenge{kind: :typed_term, payload: %{term: t}}) do
    case t do
      {:ctor, :vcons, [{:app, {:app, {:global, :plus}, _}, _}, _, _]} -> :conv_index
      {:case, _, {:lam, _, {:data, :Vec, _, [{:app, {:app, {:global, :plus}, _}, _}]}}, _} -> :conv_motive
      _ -> nil
    end
  end

  def conv_carrier_of(_), do: nil

  @doc "Conversion-subset vacuity metrics over both polarities (spec §6)."
  def conversion_metrics(challenges) do
    rej =
      challenges
      |> Enum.filter(fn c -> match?(%Challenge{kind: :mutant_term}, c) and Map.get(c.payload.fault, :witness) == :conv end)
      |> Enum.map(fn c -> c.payload.fault.carrier end)

    acc = challenges |> Enum.map(&conv_carrier_of/1) |> Enum.reject(&is_nil/1)

    %{
      conv_carrier_diversity: MapSet.size(MapSet.new(rej ++ acc)),
      conv_both_polarities: rej != [] and acc != [],
      conv_reject_count: length(rej),
      conv_accept_count: length(acc)
    }
  end

  def conversion_stamp(%{conv_carrier_diversity: d, conv_both_polarities: both}),
    do: if(d >= @conv_carrier_floor and both, do: :healthy, else: :vacuous)
```
And in `explore/1`, after the `mutant_term` health line:
```elixir
    cm = conversion_metrics(challenges)

    if cm.conv_reject_count + cm.conv_accept_count > 0 do
      IO.puts(
        "antigen health[conversion]: carriers=#{cm.conv_carrier_diversity} " <>
          "both_polarities=#{cm.conv_both_polarities} " <>
          "reject=#{cm.conv_reject_count} accept=#{cm.conv_accept_count} → #{conversion_stamp(cm)}"
      )
    end
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/generators/conversion_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex test/antigen/generators/conversion_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): conversion health metrics with structural accept detection"
```

---

## Task 6: bank conversion seeds + static meta-test

**Files:** Modify `test/antigen/seeds.sexp`, `test/antigen/mutation_meta_test.exs`.

**Interfaces:** Produces: banked reject + accept conversion seeds meeting the floors as a committed fact; both polarities replay to the correct verdict.

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/mutation_meta_test.exs (before final end)
  test "banked conversion corpus: both polarities present, replay to correct verdicts" do
    banked = Corpus.stream(@seeds_path) |> Enum.flat_map(fn {:ok, c} -> [c]; _ -> [] end)
    m = Runner.conversion_metrics(banked)
    assert m.conv_carrier_diversity >= 2, "banked conv carriers #{m.conv_carrier_diversity} < 2"
    assert m.conv_both_polarities, "banked conversion missing a polarity"

    for c <- banked, c.kind == :mutant_term, Map.get(c.payload.fault, :witness) == :conv do
      assert Antigen.Assays.Mutation.run(c) == :ok        # reject seeds are correctly rejected
    end
    for c <- banked, Runner.conv_carrier_of(c) != nil do
      assert Antigen.Assays.Term.run(c) == :ok            # accept seeds are correctly accepted
    end
  end
```

- [ ] **Step 2: Run — expect FAIL** (no conversion seeds banked → `conv_carrier_diversity == 0`).

- [ ] **Step 3: Implement** — bank seeds via a script against the built test beams (deep, coverage-deduped, covering both carriers × both polarities):
```bash
MIX_ENV=test mix compile
elixir $(printf ' -pa %s' _build/test/lib/*/ebin) - <<'EOF'
alias Antigen.{Corpus, Generators.Conversion}
alias Antigen.Backend.StreamData, as: B
path = "test/antigen/seeds.sexp"

rej = B.interp(Conversion.conv_reject()) |> Enum.take(1500) |> Enum.filter(& &1.payload.fault.depth >= 4)
acc = B.interp(Conversion.conv_accept("term/infer_check")) |> Enum.take(1500)

pick = fn list, keyfn ->
  list |> Enum.reduce({%{}, []}, fn c, {seen, acc} ->
    k = keyfn.(c)
    if Map.has_key?(seen, k), do: {seen, acc}, else: {Map.put(seen, k, 1), [c | acc]}
  end) |> elem(1)
end

picked =
  pick.(rej, fn c -> c.payload.fault.carrier end) ++
  pick.(acc, fn c -> {c.assay, elem(c.payload.term, 0)} end)

for c <- picked do
  c = %{c | seed: :erlang.phash2({c.kind, c.payload})}
  IO.inspect({Corpus.append(path, c, Corpus.dedup_key(c, :seed)), c.kind}, label: "banked")
end
EOF
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/mutation_meta_test.exs test/antigen/corpus_replay_test.exs`
(The existing mutation/typed-term replay + every-entry invariants must stay green.)

- [ ] **Step 5: Commit**
```bash
git add test/antigen/seeds.sexp test/antigen/mutation_meta_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): bank conversion seeds (both polarities) + static replay meta-test"
```

---

## Task 7: Acceptance — quarantine + full suite + explore

**Files:** none (verification only).

- [ ] **Step 1: Quarantine** — `mix test test/antigen/architecture_test.exs` (no `StreamData` literal in `conversion.ex`). PASS.
- [ ] **Step 2: Full suite ONCE** — `mix test`. All green.
- [ ] **Step 3: Explore** — `MIX_ENV=test mix antigen --count 800 --seeds /tmp/cv_seeds.sexp --corpus /tmp/cv_corpus.sexp`. Expect a line `antigen health[conversion]: carriers=2 both_polarities=true reject=… accept=… → healthy` and **0 infections**. Record it for the report.
- [ ] **Step 4:** No commit. Any conversion infection (a reject survivor OR an accept false-violation) is a genuine conversion-at-depth finding — STOP and report, do not silence.

---

## Self-Review

**Spec coverage:** §3 mechanism + draw order → Task 2 (`depth_split`). §4 construction guarantees + `vec_of` → Tasks 2/3. §5 totality → Task 2/3 construction tests assert `{:error,_}`/`:ok`. §6 challenge model (reject fault, `type` field, atoms) → Tasks 1/2; accept payload → Task 3; health gate + structural detection + masking caveat → Task 5. §7 tests 1–8 → 7.1 Task 2; 7.2 Task 2 (witness+redex); 7.3 Task 3 (accept + control); 7.4 Task 3 (redex present); 7.5 Tasks 2/3 (depth reached); 7.6 Task 1 (blob decode); 7.7 Tasks 5/6 (health, seeds, detector-not-false-positive); 7.8 Task 7 (full suite). §8 files → Tasks 1–6.

**Placeholder scan:** the only fill-in is Task 1's base64 blob (generated in Step 1, pasted in Step 2) and Task 6's banking script output — both concrete runtime procedures, not code placeholders.

**Type consistency:** `carrier_term/4`, `accept_type/2`, `vec_of/1`, `num/1` defined in Task 2, reused in Task 3. `conv_reject/0 → :mutant_term` (Task 2) and `conv_accept/1 → :typed_term` (Task 3) consumed by Task 4 (mix wiring) and Task 5 (metrics). `conv_carrier_of/1` structural predicate defined in Task 5, reused in Task 6's replay test. `fault.carrier`/`fault.witness == :conv` keys consistent across Tasks 2, 5, 6. `@conv_carrier_floor 2` matches spec §6 floor.

**Deviation note:** none from the hardened spec — the spec was probe-verified during review and again here at deep `conv_depth`. Empty-context choice (Global Constraints) is a spec-consistent concretization (§4 carriers are closed).
