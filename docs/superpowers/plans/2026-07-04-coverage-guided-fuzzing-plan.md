# Coverage-Guided Fuzzing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Give Antigen real `:cover`-based code-coverage feedback over the Cure kernel, in two staged phases — (1) measure kernel coverage + report cold lines; (2) a coverage-guided loop that steers generation by new-edge yield.

**Architecture:** A new `Antigen.Cover` harness drives Erlang `:cover` around the existing `Runner.explore/1` campaign; `Antigen.CoverReport` renders the report. Phase 2 adds per-input coverage attribution, an edge-minimal corpus, a live-refreshed SeedPool, and edge-novelty generator reweighting — all in Antigen tooling, reusing `Mutation`/`Triage`/`Corpus`/`SeedPool` unchanged. Entry point is a new `cover` subcommand of `mix antigen`.

**Tech Stack:** Elixir/OTP `:cover`, `:beam_lib` (abstract_code for line→function), StreamData (only via `Antigen.Backend.StreamData`), ExUnit.

## Global Constraints

- **No TCB edits.** No changes to `Cure.Core.*` or `Cure.Elab.*`. Coverage is tooling; `:cover` instruments for measurement only (in-memory via `code:load_binary/3`, never writes `.beam`).
- **`:cover` is node/VM-global + serial.** One cover session per node. Every test file that starts/stops `:cover` MUST `use ExUnit.Case, async: false`. Never run the normal `mix test` under cover.
- **Always clean up cover.** Wrap campaigns in `try/after` so `:cover.stop/0` runs even on crash; instrumented modules must not leak into the rest of the VM.
- **StreamData quarantine.** Only `Antigen.Backend.StreamData` may reference `StreamData`. New generator/assay code must not.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NEVER a `Co-Authored-By` trailer.
- **One build/test run at a time.** `MIX_ENV=test`, from the worktree root. Stay on `autopilot/antigen-tier-b`. No auto-merge.
- **Strict TDD, tests immutable once green.** Every task below follows failing-test → RED → minimal implementation → GREEN → commit, in that order — never implement before the test exists. Once a test is written and confirmed red for the right reason, make it pass by changing implementation code only; never delete, skip, or weaken a test to reach green. The sole exception is a test proven to encode incorrect behavior itself — in that case state explicitly why it's wrong before touching it.
- `@cover_modules = [Cure.Core.Kernel, Normalise, Conv, Eval, Quote, Inductive, Serialize, Certificate]` (verbatim from spec §Phase-1).

---

## File Structure

- **Create** `lib/antigen/cover.ex` — `Antigen.Cover`: `:cover` lifecycle, guard, campaign-under-cover, per-module analyse, cold-line extraction, (Phase 2) per-input delta + guided loop orchestration.
- **Create** `lib/antigen/cover_report.ex` — `Antigen.CoverReport`: line→function map via `:beam_lib`, deterministic markdown render.
- **Create** `test/support/cover_fixture.ex` — a tiny `Antigen.CoverFixture` module with known executable lines + a branch, used as the controlled target for Phase-1 unit tests (never the real kernel).
- **Modify** `lib/mix/tasks/antigen.ex` — add the `cover` mode (`["cover" | _]`) + `--out`/`--guided`/`--precise`/`--edge-corpus` switches.
- **Modify** `lib/antigen/runner.ex` — Phase 2: an edge-novelty reweighting hook usable by the guided loop, alongside (not replacing) `draw_biased`.
- **Create** `test/antigen/cover_test.exs`, `test/antigen/cover_report_test.exs`, `test/antigen/cover_guided_test.exs` — all `async: false`.
- **Reuse unchanged:** `Antigen.Generators.Mutation`, `Antigen.Triage`, `Antigen.Corpus`, `Antigen.Generators.SeedPool`, `Antigen.Report`.

**Interfaces produced (names later tasks rely on):**
- `Antigen.Cover.with_cover(modules, fun)` → runs `fun` with `modules` cover-compiled, guarantees `:cover.stop/0`; returns `fun`'s result.
- `Antigen.Cover.cover_compilable?(module)` → boolean (module's beam carries real `abstract_code`, i.e. was compiled with debug_info retained — checked by chunk *value*, not just chunk presence).
- `Antigen.Cover.line_coverage(module)` → `%{covered: [line], cold: [line], total: n}` (from `:cover.analyse(module, :coverage, :line)`).
- `Antigen.Cover.run_report(opts)` → runs a campaign under cover, returns `%{module => line_coverage}`.
- `Antigen.CoverReport.render(coverage_map, fn_index)` → markdown string (deterministic).
- `Antigen.CoverReport.function_index(module)` → `%{line => {fun, arity}}` via `:beam_lib`.
- Phase 2: `Antigen.Cover.delta(prev_set, module)` → new lines; `Antigen.Cover.guided_loop(opts)`.

---

## PHASE 1 — Coverage measurement + report

### Task 1: `Antigen.Cover` lifecycle + cover-compilability guard

**Files:** Create `lib/antigen/cover.ex`, `test/support/cover_fixture.ex`, `test/antigen/cover_test.exs`.

- [ ] **Step 1: Create the fixture** `test/support/cover_fixture.ex`:

```elixir
defmodule Antigen.CoverFixture do
  @moduledoc false
  def classify(n) when is_integer(n) do
    cond do
      n < 0 -> :neg      # line A
      n == 0 -> :zero    # line B
      true -> :pos       # line C
    end
  end
end
```

`test/support` is **already** on the compile path — confirmed at `mix.exs:37` (`defp elixirc_paths(:test), do: ["lib", "test/support"]`). No `mix.exs` edit is needed in this step; just create the file (and the `test/support/` directory, which does not yet exist in the tree).

- [ ] **Step 2: Write the failing test** (`test/antigen/cover_test.exs`):

```elixir
defmodule Antigen.CoverTest do
  use ExUnit.Case, async: false   # :cover is node-wide global
  alias Antigen.Cover

  test "cover_compilable? is true for a debug_info module, and with_cover cleans up" do
    assert Cover.cover_compilable?(Antigen.CoverFixture)
    assert :cover.modules() == []   # not instrumented before
    result = Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(5)
      :ran
    end)
    assert result == :ran
    # cover fully stopped afterward — instrumented module list is empty again.
    # (Confirmed against OTP: :cover.stop/0 does NOT stop the cover_server
    # process or make :cover.modules/0 raise — it unloads instrumented modules,
    # and :cover.modules/0 keeps returning a plain list, [] once none remain.)
    assert :cover.modules() == []
  end

  test "cover_compilable? is false for a beam without debug_info" do
    # Build a module with NO debug_info at test runtime (mirrors `erlc` with no
    # `+debug_info`) — Mix's elixirc always embeds debug_info project-wide, so
    # this is the only way to exercise the false branch without a global
    # compiler-option change. Without this case, cover_compilable?/1 could
    # vacuously always return true and no test would catch it.
    # Compile to a REAL .beam on disk (not in-memory :binary) and load via
    # :code.load_abs/1, so :code.which/1 resolves a real path and
    # cover_compilable?/1 actually reaches :beam_lib.chunks on it — this is
    # what exposes the sentinel-value bug (an in-memory :code.load_binary/3
    # load makes :code.which/1 return the literal atom given as the 2nd arg,
    # e.g. `nofile`, so :beam_lib.chunks fails with :enoent and the guard
    # returns false for the wrong reason, without exercising the real branch).
    dir = System.tmp_dir!()
    src_path = Path.join(dir, "antigen_no_debug_fixture.erl")
    File.write!(src_path, """
    -module(antigen_no_debug_fixture).
    -export([f/0]).
    f() -> ok.
    """)
    {:ok, :antigen_no_debug_fixture} =
      :compile.file(String.to_charlist(src_path), [{:outdir, String.to_charlist(dir)}])
    beam_no_ext = dir |> Path.join("antigen_no_debug_fixture") |> String.to_charlist()
    {:module, :antigen_no_debug_fixture} = :code.load_abs(beam_no_ext)

    try do
      refute Cover.cover_compilable?(:antigen_no_debug_fixture)
    after
      :code.purge(:antigen_no_debug_fixture)
      :code.delete(:antigen_no_debug_fixture)
    end
  end
end
```

- [ ] **Step 3: Run RED** — `MIX_ENV=test mix test test/antigen/cover_test.exs` → both tests fail (module undefined).

- [ ] **Step 4: Implement** `lib/antigen/cover.ex`:

```elixir
defmodule Antigen.Cover do
  @moduledoc "Erlang :cover harness for kernel code coverage (Antigen tooling; no TCB changes)."

  @cover_modules [Cure.Core.Kernel, Cure.Core.Normalise, Cure.Core.Conv,
                  Cure.Core.Eval, Cure.Core.Quote, Cure.Core.Inductive,
                  Cure.Core.Serialize, Cure.Core.Certificate]
  def cover_modules, do: @cover_modules

  @doc """
  True if `module`'s beam carries real abstract_code (required by both
  :cover.compile_beam AND Task 3's function_index; :cover.analyse needs the
  former, cold-line→function mapping needs the latter — same underlying chunk).

  MUST inspect the chunk's inner VALUE, not just that :beam_lib.chunks/2
  returned :ok — confirmed against OTP: :beam_lib.chunks(beam, [:abstract_code])
  ALWAYS returns {:ok, {Mod, [...]}} for any valid .beam, even when abstract
  code is absent; absence is signalled by the sentinel atom
  `:no_abstract_code` as the chunk's VALUE, not by an outer :error. A guard
  that only pattern-matches the outer {:ok, _} (as an earlier draft of this
  function did) is vacuously always true and never rejects anything — the
  negative test above exists specifically to catch that regression.
  """
  def cover_compilable?(module) do
    case :code.which(module) do
      beam when is_list(beam) ->
        match?(
          {:ok, {^module, [{:abstract_code, {:raw_abstract_v1, _forms}}]}},
          :beam_lib.chunks(beam, [:abstract_code])
        )

      _ ->
        false
    end
  end

  @doc "Run `fun` with `modules` cover-compiled; always :cover.stop afterward."
  def with_cover(modules, fun) do
    {:ok, _} = :cover.start()
    try do
      Enum.each(modules, fn m ->
        {:ok, ^m} = {:cover.compile_beam(m), m} |> normalize_compile(m)
      end)
      fun.()
    after
      :cover.stop()
    end
  end

  defp normalize_compile({{:ok, m}, _}, m), do: {:ok, m}
  defp normalize_compile({{:error, reason}, m}, m),
    do: raise("cover.compile_beam failed for #{inspect(m)}: #{inspect(reason)}")
end
```

> Confirmed against OTP: `:cover.compile_beam/1` called with a **single module atom** (as `Enum.each` does here, one call per module) returns the single tuple `{:ok, Module}` — the list-of-results shape only occurs when the *argument* is a list, which this code never passes. `normalize_compile/2` as written is correct for the single-module call form; keep the `try/after :cover.stop()` invariant.

- [ ] **Step 5: Run GREEN** — `MIX_ENV=test mix test test/antigen/cover_test.exs` → PASS.
- [ ] **Step 6: Commit** — `feat(antigen): :cover lifecycle harness + compilability guard`.

### Task 2: line coverage analyse + cold-line extraction

**Files:** Modify `lib/antigen/cover.ex`; extend `test/antigen/cover_test.exs`.

- [ ] **Step 1: Failing test** — run the fixture's `classify` under cover on inputs that hit only the `:pos` branch, assert `line_coverage` reports the `:neg`/`:zero` lines cold:

```elixir
  test "line_coverage reports covered and cold lines, excluding the line-0 pseudo-entry" do
    cov =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        Antigen.CoverFixture.classify(5)   # hits :pos only
        Cover.line_coverage(Antigen.CoverFixture)
      end)
    assert cov.total > 0
    assert cov.cold != []                  # :neg / :zero never executed
    assert Enum.all?(cov.covered ++ cov.cold, &is_integer/1)
    assert length(cov.covered) + length(cov.cold) == cov.total
    # Confirmed against OTP: :cover.analyse(mod, :coverage, :line) emits a
    # {{Mod, 0}, {0, 1}} pseudo-entry (module-level, not real source) for
    # every module — verified empirically on a `def ... do cond do ... end end`
    # fixture. Without filtering `line == 0`, it silently lands in `cold`
    # (NotCov == 1) and both the total and the eventual function_index lookup
    # (Task 3) get polluted by a line that maps to no real code. This
    # assertion is the one that actually catches a missing filter — the
    # assertions above all still pass even if line 0 leaks through.
    refute 0 in cov.cold
    refute 0 in cov.covered
  end
```

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `line_coverage/1` using `:cover.analyse(module, :coverage, :line)` — returns `{:ok, [{{Mod,Line},{Cov,NotCov}}]}`; `covered = lines where Cov==1`, `cold = lines where NotCov==1`, **excluding `line == 0`** (the pseudo-entry confirmed above). Note `line_coverage` must be called *inside* `with_cover` (before stop):

```elixir
  def line_coverage(module) do
    {:ok, pairs} = :cover.analyse(module, :coverage, :line)
    {cov, cold} =
      pairs
      |> Enum.reject(fn {{_m, line}, _} -> line == 0 end)
      |> Enum.reduce({[], []}, fn {{_m, line}, {c, _n}}, {yes, no} ->
        if c > 0, do: {[line | yes], no}, else: {yes, [line | no]}
      end)
    %{covered: Enum.sort(cov), cold: Enum.sort(cold), total: length(cov) + length(cold)}
  end
```

> `:cover.analyse/3`'s tuple shape confirmed against OTP directly (`{:ok, [{{Mod,Line},{Cov,NotCov}}]}`, `Cov`/`NotCov` each 0 or 1). The `line == 0` pseudo-entry is real, not hypothetical — reject it before computing `total`, not just before bucketing, so `total` reflects real executable lines only.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): line-coverage analyse + cold-line extraction`.

### Task 3: `Antigen.CoverReport` — line→function map + deterministic markdown

**Files:** Create `lib/antigen/cover_report.ex`, `test/antigen/cover_report_test.exs`.

- [ ] **Step 1: Failing test** — build a `function_index` for the fixture and assert cold lines render grouped under their function; assert render is deterministic (same input → byte-identical output, sorted, no timestamps):

```elixir
defmodule Antigen.CoverReportTest do
  use ExUnit.Case, async: false
  alias Antigen.{Cover, CoverReport}

  test "function_index maps lines to {fun, arity}, keyed by plain integer lines" do
    idx = CoverReport.function_index(Antigen.CoverFixture)
    assert Enum.any?(idx, fn {_line, fa} -> fa == {:classify, 1} end)
    # This is the assertion that actually catches a missing :erl_anno.line/1
    # normalization: if a key were left as the raw {Line, Column} anno tuple,
    # `Enum.any?` above would still find the {:classify, 1} value (only the
    # VALUE is checked there) — the key-shape check below is what fails.
    assert Enum.all?(idx, fn {line, _fa} -> is_integer(line) end)
    # Cross-check against line_coverage/1's own (confirmed integer) keys —
    # function_index must be usable to look up cover's real cold lines.
    cold_lines =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        Antigen.CoverFixture.classify(5)
        Cover.line_coverage(Antigen.CoverFixture)
      end).cold
    assert Enum.all?(cold_lines, &Map.has_key?(idx, &1))
  end

  test "render is deterministic and groups cold lines by function" do
    covmap = %{Antigen.CoverFixture => %{covered: [5], cold: [3, 4], total: 3}}
    idx = CoverReport.function_index(Antigen.CoverFixture)
    out1 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    out2 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    assert out1 == out2
    assert out1 =~ "classify/1"
  end
end
```

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `function_index/1` via `:beam_lib.chunks(beam, [:abstract_code])` (same chunk `cover_compilable?/1` already validated — reuse its `{:raw_abstract_v1, forms}` match) → walk the abstract forms, mapping each function's clause line spans to `{name, arity}`.

  **Anno normalization is required, not optional.** Confirmed against OTP: on this project's Erlang/OTP release, abstract-code annotations are the compact 2-tuple `{Line, Column}` (e.g. `{3, 1}`), NOT a bare integer — verified directly via `:beam_lib.chunks/2` on a compiled fixture. Meanwhile `:cover.analyse/3`'s `{Mod, Line}` keys (Task 2) ARE bare integers. Extract every line number via `:erl_anno.line(anno)` (confirmed to normalize both the compact tuple form and a bare-integer anno to a plain integer) before using it as a map key — pattern-matching a `{:function, anno, name, arity, clauses}` form and treating `anno` as if it were already an integer produces keys of the wrong shape that silently never match `line_coverage/1`'s cold-line integers, so `function_index` results would look empty/wrong without ever raising.

  Implement `render/2`: a per-module summary table (module, covered/total, %) sorted by module name, then a "Cold lines" section grouping each module's cold lines under their enclosing `fun/arity` (unknown → `:module-level`). No timestamps in the body.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): coverage report renderer (line→function, deterministic markdown)`.

### Task 4: `mix antigen cover` subcommand

**Files:** Modify `lib/mix/tasks/antigen.ex`; extend a mix-task test (or `test/antigen/cover_test.exs`).

- [ ] **Step 1: Failing test** — assert `mode` resolution routes `["cover"]` to a cover run and that `run_report/1` produces a `%{module => coverage}` map over the real `@cover_modules` (small `--count`), writing a report to a tmp `--out`. Keep it `async: false` and small.

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `Antigen.Cover.run_report(opts)` — `with_cover(@cover_modules, fn -> run a campaign (Runner.explore with opts[:count]/gen) then Map.new(@cover_modules, &{&1, line_coverage(&1)}) end)`, then render + write to `opts[:out]`. Add `mode = :cover` dispatch in `Mix.Tasks.Antigen.run/1` (`match?(["cover" | _], rest)`), parse `--out`, call `Cover.run_report`, print a one-line summary. Add `out`/`guided`/`precise`/`edge_corpus` to `@switches`.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): mix antigen cover subcommand (Phase 1 report)`.

### Task 5: Phase 1 verification (real kernel)

- [ ] **Step 1:** `MIX_ENV=test mix antigen cover --count 500 --out /tmp/kcov.md` → produces a report over the real kernel modules; eyeball that cold lines look plausible (e.g. rarely-hit error branches).
- [ ] **Step 2:** `MIX_ENV=test mix test` → full suite still green (cover left no residue; new tests `async: false`). Confirm `:cover.modules()` server is down after the task.
- [ ] **Step 3: Commit** any report artifact intentionally kept, else none. Phase 1 complete.

---

## PHASE 2 — Coverage-guided loop

### Task 6: per-input coverage delta (batch-gate + precise re-attribution)

**Files:** Modify `lib/antigen/cover.ex`; `test/antigen/cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — with the fixture cover-compiled, snapshot the accumulated covered set, run an input hitting a new line, assert `delta/2` returns exactly that new line; run an input hitting only already-covered lines, assert `delta/2` is empty. (`async: false`.)
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `covered_set(modules)` (union of `line_coverage` covered, tagged `{module, line}`) and `delta(prev_set, modules)` = `covered_set - prev_set`. Implement the **batch-gate/precise** pair: `round_delta(prev, modules)` (one analyse) and, when non-empty, `attribute(prev, challenges, run_fun, modules)` which `:cover.reset()`s and re-runs each challenge individually to find which caused new lines. Note `:cover.reset/0` clears counters node-wide — only valid inside a `with_cover` block and incompatible with concurrent cover use (already guarded by `async: false` + the serial mode).
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): per-input coverage delta (batch-gate + precise attribution)`.

### Task 7: interesting-input edge-minimal corpus

**Files:** Modify `lib/antigen/cover.ex`; extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — feed a challenge that hits a new edge; assert it's banked to a tmp edge-corpus (via `Corpus.append`), minimized first via `Triage.minimize` (assert banked size ≤ original), and deduped by covered-line set (a second challenge with the same covered set is not re-banked).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `bank_interesting(challenge, new_lines, edge_corpus_path, seen_sets)` — if `MapSet.new(new_lines)` not in `seen_sets`: `Triage.minimize(challenge, pred, budget)` where `pred` re-runs the challenge under cover and checks it still hits ≥1 of `new_lines`; `Corpus.append(edge_corpus_path, min_challenge, Corpus.dedup_key(min_challenge, :antibody))`; return the updated `seen_sets`. Default path `test/antigen/edge_corpus.sexp`.

  **Pin the `dedup_key` argument explicitly** — `Corpus.dedup_key/2`'s spec is `(Challenge.t(), :antibody | :seed) :: String.t()`; it only accepts those two atoms, no third "by covered-line set" variant exists or should be added (the covered-line-set dedup is the in-memory `seen_sets` MapSet gate above it, evaluated BEFORE `Corpus.append` is ever called — `seen_sets` is what implements "deduped by covered-line set," not the on-disk key). Use `:antibody` (assay + term-pieces content key) for the on-disk append, matching how `Runner.explore` already dedupes its own antibody corpus (`lib/antigen/runner.ex`, `Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))`) — `:seed` is reserved for the closed-`:typed_term` seed store (`Coverage.key`-based) and is the wrong key for an edge corpus that may bank any challenge kind.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): edge-minimal interesting-input corpus (Triage-minimized, set-deduped)`.

### Task 8: SeedPool live-refresh feedback

**Files:** Modify `lib/antigen/cover.ex`; extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — assert that after `bank_interesting` on a **closed `:typed_term` challenge with `ctx: []`**, the guided loop re-`Process.put(:antigen_seed_pool, ...)` a pool that now includes the banked term's type key (so `gnat`'s crossover can draw it within the same run). Assert the pool before the bank lacked it and after includes it.

  **Fixture kind is load-bearing, not incidental.** `SeedPool.load/1` (`lib/antigen/generators/seed_pool.ex`) only picks up records matching `{:ok, %{kind: :typed_term, payload: %{ctx: [], type: type, term: term}}}` with `Term.closed?(term)` — every other challenge kind (`:mutant_term`, an open-context `:typed_term`, etc.) is silently dropped by `load/1`'s `flat_map`, by design (spec §Phase-2 mechanism note: "Banking an interesting input into that pool (as a `:typed_term` seed, keyed by its checked type — the same shape `SeedPool.load/1` already expects)"). This is expected behavior, not a bug: for challenge kinds outside that shape, `refresh_seed_pool!` is a no-op on this feedback path — the interesting input is still durably banked to the edge-corpus by Task 7 regardless. A red test written against a `:mutant_term` (or any non-closed-typed_term) fixture challenge could never turn green through this path and would misrepresent what "SeedPool live-refresh" actually covers — use a closed `:typed_term`, `ctx: []` fixture challenge here.
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `refresh_seed_pool!(edge_corpus_path)` — `SeedPool.load(edge_corpus_path)` (or in-memory merge of the newly banked seed) and `Process.put(:antigen_seed_pool, pool)`. Call it after each `bank_interesting`. This is orchestration in `Antigen.Cover`; `SeedPool` source is unchanged (spec §Phase-2 mechanism note). Document in the moduledoc/comment that this refresh only affects closed `:typed_term` bankings, per the fixture note above.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): live SeedPool refresh so crossover sees banked edges mid-run`.

### Task 9: edge-novelty generator reweighting

**Files:** Modify `lib/antigen/runner.ex`; `test/antigen/runner_test.exs` (async: false if it touches shared state).

- [ ] **Step 1: Failing test** — a pure unit test of the reweight function: given per-group new-edge yields, assert groups with higher new-edge yield get proportionally higher weight (parallel to the existing health-based `reweight`, but keyed on edge yield). No `:cover` needed for this unit (feed synthetic yields).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `reweight_by_edges(weights, group_table, edge_yields)` in `runner.ex` — mirrors the existing `reweight/3` shape but uses edge-yield stamps. Keep it additive: the default `explore`/`draw_biased` path is untouched; the guided loop opts into this reweighter.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): edge-novelty generator reweighting (guided-mode bias)`.

### Task 10: guided loop orchestration + jackpot coverage-delta

**Files:** Modify `lib/antigen/cover.ex` (+ `runner.ex` if the loop lives there); extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — run a short guided loop over the fixture (or a small kernel campaign); assert it (a) terminates on plateau (K rounds no new edge), (b) grows the edge-corpus monotonically, and (c) when a challenge both hits a new edge AND violates (use a stub assay that violates on a marked input), the single `Report.write_infection` call carries a coverage-delta field in its `health` map (not a second report).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `guided_loop(opts)` — the draw→run-under-cover→delta→(bank+refresh+reweight | discard)→repeat loop with a plateau counter; thread coverage delta into the existing `write_infection(dir, c, detail, health)` call by adding `:coverage_delta` to the `health` map. Reuse `Runner.explore`'s per-challenge assay dispatch; do not fork it — factor the shared step if needed, keeping the non-guided path byte-identical.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): coverage-guided loop + jackpot coverage-delta in infection report`.

### Task 11: `mix antigen cover --guided` wiring

**Files:** Modify `lib/mix/tasks/antigen.ex`; extend the mix-task test.

- [ ] **Step 1: Failing test** — assert `["cover"]` + `--guided` routes to `guided_loop`, `--precise` sets the precise flag, `--edge-corpus PATH` overrides the corpus path.
- [ ] **Step 2: RED.** **Step 3:** wire the flags into `Cover.guided_loop(opts)`. **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): mix antigen cover --guided/--precise/--edge-corpus wiring`.

### Task 12: Phase 2 verification

- [ ] **Step 1:** `MIX_ENV=test mix antigen cover --guided --count 2000 --out /tmp/kcov2.md` → runs the guided loop, banks an edge-corpus, produces a report. Compare kernel coverage % vs. the Phase-1 unguided run at equal budget (spec Risk #3: guided should reach ≥ unguided coverage; log the delta — if not measurably better, record the finding, do NOT silently claim success).
- [ ] **Step 1b (spec Risk #2 — quantify both cost regimes):** also run `MIX_ENV=test mix antigen cover --guided --precise --count 2000 --out /tmp/kcov2-precise.md` and record wall-clock time for both runs. Report the batch-vs-precise cost delta explicitly (this is the actual quantification Risk #2 asks for — Step 1 alone only measures guided-vs-unguided coverage, not the two attribution regimes' cost).
- [ ] **Step 2:** `MIX_ENV=test mix test` → full suite green; `:cover` server down afterward. **Manually verify the StreamData quarantine on the new files** — `architecture_test.exs`'s grep-guard globs only `lib/antigen/{generators,assays}/**/*.ex`, which does NOT cover `lib/antigen/cover.ex`, `lib/antigen/cover_report.ex`, or `lib/mix/tasks/antigen.ex` (confirmed by reading the guard: `Path.wildcard("lib/antigen/{generators,assays}/**/*.ex")`), so "architecture_test.exs still green" is not evidence about the new files and must not be cited as such. Instead run `grep -rn "StreamData" lib/antigen/cover.ex lib/antigen/cover_report.ex lib/mix/tasks/antigen.ex` and confirm no match (none of these files need direct `StreamData` access — coverage tooling only calls `Runner.explore/1`, which already owns the one legitimate `Backend.StreamData` call site).
- [ ] **Step 3:** Restore/keep `test/antigen/edge_corpus.sexp` per the standing corpus-expansion policy (intentional expansion; commit separately if it grew). Commit any kept report.

---

## Self-review (against spec)

- **Phase 1 (measure+report)** → Tasks 1–5 (lifecycle+guard, analyse+cold, report+beam_lib fn-map, mix subcommand, verify). ✓
- **Phase 2 (guided loop)** → Tasks 6–12 (delta batch/precise, edge-minimal corpus, SeedPool live-refresh, edge reweight, loop+jackpot, wiring, verify). ✓
- **Spec Risk #1 (cover-compilable/debug_info)** → Task 1 `cover_compilable?` guard. ✓
- **Spec Risk #2 (batch/precise cost)** → Task 6 nested model + Task 12 Step 1b quantifies both regimes (batch-default vs. `--precise`, wall-clock). ✓
- **Spec Risk #3 (indirect feedback weakest link)** → Task 12 Step 1 explicitly measures guided-vs-unguided and records a finding if not better. ✓
- **Spec Risk #4 (determinism)** → Task 3 deterministic render test. ✓
- **Spec Risk #5 (line→function needs beam_lib)** → Task 3 `function_index` via abstract_code, with `:erl_anno.line/1` normalization (confirmed necessary — abstract-code annos are `{Line,Column}` tuples, not bare integers, on this OTP release). ✓
- **No-TCB-edits / cover cleanup / async:false / quarantine** → Global Constraints + every cover test `async: false` + Task 12 Step 2 manual grep (the `architecture_test.exs` automated guard does not reach the new files — see Task 12 Step 2). ✓
- **No placeholders:** every task's API usage against real dependencies is now pinned by direct empirical verification against this OTP release (`:cover.compile_beam/1`'s single-module `{:ok, Module}` shape, `:cover.analyse/3`'s `{:ok,[{{Mod,Line},{Cov,NotCov}}]}` shape and its `line == 0` pseudo-entry, `:cover.modules/0`'s non-raising post-stop behavior, `:beam_lib.chunks/2`'s sentinel-value-on-absence shape for both `:debug_info` and `:abstract_code`, `:erl_anno.line/1` normalization) — none of the "executor confirms against OTP" hedges from the prior draft remain unresolved. Antigen-internal reuse APIs are pinned (`Runner.explore`, `Report.write_infection/4`, `SeedPool.load/1`'s closed-`:typed_term`-only filter, `Corpus.append/3` + `Corpus.dedup_key/2`'s `:antibody`/`:seed` atoms only).
