# Antigen prune + regenerate staleness pipeline — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give Antigen a way to bring its committed replay stores forward across kernel shape changes — regenerate the generator-derived seed pool from current generators, and prune the fuzz-found antibody corpus (keep-if-still-valid, else retire with a reason) — without ever rewriting a term.

**Architecture:** Two independent mix tasks over small, unit-tested library functions. `Antigen.Regen.regenerate_seeds/1` re-harvests coverage-novel seeds from the current generators into a fresh file and atomically swaps it over `seeds.sexp` ("replace, not append"). `Antigen.Prune.prune/3` walks `corpus.sexp`, re-checks each record against the live kernel through a shared replay registry (`Runner.replay_registry/0`, built from the authoritative dispatch table), keeps records that decode and replay `:ok`, and moves the rest verbatim to an append-only `retired.sexp` annotated with the failure reason. The existing `corpus_replay_test` remains the oracle — prune's keep-criterion *is* that gate's criterion, so a correct run leaves the gate green by construction.

**Tech Stack:** Elixir, Mix.Task, ExUnit. Reuses `Antigen.Corpus` (record codec + `record_lines/1`), `Antigen.Runner` (`generate/1`, `registered_assays/0`, `assay_module_for/1`), `Mix.Tasks.Antigen.default_gen/0`, `Antigen.Generators.SeedPool`.

## Global Constraints

- **Never co-sign commits.** Plain `git commit -m "..."` only — NO `Co-Authored-By`, NO `Claude-Session` trailer, NO any other trailer. Commits appear to come from the user alone. (from `/Users/ch/Develop/CLAUDE.md`.)
- **Tests must stay git-clean.** No test may mutate a committed store (`test/antigen/corpus.sexp`, `seeds.sexp`, `reach.sexp`, `retired.sexp`). All fixture I/O goes to a per-test `tmp/…` directory, removed in `setup`/`on_exit`. (Committed stores are read-only inputs at most.)
- **No term rewriting, no `schema=` versioning, no rule registry** (YAGNI — spec "Why no rewrite engine"). Stale generator-derived records are re-derived; stale antibodies are kept or retired, never translated.
- **Canonical paths:** corpus `test/antigen/corpus.sexp`, seeds `test/antigen/seeds.sexp`, retired `test/antigen/retired.sexp`. Every task's requirements implicitly include this section.
- Spec: `docs/superpowers/specs/antigen/2026-07-10-antigen-migration-design.md`. Merge tool (`Corpus.merge/2` + `mix antigen.merge`) already landed (930ffd6) and is out of scope.

---

### Task 1: Shared replay registry — `Runner.replay_registry/0`

Prune must re-check records for **every** assay the kernel knows, not the hardcoded subset in `corpus_replay_test`'s `@registry`. Build the full map from the authoritative dispatch table (`registered_assays/0` + `assay_module_for/1`), so it never drifts out of sync.

**Files:**
- Modify: `lib/antigen/runner.ex` (add `replay_registry/0` immediately after `assay_module_for/1`, currently line 426)
- Test: `test/antigen/replay_registry_test.exs`

**Interfaces:**
- Consumes: `Runner.registered_assays/0 :: [String.t()]` (line 374), `Runner.assay_module_for/1 :: (String.t() -> module())` (line 426).
- Produces: `Runner.replay_registry/0 :: %{String.t() => module()}` — every registered assay id mapped to its module. Consumed by `Antigen.Prune` (Task 2).

- [ ] **Step 1: Write the failing test**

Create `test/antigen/replay_registry_test.exs`:

```elixir
defmodule Antigen.ReplayRegistryTest do
  @moduledoc """
  `Antigen.Runner.replay_registry/0` — the full assay id → module map, built from
  the authoritative dispatch table so it covers every registered assay (unlike the
  hardcoded subset in `corpus_replay_test`). This is the registry `Antigen.Prune`
  re-checks corpus records against.
  """
  use ExUnit.Case, async: true
  alias Antigen.Runner

  test "covers every registered assay and every value is a run/1 module" do
    reg = Runner.replay_registry()

    assert Enum.sort(Map.keys(reg)) == Enum.sort(Runner.registered_assays())
    assert map_size(reg) == length(Runner.registered_assays())

    for {_id, mod} <- reg do
      Code.ensure_loaded!(mod)
      assert function_exported?(mod, :run, 1)
    end

    # spot-check one known wiring against the dispatch table
    assert reg["totality/diverging"] == Antigen.Assays.Totality
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/replay_registry_test.exs`
Expected: FAIL with `(UndefinedFunctionError) function Antigen.Runner.replay_registry/0 is undefined`.

- [ ] **Step 3: Write minimal implementation**

In `lib/antigen/runner.ex`, immediately after `assay_module_for/1` (line 426), add:

```elixir
  @doc """
  The full assay replay registry: every registered assay id mapped to its module.
  Built from `registered_assays/0` + `assay_module_for/1`, so it stays in sync with
  the dispatch table automatically (unlike a hand-maintained literal). Consumers:
  `Antigen.Prune` (re-check each corpus record against the live kernel) and any
  replay driver that must cover *every* assay, not a hardcoded subset.
  """
  @spec replay_registry() :: %{String.t() => module()}
  def replay_registry do
    for id <- registered_assays(), into: %{}, do: {id, assay_module_for(id)}
  end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/replay_registry_test.exs`
Expected: PASS (1 test).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/runner.ex test/antigen/replay_registry_test.exs
git commit -m "feat(antigen): shared replay registry from the authoritative dispatch table"
```

---

### Task 2: Antibody prune — `Antigen.Prune.prune/3` + `Corpus.record_lines/1` promotion + `retired.sexp`

The core: walk a corpus's raw lines, decode+replay each, keep the still-valid ones (byte-identical), move the rest to a retirement store with a reason. Prune needs raw record lines (to preserve byte identity), so promote the private `Corpus.record_lines/1` that `merge/2` already uses.

**Files:**
- Modify: `lib/antigen/corpus.ex:150` (promote `defp record_lines` → public `def record_lines` with a doc)
- Create: `lib/antigen/prune.ex`
- Create: `test/antigen/retired.sexp` (empty, git-tracked retirement store)
- Test: `test/antigen/prune_test.exs`

**Interfaces:**
- Consumes: `Corpus.record_lines/1 :: (String.t() -> [String.t()])` (raw, newline-trimmed, blank-free), `Corpus.decode_record/1 :: (String.t() -> {:ok, Challenge.t()} | {:error, term()})`, `Runner.replay_registry/0` (Task 1), each assay module's `run/1 :: (Challenge.t() -> :ok | {:violation, term()})`.
- Produces: `Antigen.Prune.prune/3 :: (corpus_path, retired_path, registry \\ Runner.replay_registry()) -> %{kept: non_neg_integer(), retired: non_neg_integer(), reasons: [reason()]}` where each `reason` is a `{kind, detail}` tuple (`:decode_error | :unknown_assay | :label_drift | :replay_error | :unexpected`). Consumed by `mix antigen.prune` (Task 3).

- [ ] **Step 1: Write the failing test**

Create `test/antigen/prune_test.exs`:

```elixir
defmodule Antigen.PruneTest do
  @moduledoc """
  `Antigen.Prune.prune/3` — re-check antibody records against the live kernel via
  the shared replay registry; keep the ones that decode and replay `:ok`, move the
  rest verbatim to a retirement store with a reason. Never rewrites a term; a run
  that retires nothing leaves the corpus byte-identical. All I/O is on tmp copies
  (the committed stores are never touched).
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Prune, Runner}

  @tmp "tmp/antigen_prune_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp path(name), do: Path.join(@tmp, name)
  defp stub_rec(term), do: Corpus.encode_record(Challenge.stub(term))

  # A record that decodes cleanly but whose term uses a head the grammar rejects —
  # surgically swap the pieces field of a valid stub record (key= precedes pieces=
  # in the encoding, so the stored key stays intact).
  defp undecodable_rec do
    Regex.replace(~r/pieces=.*$/, stub_rec({:type, 7}), "pieces=t::(zzz_unknown_node 1)")
  end

  defp write(name, lines) do
    p = path(name)
    File.write!(p, Enum.join(lines, "\n") <> "\n")
    p
  end

  test "keeps a replay-:ok record and retires an undecodable one, with a reason" do
    keep = stub_rec({:type, 0})
    bad = undecodable_rec()
    corpus = write("corpus.sexp", [keep, bad])
    retired = path("retired.sexp")

    tally = Prune.prune(corpus, retired)

    assert tally.kept == 1
    assert tally.retired == 1
    assert [{:decode_error, _}] = tally.reasons

    # kept record survives byte-identically; the bad one is gone
    got = corpus |> File.read!() |> String.split("\n", trim: true)
    assert got == [keep]

    # the retired store carries the reason and the verbatim record
    retired_text = File.read!(retired)
    assert retired_text =~ "# retired: {:decode_error"
    assert retired_text =~ bad
  end

  test "retires a label-drift record (decodes, replays a non-:ok verdict)" do
    defmodule DriftAssay do
      def run(_c), do: {:violation, :drift}
    end

    rec = stub_rec({:type, 3})
    corpus = write("corpus.sexp", [rec])
    retired = path("retired.sexp")

    tally = Prune.prune(corpus, retired, %{"stub" => DriftAssay})

    assert tally.kept == 0
    assert [{:label_drift, :drift}] = tally.reasons
    assert File.read!(retired) =~ "# retired: {:label_drift, :drift}"
    assert File.read!(corpus) == ""
  end

  test "leaves an all-green corpus byte-identical and writes no retirement file" do
    a = stub_rec({:type, 1})
    b = stub_rec({:type, 2})
    corpus = write("corpus.sexp", [a, b])
    retired = path("retired.sexp")
    before = File.read!(corpus)

    tally = Prune.prune(corpus, retired, Runner.replay_registry())

    assert tally == %{kept: 2, retired: 0, reasons: []}
    assert File.read!(corpus) == before
    refute File.exists?(retired)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/prune_test.exs`
Expected: FAIL with `(UndefinedFunctionError) function Antigen.Prune.prune/3 is undefined` (and, if reached, `Corpus.record_lines/1 is undefined or private`).

- [ ] **Step 3a: Promote `Corpus.record_lines/1`**

In `lib/antigen/corpus.ex`, replace the private definition at line 150:

```elixir
  # Non-blank, newline-trimmed record lines of a file (empty list if the file is absent).
  defp record_lines(path) do
```

with a public, documented one (body unchanged):

```elixir
  @doc """
  Non-blank, newline-trimmed record lines of a file (empty list if the file is
  absent). Raw lines — no decode — so callers preserve byte identity. Used by
  `merge/2` and `Antigen.Prune`.
  """
  @spec record_lines(String.t()) :: [String.t()]
  def record_lines(path) do
```

- [ ] **Step 3b: Write the prune module**

Create `lib/antigen/prune.ex`:

```elixir
defmodule Antigen.Prune do
  @moduledoc """
  Antibody-corpus pruning across kernel shape changes (migration design, C2). Walks
  a corpus file, re-checks each record against the LIVE kernel via the shared replay
  registry, keeps the ones that still decode and replay `:ok`, and moves the rest
  **verbatim** to a retirement store, annotated with the reason. Never rewrites a
  term; never silently deletes. A run that retires nothing leaves the corpus
  byte-identical (idempotent).
  """
  alias Antigen.{Corpus, Runner}

  @type reason ::
          {:decode_error, term()}
          | {:unknown_assay, String.t()}
          | {:label_drift, term()}
          | {:replay_error, String.t()}
          | {:unexpected, term()}

  @type tally :: %{kept: non_neg_integer(), retired: non_neg_integer(), reasons: [reason()]}

  @doc """
  Prune `corpus_path`. Kept records (decode AND replay `:ok`) are rewritten back
  byte-identically; retired records are appended to `retired_path` with their reason.
  `registry` defaults to the full `Runner.replay_registry/0`.
  """
  @spec prune(String.t(), String.t(), %{String.t() => module()}) :: tally()
  def prune(corpus_path, retired_path, registry \\ Runner.replay_registry()) do
    {kept, retired} =
      corpus_path
      |> Corpus.record_lines()
      |> Enum.reduce({[], []}, fn line, {keep, ret} ->
        case classify(line, registry) do
          :keep -> {[line | keep], ret}
          {:retire, reason} -> {keep, [{line, reason} | ret]}
        end
      end)

    kept = Enum.reverse(kept)
    retired = Enum.reverse(retired)

    # Only rewrite when something was retired, so an all-green corpus is left
    # byte-identical (no spurious diff on a no-op run).
    unless retired == [], do: rewrite(corpus_path, kept)
    append_retired(retired_path, retired)

    %{kept: length(kept), retired: length(retired), reasons: Enum.map(retired, &elem(&1, 1))}
  end

  # decodes AND replays :ok → keep; anything else → retire with a reason.
  defp classify(line, registry) do
    case Corpus.decode_record(line) do
      {:error, reason} ->
        {:retire, {:decode_error, reason}}

      {:ok, c} ->
        case Map.fetch(registry, c.assay) do
          :error -> {:retire, {:unknown_assay, c.assay}}
          {:ok, mod} -> replay(mod, c)
        end
    end
  end

  defp replay(mod, c) do
    case apply(mod, :run, [c]) do
      :ok -> :keep
      {:violation, v} -> {:retire, {:label_drift, v}}
      other -> {:retire, {:unexpected, other}}
    end
  rescue
    e -> {:retire, {:replay_error, Exception.message(e)}}
  end

  # Atomically rewrite the corpus with only the kept (verbatim) lines.
  defp rewrite(path, kept) do
    tmp = path <> ".pruning"
    content = if kept == [], do: "", else: Enum.join(kept, "\n") <> "\n"
    File.write!(tmp, content)
    File.rename!(tmp, path)
  end

  defp append_retired(_path, []), do: :ok

  defp append_retired(path, retired) do
    File.mkdir_p!(Path.dirname(path))

    chunk =
      Enum.map_join(retired, "\n", fn {line, reason} ->
        "# retired: #{inspect(reason)}\n#{line}"
      end)

    File.write!(path, newline_guard(path) <> chunk <> "\n", [:append])
  end

  # A leading "\n" iff the file is non-empty and does not already end in one, so an
  # appended block can never glue onto a hand-edited last line.
  defp newline_guard(path) do
    case File.read(path) do
      {:ok, ""} -> ""
      {:ok, content} -> if String.ends_with?(content, "\n"), do: "", else: "\n"
      _ -> ""
    end
  end
end
```

- [ ] **Step 3c: Create the git-tracked retirement store**

```bash
: > test/antigen/retired.sexp
```

(Creates an empty `test/antigen/retired.sexp`. It is intentionally NOT in any replay scanner's file list — `corpus_atoms_test`'s `@corpora` and `corpus_replay_test`'s `[@corpus, @seeds]` both exclude it — so it stays out of the gate, per spec C3.)

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/prune_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/corpus.ex lib/antigen/prune.ex test/antigen/prune_test.exs test/antigen/retired.sexp
git commit -m "feat(antigen): prune stale antibodies to a retirement store, keep replay-:ok records"
```

---

### Task 3: `mix antigen.prune` CLI

Thin wrapper over `Antigen.Prune.prune/3` with the canonical path defaults and a printed tally.

**Files:**
- Create: `lib/mix/tasks/antigen.prune.ex`
- Test: `test/antigen/prune_task_test.exs`

**Interfaces:**
- Consumes: `Antigen.Prune.prune/3` (Task 2).
- Produces: `mix antigen.prune [--corpus PATH] [--retired PATH]` — invocable task; prints `antigen prune: N kept, M retired[ (kind×n, … → PATH)]`.

- [ ] **Step 1: Write the failing test**

Create `test/antigen/prune_task_test.exs`:

```elixir
defmodule Mix.Tasks.Antigen.PruneTest do
  use ExUnit.Case, async: true
  import ExUnit.CaptureIO
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_prune_task_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "runs prune on the given paths and prints a tally" do
    corpus = Path.join(@tmp, "corpus.sexp")
    retired = Path.join(@tmp, "retired.sexp")
    keep = Corpus.encode_record(Challenge.stub({:type, 0}))
    bad = Regex.replace(~r/pieces=.*$/, Corpus.encode_record(Challenge.stub({:type, 1})),
                        "pieces=t::(zzz_unknown_node 1)")
    File.write!(corpus, keep <> "\n" <> bad <> "\n")

    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.Prune.run(["--corpus", corpus, "--retired", retired])
      end)

    assert out =~ "antigen prune: 1 kept, 1 retired"
    assert File.read!(corpus) |> String.split("\n", trim: true) == [keep]
    assert File.read!(retired) =~ "# retired:"
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/prune_task_test.exs`
Expected: FAIL with `(UndefinedFunctionError) function Mix.Tasks.Antigen.Prune.run/1 is undefined` (module not defined).

- [ ] **Step 3: Write minimal implementation**

Create `lib/mix/tasks/antigen.prune.ex`:

```elixir
defmodule Mix.Tasks.Antigen.Prune do
  use Mix.Task

  @shortdoc "Prune stale antibodies from the Antigen corpus (retire the ones that no longer replay :ok)"

  @moduledoc """
  Re-check every record in the antibody corpus against the LIVE kernel. Records that
  still decode and replay `:ok` stay; the rest move to a retirement store, annotated
  with the reason (`:unknown_node` decode error, `unknown_assay`, a label-drift
  verdict, …). Never rewrites a term; never silently deletes. A run that retires
  nothing leaves the corpus byte-identical.

      mix antigen.prune [--corpus PATH] [--retired PATH]

  Defaults: corpus `test/antigen/corpus.sexp`, retired `test/antigen/retired.sexp`.
  Run after a kernel shape change, review the diff (what retired and why — for any
  retired guard that still matters, add or confirm a generator cell for its
  shape-class), then commit.
  """

  @switches [corpus: :string, retired: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, _, _} = OptionParser.parse(argv, strict: @switches)
    corpus = opts[:corpus] || "test/antigen/corpus.sexp"
    retired = opts[:retired] || "test/antigen/retired.sexp"

    tally = Antigen.Prune.prune(corpus, retired)

    detail =
      if tally.retired == 0 do
        ""
      else
        kinds =
          tally.reasons
          |> Enum.frequencies_by(&elem(&1, 0))
          |> Enum.map_join(", ", fn {kind, n} -> "#{kind}×#{n}" end)

        " (#{kinds} → #{retired})"
      end

    Mix.shell().info("antigen prune: #{tally.kept} kept, #{tally.retired} retired#{detail}")
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/prune_task_test.exs`
Expected: PASS (1 test).

- [ ] **Step 5: Commit**

```bash
git add lib/mix/tasks/antigen.prune.ex test/antigen/prune_task_test.exs
git commit -m "feat(antigen): mix antigen.prune CLI over the prune library"
```

---

### Task 4: Seed regeneration — `Antigen.Regen.regenerate_seeds/1`

Re-harvest coverage-novel seeds from the current generators into a fresh file, then atomically swap it over the destination ("replace, not append"). Reuses the existing harvest path (`Runner.generate/1`) and the explorer generator pool (`Mix.Tasks.Antigen.default_gen/0`).

**Files:**
- Create: `lib/antigen/regen.ex`
- Test: `test/antigen/regen_test.exs`

**Interfaces:**
- Consumes: `Runner.generate/1` (returns `%{seeds_banked: n}`, banks via coverage-dedup to `:seeds_path`), `Mix.Tasks.Antigen.default_gen/0`, `Antigen.Generators.SeedPool.load/1` (inert on a missing file).
- Produces: `Antigen.Regen.regenerate_seeds/1 :: (keyword() -> %{seeds_banked: non_neg_integer(), dest: String.t()})`. Opts: `:seeds_path` (default `"test/antigen/seeds.sexp"`), `:count` (default `20_000`), `:gen` (default `Mix.Tasks.Antigen.default_gen()`). Consumed by `mix antigen.regen_seeds` (Task 5).

- [ ] **Step 1: Write the failing test**

Create `test/antigen/regen_test.exs`:

```elixir
defmodule Antigen.RegenTest do
  @moduledoc """
  `Antigen.Regen.regenerate_seeds/1` — drop the stale seed pool and re-harvest
  coverage-novel seeds from the current generators into a fresh file, atomically
  replacing the old one. The regenerated pool must decode and replay clean. All I/O
  is on a tmp destination (the committed store is never touched).
  """
  use ExUnit.Case, async: true
  alias Antigen.{Regen, Runner}

  @tmp "tmp/antigen_regen_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "replaces (not appends) with a fresh, decodable, replay-clean pool" do
    dest = Path.join(@tmp, "seeds.sexp")
    File.write!(dest, "stale garbage line that must not survive\n")

    result =
      Regen.regenerate_seeds(
        seeds_path: dest,
        count: 60,
        gen: Antigen.Generators.Totality.gen()
      )

    assert result.dest == dest
    assert result.seeds_banked > 0

    # replace, not append: the stale line is gone
    refute File.read!(dest) =~ "stale garbage line"

    # every regenerated record decodes and replays :ok through the live kernel
    results = Runner.replay([dest], Runner.replay_registry())
    assert results != []
    assert Enum.all?(results, &(&1.verdict == :ok))
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/regen_test.exs`
Expected: FAIL with `(UndefinedFunctionError) function Antigen.Regen.regenerate_seeds/1 is undefined`.

- [ ] **Step 3: Write minimal implementation**

Create `lib/antigen/regen.ex`:

```elixir
defmodule Antigen.Regen do
  @moduledoc """
  Seed-pool regeneration across kernel shape changes (migration design, C1). Drops
  the stale seed pool and re-harvests coverage-novel seeds from the CURRENT
  generators into a fresh file, then atomically swaps it over the canonical store —
  "replace, not append". Undecodable old seeds are re-derived, never translated.
  Zero term-rewriting. Reuses the existing harvest path (`Runner.generate/1`) and
  explorer pool (`Mix.Tasks.Antigen.default_gen/0`).
  """
  alias Antigen.Runner

  @type result :: %{seeds_banked: non_neg_integer(), dest: String.t()}

  @spec regenerate_seeds(keyword()) :: result()
  def regenerate_seeds(opts \\ []) do
    dest = Keyword.get(opts, :seeds_path, "test/antigen/seeds.sexp")
    count = Keyword.get(opts, :count, 20_000)
    gen = Keyword.get(opts, :gen, Mix.Tasks.Antigen.default_gen())

    tmp = dest <> ".regen"
    File.rm(tmp)

    # Harvest into the fresh (empty) tmp with an inert filler pool loaded from it, so
    # the new pool is derived from the current generators — not primed by the stale
    # store we are about to discard.
    Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(tmp))
    %{seeds_banked: banked} = Runner.generate(gen: gen, count: count, seeds_path: tmp)

    # generate only creates the file once a seed banks; guarantee a file to swap so a
    # zero-yield run still produces a (correctly empty) fresh pool.
    File.exists?(tmp) || File.write!(tmp, "")
    File.rename!(tmp, dest)

    %{seeds_banked: banked, dest: dest}
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/regen_test.exs`
Expected: PASS (1 test).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/regen.ex test/antigen/regen_test.exs
git commit -m "feat(antigen): regenerate the seed pool from current generators (replace, not append)"
```

---

### Task 5: `mix antigen.regen_seeds` CLI

Thin wrapper over `Antigen.Regen.regenerate_seeds/1`.

> **Note:** Mix derives the task name from the module via underscore, so `Mix.Tasks.Antigen.RegenSeeds` is invoked as `mix antigen.regen_seeds`. The spec's prose `mix antigen.regen-seeds` (hyphen) is cosmetic; the underscore form is the actual command.

**Files:**
- Create: `lib/mix/tasks/antigen.regen_seeds.ex`
- Test: `test/antigen/regen_task_test.exs`

**Interfaces:**
- Consumes: `Antigen.Regen.regenerate_seeds/1` (Task 4).
- Produces: `mix antigen.regen_seeds [--count N] [--seeds PATH]` — invocable task; prints `antigen regen_seeds: N seed(s) harvested → PATH`.

- [ ] **Step 1: Write the failing test**

Create `test/antigen/regen_task_test.exs`:

```elixir
defmodule Mix.Tasks.Antigen.RegenSeedsTest do
  use ExUnit.Case, async: true
  import ExUnit.CaptureIO

  @tmp "tmp/antigen_regen_task_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "regenerates seeds into the given path and prints a tally" do
    dest = Path.join(@tmp, "seeds.sexp")

    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.RegenSeeds.run(["--seeds", dest, "--count", "40"])
      end)

    assert out =~ "antigen regen_seeds:"
    assert out =~ dest
    assert File.exists?(dest)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/regen_task_test.exs`
Expected: FAIL with `(UndefinedFunctionError) function Mix.Tasks.Antigen.RegenSeeds.run/1 is undefined`.

- [ ] **Step 3: Write minimal implementation**

Create `lib/mix/tasks/antigen.regen_seeds.ex`:

```elixir
defmodule Mix.Tasks.Antigen.RegenSeeds do
  use Mix.Task

  @shortdoc "Regenerate the Antigen seed pool from the current generators (replace, not append)"

  @moduledoc """
  Drop the stale seed pool and re-harvest coverage-novel seeds from the CURRENT
  generators into a fresh `seeds.sexp`, atomically replacing the old file. Stale /
  undecodable seeds are re-derived, never translated. Run after a kernel shape
  change; the replay gate (`corpus_replay_test`) then verifies the fresh pool decodes
  and replays clean.

      mix antigen.regen_seeds [--count N] [--seeds PATH]

  Defaults: count 20000, seeds `test/antigen/seeds.sexp`.
  """

  @switches [count: :integer, seeds: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, _, _} = OptionParser.parse(argv, strict: @switches)

    regen_opts =
      []
      |> put_opt(:seeds_path, opts[:seeds])
      |> put_opt(:count, opts[:count])

    %{seeds_banked: banked, dest: dest} = Antigen.Regen.regenerate_seeds(regen_opts)
    Mix.shell().info("antigen regen_seeds: #{banked} seed(s) harvested → #{dest}")
  end

  defp put_opt(kw, _key, nil), do: kw
  defp put_opt(kw, key, val), do: Keyword.put(kw, key, val)
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/regen_task_test.exs`
Expected: PASS (1 test).

- [ ] **Step 5: Commit**

```bash
git add lib/mix/tasks/antigen.regen_seeds.ex test/antigen/regen_task_test.exs
git commit -m "feat(antigen): mix antigen.regen_seeds CLI over the regen library"
```

---

### Task 6: End-to-end integration + gate verification

Prove the two tools together leave a corpus/seed pair in the exact state `corpus_replay_test` demands (all records decode + replay `:ok`), and confirm the existing gate is still green after the new code lands.

**Files:**
- Test: `test/antigen/prune_regen_integration_test.exs`

**Interfaces:**
- Consumes: `Antigen.Prune.prune/3`, `Antigen.Regen.regenerate_seeds/1`, `Runner.replay/2`, `Runner.replay_registry/0`.
- Produces: nothing (integration test only).

- [ ] **Step 1: Write the failing test**

Create `test/antigen/prune_regen_integration_test.exs`:

```elixir
defmodule Antigen.PruneRegenIntegrationTest do
  @moduledoc """
  End-to-end: prune a mixed corpus and regenerate a seed pool on tmp copies, then
  replay both through the live kernel exactly as `corpus_replay_test` does. Prune's
  keep-criterion IS that gate's criterion, so the post-run stores must be all-green
  by construction. The committed stores are never touched.
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Prune, Regen, Runner}

  @tmp "tmp/antigen_prune_regen_integration_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "after prune + regen, corpus and seeds both replay all-:ok (gate green by construction)" do
    corpus = Path.join(@tmp, "corpus.sexp")
    seeds = Path.join(@tmp, "seeds.sexp")
    retired = Path.join(@tmp, "retired.sexp")

    keep = Corpus.encode_record(Challenge.stub({:type, 0}))
    bad = Regex.replace(~r/pieces=.*$/, Corpus.encode_record(Challenge.stub({:type, 1})),
                        "pieces=t::(zzz_unknown_node 1)")
    File.write!(corpus, keep <> "\n" <> bad <> "\n")

    assert %{kept: 1, retired: 1} = Prune.prune(corpus, retired)
    assert %{seeds_banked: n} when n > 0 = Regen.regenerate_seeds(
             seeds_path: seeds, count: 60, gen: Antigen.Generators.Totality.gen())

    # the replay gate's own check: every remaining record decodes and replays :ok
    results = Runner.replay([corpus, seeds], Runner.replay_registry())
    assert results != []
    assert Enum.all?(results, &(&1.verdict == :ok)),
           "post-prune/regen stores are not all-green: " <>
             inspect(Enum.reject(results, &(&1.verdict == :ok)))
  end
end
```

- [ ] **Step 2: Run test to verify it fails, then passes**

Run: `mix test test/antigen/prune_regen_integration_test.exs`
Expected: PASS (1 test) — all consumed functions already exist from Tasks 1–5, so this is a green integration check. (If it fails, the failure localizes which prior task's contract broke.)

- [ ] **Step 3: Confirm the existing replay gate is still green**

Run: `mix test test/antigen/corpus_replay_test.exs test/antigen/cover_manifest_gate_test.exs`
Expected: PASS — the committed stores were never touched and the new registry is a superset of the old hardcoded one, so both gates stay green.

- [ ] **Step 4: Full Antigen suite regression check**

Run: `mix test test/antigen/`
Expected: PASS — no regressions across the Antigen suite.

- [ ] **Step 5: Commit**

```bash
git add test/antigen/prune_regen_integration_test.exs
git commit -m "test(antigen): end-to-end prune + regen leaves the replay gate green"
```

---

## Self-Review

**1. Spec coverage** (`docs/superpowers/specs/antigen/2026-07-10-antigen-migration-design.md`):
- C1 Regeneration (`mix antigen.regen-seeds`, replace-not-append, reuse generate path) → Tasks 4 + 5. ✓
- C2 Antibody prune (`mix antigen.prune`, keep-if-decodes-and-:ok, retire-with-reason, shared registry, never rewrite/silently-delete) → Tasks 1 + 2 + 3. ✓
- C3 Retirement store (`test/antigen/retired.sexp`, append-only, git-tracked, not gate-replayed) → Task 2 Step 3c (created empty + tracked; excluded from all scanner file lists). ✓
- C4 Verification via existing replay gate → Task 6 Step 3. ✓
- Testing list (keep+retire-undecodable, label-drift, idempotent no-op, regen decodable+clean, post-run gate green) → Tasks 2, 4, 6. ✓
- Non-goals (no rewrite engine / `schema=` / rule registry / seed migration / per-seed replay / in-test mutation of committed stores) → honored: no such code; Global Constraints pin git-clean tmp-only test I/O. ✓
- `reach.sexp` regeneration ("when non-empty") → currently 0 bytes (verified `-rw-r--r-- 0 reach.sexp`); it has no automated banking path (only test-driven pins), so the automated regen path is scoped to `seeds.sexp`. `regenerate_seeds/1` is path-parameterized, so a future reach generator reuses the same swap by passing `seeds_path: "test/antigen/reach.sexp"` with a reach gen. Documented, not gold-plated (YAGNI). ✓

**2. Placeholder scan:** No TBD/TODO/"handle edge cases"/"similar to Task N". Every code step shows complete code; every run step shows the exact command + expected result. ✓

**3. Type consistency:** `replay_registry/0 :: %{String.t() => module()}` (Task 1) is the exact type `prune/3`'s `registry` param and default consume (Task 2), and the exact map `Runner.replay/2` accepts in Tasks 4/6. `prune/3` returns `%{kept, retired, reasons}` — consumed identically by the CLI (Task 3, `tally.kept`/`tally.retired`/`tally.reasons`) and the integration test (Task 6). `regenerate_seeds/1` returns `%{seeds_banked, dest}` — consumed identically by the CLI (Task 5) and its test (Task 4). `Corpus.record_lines/1` signature matches its promoted body + its existing `merge/2` caller. Reason tuples are always `{kind, detail}`, so `elem(&1, 0)` in the CLI and `Enum.map(retired, &elem(&1, 1))` in prune are well-typed. ✓

---

## Execution Handoff

**Plan complete and saved to `docs/superpowers/plans/2026-07-10-antigen-prune-regenerate.md`. Two execution options:**

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration.

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints for review.

**Which approach?**
