# Transliteration Program P0 — audit + snapshot refresh + differential-oracle skeleton + ledger corrections

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land cluster **P0** of the Idris-transliteration program: refresh the reference snapshot, build the pinned `idris2`, stand up the differential-oracle harness with a first rewrite corpus, audit `rewrite_plan/5` against `elabRewrite`, and correct the parity ledger — all at near-zero port risk, calibrating the brief/oracle machinery for P1–P5.

**Architecture:** Follows the program charter [`2026-07-02-idris-transliteration-program-design.md`](../specs/roadmap/2026-07-02-idris-transliteration-program-design.md) §6 "P0" and §7 "differential oracle". P0 writes no port code except an audit-level delta in the untrusted elaborator (`Cure.Elab.Elaborator.rewrite_plan/5`); the kernel is untouched. The oracle is a two-mode harness (`live` regenerates fixtures from a pinned `idris2 --check`; `replay` asserts Cure's verdicts against committed fixtures with no Idris toolchain), enforcing a relation contract (`same` / `cure_stricter` / `idris_only`) where every divergence carries a written reason.

**Tech Stack:** Elixir (Cure compiler + Mix tasks), ExUnit, Elixir 1.20 bundled `JSON` module (no new dep), the pinned `idris2` (Chez backend), Idris 2 / Agda vendored reference sources under `~/Develop/esp32-beam/reference/`.

## Global Constraints

- **Ghost-writer commits.** Every commit uses `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, **no** `Co-Authored-By` trailer, no Claude signature.
- **Explicit staging only.** A concurrent session works in this same worktree. NEVER `git add -A` / `git add .`. Stage each file by exact path (`git add -- <path>`), and commit with an explicit pathspec (`git commit -- <path>…`) so another agent's pre-staged files are never swept into our commit.
- **One build/test run at a time.** Never launch concurrent `mix` suites — a past concurrent full-suite run caused a kernel panic. Serialize every `mix test` / `mix compile`.
- **writing-plans format.** Checkbox steps, complete code in every code step, no placeholders, exact commands with expected output.
- **Repo split.** Task 1's commit lands in the **esp32-beam** repo (`~/Develop/esp32-beam`), because `reference/` lives there and only `MANIFEST.md` is tracked (sources are gitignored). **Every other task commits in the cure-lang worktree** (`~/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0`, branch `autopilot/transliteration-p0`).
- **Compile Cure with OTP 26–28.** Entry point convention is `start/0`, not `main/0` (not exercised here, but the house rule).
- **Audit-first (charter D5).** Verify each ledger claim against the tree before writing code; update the ledger after.
- **Red-green TDD (`~/agent_docs/testing.md`).** Every behavioral delta gets a failing test first, then the fix.
- **Tests are immutable once green.** Once a test written under this plan (Tasks 3/4/5's unit, replay, and audit tests) correctly encodes the intended behavior and passes, make it green only by changing implementation code — never by deleting, skipping, or weakening the test's assertions to fit whatever the code currently does. The sole exception: the test itself is proven wrong (it encodes an incorrect expectation) — in that case state explicitly why before touching it.
- **Oracle triage rule.** Never hand-edit a generated verdict. A new divergence defaults to relation `same` so replay fails loudly and forces triage. `Cure-rejects-where-Idris-accepts` routes into Task 5's audit; it is not silenced with a `cure_stricter` label unless the audit confirms the divergence is a deliberate, documented Cure restriction.

**Absolute paths used throughout:**
- Worktree (cure-lang): `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0` — henceforth `$WT`.
- esp32-beam repo root: `/Users/ch/Develop/esp32-beam` — henceforth `$BEAM`.
- Reference tree: `$BEAM/reference`. Idris2 clone: `/Users/ch/Develop/Idris2`. Agda clone: `/Users/ch/Develop/agda`.

---

### Task 1: Snapshot refresh + manifest (esp32-beam repo)

Refresh the pinned reference snapshot with the three files P2/P4 need (charter finding 5), and record them in the tracked manifest. This is the only task that commits in `$BEAM`.

**Files:**
- Create (copy, gitignored — not committed): `$BEAM/reference/idris2/src/TTImp/WithClause.idr`, `$BEAM/reference/idris2/src/TTImp/Elab/Case.idr`, `$BEAM/reference/agda/src/full/Agda/TypeChecking/With.hs`
- Modify (tracked — committed): `$BEAM/reference/MANIFEST.md`

**Interfaces:**
- Produces: three vendored source files at the paths above (consumed by P2/P4 briefs, not by P0 code), plus manifest section-E entries + a refresh-log line recording this snapshot event.

- [ ] **Step 1: Verify the clone pins match the manifest before copying**

Run:
```bash
git -C /Users/ch/Develop/Idris2 rev-parse --short=9 HEAD
git -C /Users/ch/Develop/agda rev-parse --short=10 HEAD
```
Expected: `fd405085b` for Idris2 and `7273757e5e` for Agda (the pins in `$BEAM/reference/MANIFEST.md` Provenance table). If either differs, STOP — the snapshot would not be reproducible against the recorded pin (charter risk "Reference drift"); report the mismatch rather than copying drifted sources.

- [ ] **Step 2: Copy the three gap files idempotently**

Run:
```bash
set -e
mkdir -p /Users/ch/Develop/esp32-beam/reference/idris2/src/TTImp/Elab
mkdir -p /Users/ch/Develop/esp32-beam/reference/agda/src/full/Agda/TypeChecking
for pair in \
  "/Users/ch/Develop/Idris2/src/TTImp/WithClause.idr:/Users/ch/Develop/esp32-beam/reference/idris2/src/TTImp/WithClause.idr" \
  "/Users/ch/Develop/Idris2/src/TTImp/Elab/Case.idr:/Users/ch/Develop/esp32-beam/reference/idris2/src/TTImp/Elab/Case.idr" \
  "/Users/ch/Develop/agda/src/full/Agda/TypeChecking/With.hs:/Users/ch/Develop/esp32-beam/reference/agda/src/full/Agda/TypeChecking/With.hs"; do
  src="${pair%%:*}"; dst="${pair##*:}"
  if cmp -s "$src" "$dst" 2>/dev/null; then echo "unchanged: $dst"; else cp "$src" "$dst"; echo "copied: $dst"; fi
done
```
Expected: three `copied:` (first run) or `unchanged:` (idempotent re-run) lines, no errors.

- [ ] **Step 3: Verify the copies landed and are gitignored**

Run:
```bash
wc -l /Users/ch/Develop/esp32-beam/reference/idris2/src/TTImp/WithClause.idr \
      /Users/ch/Develop/esp32-beam/reference/idris2/src/TTImp/Elab/Case.idr \
      /Users/ch/Develop/esp32-beam/reference/agda/src/full/Agda/TypeChecking/With.hs
git -C /Users/ch/Develop/esp32-beam status --short -- reference/
```
Expected: three non-zero line counts; `git status` shows **only** `reference/MANIFEST.md` as modified once Step 4 runs — the three sources must NOT appear (they are covered by `reference/`'s gitignore of source trees). If a source file appears as untracked, STOP: the gitignore is not covering it and committing would vendor third-party code.

- [ ] **Step 4: Add the three files to MANIFEST.md section E and append a refresh log**

In `$BEAM/reference/MANIFEST.md`, extend section **E** (`### E. Dependent pattern matching (case trees) + index unification + coverage`) so its `idris2:` and `agda:` bullets name the new files. Replace the two existing bullets:
```markdown
- idris2: `src/Core/Case/CaseBuilder.idr`, `Case/CaseTree.idr`, `Core/Coverage.idr`
- agda: `TypeChecking/Rules/LHS.hs`, `Rules/LHS/Unify.hs`, `Rules/LHS/Problem.hs`, `TypeChecking/Coverage.hs` ← **primary reference** for index unification
```
with:
```markdown
- idris2: `src/Core/Case/CaseBuilder.idr`, `Case/CaseTree.idr`, `Core/Coverage.idr`, `src/TTImp/Elab/Case.idr` (expression-level `case` elaboration → match lifting, P2), `src/TTImp/WithClause.idr` (`with`-clause desugaring, P4)
- agda: `TypeChecking/Rules/LHS.hs`, `Rules/LHS/Unify.hs`, `Rules/LHS/Problem.hs`, `TypeChecking/Coverage.hs` ← **primary reference** for index unification; `TypeChecking/With.hs` (with-abstraction, P4 cross-check)
```
Then append a new section at the end of the file (after the Caveats section):
```markdown

## Refresh log
- 2026-07-02 — added section-E gap files for the transliteration program (P2/P4 prerequisites): `idris2/src/TTImp/Elab/Case.idr`, `idris2/src/TTImp/WithClause.idr`, `agda/src/full/Agda/TypeChecking/With.hs`. Pins unchanged (Idris2 `fd405085b`, Agda `7273757e5e`).
```

- [ ] **Step 5: Structural verification (the red-analog for this docs task)**

Run:
```bash
grep -c "TTImp/Elab/Case.idr\|TTImp/WithClause.idr" /Users/ch/Develop/esp32-beam/reference/MANIFEST.md
grep -c "TypeChecking/With.hs" /Users/ch/Develop/esp32-beam/reference/MANIFEST.md
grep -c "^## Refresh log" /Users/ch/Develop/esp32-beam/reference/MANIFEST.md
```
Expected: first `grep -c` ≥ `2`, second ≥ `1`, third `= 1`. (The With.hs count is ≥1 because the existing text may already mention it elsewhere; the section-E bullet is the required addition.)

- [ ] **Step 6: Commit (esp32-beam repo, explicit pathspec, ghost author)**

Run:
```bash
cd /Users/ch/Develop/esp32-beam
git add -- reference/MANIFEST.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "reference: vendor with-clause/case-elab/agda-with gap files; manifest §E + refresh log" \
  -- reference/MANIFEST.md
git log --oneline -1
```
Expected: one commit containing only `reference/MANIFEST.md`.

---

### Task 2: Build the pinned `idris2` toolchain (idempotent, no repo change)

The oracle's `live` mode needs an `idris2` binary built from the pinned clone. The machine has neither `idris2` nor Chez Scheme. This task builds them; it commits nothing.

**Files:** none tracked. Produces the executable `/Users/ch/Develop/Idris2/build/exec/idris2`.

**Interfaces:**
- Produces: `/Users/ch/Develop/Idris2/build/exec/idris2` (consumed by Task 3's `Cure.Oracle.idris_verdict/2` default and Task 4's live regen).

- [ ] **Step 1: Skip-if-present guard (idempotency)**

Run:
```bash
if /Users/ch/Develop/Idris2/build/exec/idris2 --version >/dev/null 2>&1; then
  echo "SKIP: idris2 already built"; /Users/ch/Develop/Idris2/build/exec/idris2 --version
else
  echo "BUILD-NEEDED"
fi
```
If it prints `SKIP`, mark Steps 2–4 done and go to Task 3. Otherwise continue.

- [ ] **Step 2: Install Chez Scheme (Idris2's default backend)**

Run:
```bash
brew list chezscheme >/dev/null 2>&1 && echo "chezscheme present" || brew install chezscheme
which chez scheme 2>/dev/null || true
```
Expected: `chezscheme present`, or a completed `brew install`. Homebrew installs the binary as `chez` (some formulae as `scheme`); note whichever exists for Step 3.

- [ ] **Step 3: Bootstrap-build idris2 from the pinned clone**

Run:
```bash
cd /Users/ch/Develop/Idris2
CPATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib make bootstrap SCHEME=chez
```
(If Step 2 showed the binary is `scheme`, use `SCHEME=scheme`.) The `CPATH`/`LIBRARY_PATH` exports point the bootstrap C compile at Homebrew's `gmp` — without them the build fails with `gmp.h: No such file or directory` on a Homebrew-only macOS toolchain (empirically confirmed on this machine). Expected: a long build ending without error. This is a heavy, single build — do not run any other `mix`/`make` build concurrently (global constraint).

- [ ] **Step 4: Verify the binary runs**

Run:
```bash
/Users/ch/Develop/Idris2/build/exec/idris2 --version
```
Expected: a version line (e.g. `Idris 2, version 0.7.0-...`). If it fails, STOP and report — the oracle's live mode cannot run without it (replay mode, Tasks 3–4, still works offline).

---

### Task 3: Oracle harness — `Cure.Oracle` + `mix cure.oracle` (cure-lang worktree)

Stand up the differential-oracle skeleton (charter §7). Discovery, both verdict functions, fixture I/O, and the relation contract live in `Cure.Oracle`; the live regen driver is a Mix task; the contract logic is unit-tested red-green.

**Files:**
- Create: `$WT/lib/cure/oracle.ex`
- Create: `$WT/lib/mix/tasks/cure.oracle.ex`
- Test: `$WT/test/cure/oracle_test.exs`

**Interfaces:**
- Produces:
  - `Cure.Oracle.clusters() :: [String.t()]` — cluster names (subdirs of `test/oracle/`).
  - `Cure.Oracle.pairs(cluster :: String.t()) :: [%{name: String.t(), cure_path: String.t(), idr_path: String.t()}]`
  - `Cure.Oracle.cure_verdict(cure_path :: String.t()) :: :accept | :reject`
  - `Cure.Oracle.idris_verdict(bin :: String.t(), idr_path :: String.t()) :: :accept | :reject`
  - `Cure.Oracle.read_fixture(cluster :: String.t()) :: %{String.t() => map()}`
  - `Cure.Oracle.write_fixture(cluster :: String.t(), map()) :: :ok`
  - `Cure.Oracle.consistent(entry :: map()) :: :ok | {:error, term()}`
  - `Cure.Oracle.default_idris_bin() :: String.t()`
- Consumes: `Cure.Elab.Program.elaborate/1` (returns `{:ok, Env.t()} | {:error, term()}`), Elixir 1.20 `JSON`.

- [ ] **Step 1: Write the failing unit test for the relation contract + Cure verdict**

Create `$WT/test/cure/oracle_test.exs`:
```elixir
defmodule Cure.OracleTest do
  use ExUnit.Case, async: true
  alias Cure.Oracle

  describe "consistent/1 — the relation contract" do
    test "same: agreeing verdicts are consistent" do
      assert Oracle.consistent(%{"cure" => "accept", "idris" => "accept", "relation" => "same", "reason" => ""}) == :ok
      assert Oracle.consistent(%{"cure" => "reject", "idris" => "reject", "relation" => "same", "reason" => ""}) == :ok
    end

    test "same: disagreeing verdicts are inconsistent (forces triage)" do
      assert {:error, _} =
               Oracle.consistent(%{"cure" => "reject", "idris" => "accept", "relation" => "same", "reason" => ""})
    end

    test "cure_stricter: idris-accept/cure-reject with a reason is consistent" do
      assert Oracle.consistent(%{
               "cure" => "reject",
               "idris" => "accept",
               "relation" => "cure_stricter",
               "reason" => "Cure's fixed 0-2 universe hierarchy rejects this."
             }) == :ok
    end

    test "cure_stricter without a reason is inconsistent" do
      assert {:error, _} =
               Oracle.consistent(%{"cure" => "reject", "idris" => "accept", "relation" => "cure_stricter", "reason" => ""})
    end

    test "cure-accept/idris-reject is never benign — no relation label rescues it" do
      for rel <- ["same", "cure_stricter", "idris_only"] do
        assert {:error, _} =
                 Oracle.consistent(%{"cure" => "accept", "idris" => "reject", "relation" => rel, "reason" => "x"})
      end
    end
  end

  describe "cure_verdict/1" do
    test "accepts a well-typed program and rejects an ill-typed one" do
      good = Path.join(System.tmp_dir!(), "oracle_good_#{System.unique_integer([:positive])}.cure")
      bad = Path.join(System.tmp_dir!(), "oracle_bad_#{System.unique_integer([:positive])}.cure")

      File.write!(good, """
      type Nat = Z | S(Nat)
      fn zero_refl() -> Eq(Nat, Z, Z) = refl(Z)
      """)

      File.write!(bad, """
      type Nat = Z | S(Nat)
      fn bad() -> Eq(Nat, Z, S(Z)) = refl(Z)
      """)

      assert Oracle.cure_verdict(good) == :accept
      assert Oracle.cure_verdict(bad) == :reject
    after
      # tmp files are unique-per-run; explicit cleanup keeps tmp tidy
      :ok
    end
  end
end
```

- [ ] **Step 2: Run it and confirm it fails (module undefined)**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/cure/oracle_test.exs`
Expected: FAIL — `Cure.Oracle.__info__/1 is undefined (module Cure.Oracle is not available)`.

- [ ] **Step 3: Implement `Cure.Oracle`**

Create `$WT/lib/cure/oracle.ex`:
```elixir
defmodule Cure.Oracle do
  @moduledoc """
  Differential oracle for the transliteration program (design spec §7).

  Compares a corpus of paired programs — the same program in Idris surface
  syntax (`.idr`) and Cure surface syntax (`.cure`) — as accept/reject verdicts.
  Two modes: `live` (regenerates `verdicts.json` from `idris2 --check`, driven by
  `mix cure.oracle`) and `replay` (asserts Cure's current verdicts against the
  committed fixtures, no Idris toolchain — `test/oracle_replay_test.exs`).

  The contract is a *relation*, not equality: `same` (default), `cure_stricter`,
  or `idris_only`. Every divergence must carry a written reason; a divergence
  with no recorded reason fails `consistent/1`.
  """

  @root "test/oracle"

  @doc "Cluster names: immediate subdirectories of `test/oracle/`."
  @spec clusters() :: [String.t()]
  def clusters do
    case File.ls(@root) do
      {:ok, entries} -> entries |> Enum.filter(&File.dir?(Path.join(@root, &1))) |> Enum.sort()
      {:error, _} -> []
    end
  end

  @doc "Paired `.cure`/`.idr` probes in a cluster, keyed by shared basename."
  @spec pairs(String.t()) :: [%{name: String.t(), cure_path: String.t(), idr_path: String.t()}]
  def pairs(cluster) do
    dir = Path.join(@root, cluster)

    dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.map(fn cure_path ->
      name = Path.basename(cure_path, ".cure")
      %{name: name, cure_path: cure_path, idr_path: Path.join(dir, name <> ".idr")}
    end)
  end

  @doc "Cure's verdict: does the program elaborate?"
  @spec cure_verdict(String.t()) :: :accept | :reject
  def cure_verdict(cure_path) do
    case Cure.Elab.Program.elaborate(File.read!(cure_path)) do
      {:ok, _env} -> :accept
      {:error, _reason} -> :reject
    end
  end

  @doc """
  Idris' verdict via `idris2 --check`. The `.idr` is copied into a fresh
  throwaway directory and checked from there, so Idris' `build/` artifacts
  (which it writes into the current working directory) never pollute the repo.
  `IDRIS2_PATH` is set to the Prelude/base `.ttc` trees (see `idris_lib_path/1`)
  so `--check` resolves the standard library without a global `make install` —
  without this, every probe fails with "Module Prelude not found" and would
  false-`:reject`. An explicit `$IDRIS2_PATH` in the environment wins if set.
  """
  @spec idris_verdict(String.t(), String.t()) :: :accept | :reject
  def idris_verdict(bin, idr_path) do
    work = Path.join(System.tmp_dir!(), "cure_oracle_#{System.unique_integer([:positive])}")
    File.mkdir_p!(work)
    base = Path.basename(idr_path)
    File.cp!(idr_path, Path.join(work, base))

    env =
      case System.get_env("IDRIS2_PATH") || idris_lib_path(bin) do
        nil -> []
        path -> [{"IDRIS2_PATH", path}]
      end

    try do
      {_out, status} =
        System.cmd(bin, ["--check", base], cd: work, env: env, stderr_to_stdout: true)

      if status == 0, do: :accept, else: :reject
    after
      File.rm_rf(work)
    end
  end

  # The Prelude/base `.ttc` search path derived from the idris2 binary's
  # location (`.../build/exec/idris2` → `.../libs/{prelude,base}/build/ttc`).
  # We `make bootstrap` the clone but never `make install`, so the stdlib lives
  # only in the build tree. Returns nil when those dirs are absent (e.g. a
  # system-installed idris2 that already knows its own Prelude path).
  @spec idris_lib_path(String.t()) :: String.t() | nil
  defp idris_lib_path(bin) do
    root = bin |> Path.dirname() |> Path.dirname() |> Path.dirname()
    prelude = Path.join([root, "libs", "prelude", "build", "ttc"])
    base = Path.join([root, "libs", "base", "build", "ttc"])

    if File.dir?(prelude) and File.dir?(base) do
      Enum.join([prelude, base], ":")
    else
      nil
    end
  end

  @doc "Default Idris binary: `$IDRIS2_BIN` or the pinned clone's build output."
  @spec default_idris_bin() :: String.t()
  def default_idris_bin do
    System.get_env("IDRIS2_BIN") ||
      Path.expand("~/Develop/Idris2/build/exec/idris2")
  end

  @doc "Read a cluster's committed fixture map (name => entry). Empty if absent."
  @spec read_fixture(String.t()) :: %{String.t() => map()}
  def read_fixture(cluster) do
    path = fixture_path(cluster)

    case File.read(path) do
      {:ok, body} -> JSON.decode!(body)
      {:error, _} -> %{}
    end
  end

  @doc "Write a cluster's fixture map as JSON."
  @spec write_fixture(String.t(), %{String.t() => map()}) :: :ok
  def write_fixture(cluster, fixture) do
    File.write!(fixture_path(cluster), JSON.encode!(fixture) <> "\n")
  end

  @doc "The relation contract. See moduledoc."
  @spec consistent(map()) :: :ok | {:error, term()}
  def consistent(%{"relation" => "same", "cure" => v, "idris" => v}), do: :ok

  def consistent(%{"relation" => rel, "idris" => "accept", "cure" => "reject", "reason" => reason})
      when rel in ["cure_stricter", "idris_only"] and is_binary(reason) and reason != "",
      do: :ok

  def consistent(entry), do: {:error, {:relation_violated, entry}}

  defp fixture_path(cluster), do: Path.join([@root, cluster, "verdicts.json"])
end
```

- [ ] **Step 4: Run the unit test — expect green**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/cure/oracle_test.exs`
Expected: PASS (all `Cure.OracleTest` tests). If `JSON` is undefined, the Elixir version is < 1.20 — STOP and report (the plan assumes the bundled `JSON`; do not add a dep without escalation).

- [ ] **Step 5: Implement the `mix cure.oracle` live-regen driver**

Create `$WT/lib/mix/tasks/cure.oracle.ex`:
```elixir
defmodule Mix.Tasks.Cure.Oracle do
  @shortdoc "Regenerate differential-oracle fixtures (live mode; needs idris2)"
  @moduledoc """
  Live mode of the differential oracle (design spec §7). For every cluster under
  `test/oracle/`, run each `.cure` through Cure and each `.idr` through
  `idris2 --check`, then rewrite that cluster's `verdicts.json`.

  Binary: `$IDRIS2_BIN`, else `~/Develop/Idris2/build/exec/idris2`.

  Regeneration PRESERVES prior `relation`/`reason` fields. A brand-new pair gets
  `relation: "same"` deliberately, so if its verdicts diverge, `replay` fails
  loudly and forces a human to triage (never hand-edit a verdict).

  Usage:
      mix cure.oracle            # all clusters
      mix cure.oracle rewrite    # one cluster
  """
  use Mix.Task
  alias Cure.Oracle

  @impl Mix.Task
  def run(argv) do
    Mix.Task.run("app.start")
    bin = Oracle.default_idris_bin()

    unless File.exists?(bin) do
      Mix.raise("idris2 not found at #{bin} — build it (plan Task 2) or set $IDRIS2_BIN")
    end

    clusters = if argv == [], do: Oracle.clusters(), else: argv

    for cluster <- clusters do
      prior = Oracle.read_fixture(cluster)

      fixture =
        for %{name: name, cure_path: cp, idr_path: ip} <- Oracle.pairs(cluster), into: %{} do
          base = Map.get(prior, name, %{"relation" => "same", "reason" => ""})

          entry = %{
            "cure" => Atom.to_string(Oracle.cure_verdict(cp)),
            "idris" => Atom.to_string(Oracle.idris_verdict(bin, ip)),
            "relation" => Map.get(base, "relation", "same"),
            "reason" => Map.get(base, "reason", "")
          }

          Mix.shell().info(
            "#{cluster}/#{name}: cure=#{entry["cure"]} idris=#{entry["idris"]} " <>
              "rel=#{entry["relation"]}#{if Oracle.consistent(entry) == :ok, do: "", else: "  <-- TRIAGE"}"
          )

          {name, entry}
        end

      Oracle.write_fixture(cluster, fixture)
      Mix.shell().info("wrote #{Path.join(["test/oracle", cluster, "verdicts.json"])}")
    end
  end
end
```

- [ ] **Step 6: Verify the task compiles and is discoverable**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix compile 2>&1 | tail -5 && mix help cure.oracle`
Expected: clean compile; `mix help cure.oracle` prints the moduledoc. (Do not run `mix cure.oracle` yet — no corpus exists; that is Task 4.)

- [ ] **Step 7: Commit (explicit pathspec, ghost author)**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
git add -- lib/cure/oracle.ex lib/mix/tasks/cure.oracle.ex test/cure/oracle_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): differential-oracle harness (discovery, verdicts, relation contract, live regen)" \
  -- lib/cure/oracle.ex lib/mix/tasks/cure.oracle.ex test/cure/oracle_test.exs
```
Expected: one commit with exactly those three files.

---

### Task 4: Rewrite corpus + replay test + live regen/triage (cure-lang worktree)

Author seven paired rewrite probes, add the offline replay test, run live regen to populate verdicts, and triage. Corpus files are full `mod … end` programs (unwrapped by `Program.elaborate/1`); `.idr` files carry `%default total` (charter §7, totality-by-default parity) and omit a `module` line (default `Main`, so an absolute `--check` path never triggers a module-path mismatch).

**Files:**
- Create: `$WT/test/oracle/rewrite/rw01_plus_zero_right.{cure,idr}` … `rw07_conv_occurrence.{cure,idr}` (7 pairs)
- Create (generated by Step 9): `$WT/test/oracle/rewrite/verdicts.json`
- Test: `$WT/test/oracle_replay_test.exs`

**Interfaces:**
- Consumes: all of `Cure.Oracle` (Task 3), the built `idris2` (Task 2).

- [ ] **Step 1: Write the failing replay test**

Create `$WT/test/oracle_replay_test.exs`:
```elixir
defmodule OracleReplayTest do
  @moduledoc """
  Offline replay of the differential oracle (design spec §7). Needs no Idris
  toolchain: it asserts Cure's *current* verdicts against the committed
  fixtures and enforces the relation contract. Fixtures are regenerated with
  `mix cure.oracle` (live mode).
  """
  use ExUnit.Case, async: true
  alias Cure.Oracle

  test "there is at least one oracle cluster to replay" do
    assert Oracle.clusters() != [], "no clusters under test/oracle/ — corpus missing"
  end

  for cluster <- Cure.Oracle.clusters() do
    describe "oracle cluster: #{cluster}" do
      @cluster cluster

      test "fixture keys match the paired files exactly" do
        fixture_keys = @cluster |> Oracle.read_fixture() |> Map.keys() |> MapSet.new()
        pair_keys = @cluster |> Oracle.pairs() |> Enum.map(& &1.name) |> MapSet.new()
        assert fixture_keys == pair_keys
      end

      test "every pair has its .idr sibling, Cure's live verdict matches the fixture, and the relation holds" do
        fixture = Oracle.read_fixture(@cluster)

        for %{name: name, cure_path: cp, idr_path: ip} <- Oracle.pairs(@cluster) do
          entry = Map.fetch!(fixture, name)
          assert File.exists?(ip), "missing paired .idr for #{@cluster}/#{name}"
          assert Atom.to_string(Oracle.cure_verdict(cp)) == entry["cure"],
                 "Cure verdict drifted for #{@cluster}/#{name} — regenerate with `mix cure.oracle #{@cluster}`"
          assert Oracle.consistent(entry) == :ok,
                 "relation contract violated for #{@cluster}/#{name}: #{inspect(entry)}"
        end
      end
    end
  end
end
```

- [ ] **Step 2: Run it and confirm it fails (no corpus)**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/oracle_replay_test.exs`
Expected: FAIL on `there is at least one oracle cluster to replay` (no `test/oracle/` yet).

- [ ] **Step 3: rw01 — plus_zero_right (expected accept/accept)**

Create `$WT/test/oracle/rewrite/rw01_plus_zero_right.cure`:
```
mod Rw01
  type Nat = Z | S(Nat)
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  fn plus_zero_right(n: Nat) -> Eq(Nat, plus(n, Z), n) = match n
    Z() -> refl(Z)
    S(k) -> rewrite plus_zero_right(k) in refl(S(k))
end
```
Create `$WT/test/oracle/rewrite/rw01_plus_zero_right.idr`:
```idris
%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl
```

- [ ] **Step 4: rw02 — symmetry-goal `Eq(Nat, n, plus(n, Z))` (probes the symmetry branch)**

Create `$WT/test/oracle/rewrite/rw02_symmetry_goal.cure`:
```
mod Rw02
  type Nat = Z | S(Nat)
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  fn plus_zero_right_sym(n: Nat) -> Eq(Nat, n, plus(n, Z)) = match n
    Z() -> refl(Z)
    S(k) -> rewrite plus_zero_right_sym(k) in refl(S(k))
end
```
Create `$WT/test/oracle/rewrite/rw02_symmetry_goal.idr`:
```idris
%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRightSym : (n : N) -> n = plus n Z
plusZeroRightSym Z = Refl
plusZeroRightSym (S k) = rewrite plusZeroRightSym k in Refl
```

- [ ] **Step 5: rw03 — no-occurrence (expected reject/reject: `RewriteNoChange`)**

Create `$WT/test/oracle/rewrite/rw03_no_occurrence.cure`:
```
mod Rw03
  type Nat = Z | S(Nat)
  fn no_occurrence(p: Eq(Nat, Z, Z), m: Nat) -> Eq(Nat, m, m) = rewrite p in refl(m)
end
```
Create `$WT/test/oracle/rewrite/rw03_no_occurrence.idr`:
```idris
%default total

data N = Z | S N

noOccurrence : (p : the N Z = Z) -> (m : N) -> m = m
noOccurrence p m = rewrite p in Refl
```

- [ ] **Step 6: rw04 — plus_comm double-rewrite stress (`rewrite … in rewrite … in Refl`)**

Create `$WT/test/oracle/rewrite/rw04_plus_comm.cure`:
```
mod Rw04
  type Nat = Z | S(Nat)
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  fn plus_zero_right(n: Nat) -> Eq(Nat, plus(n, Z), n) = match n
    Z() -> refl(Z)
    S(k) -> rewrite plus_zero_right(k) in refl(S(k))
  fn plus_succ_right(m: Nat, n: Nat) -> Eq(Nat, plus(m, S(n)), S(plus(m, n))) = match m
    Z() -> refl(S(n))
    S(k) -> rewrite plus_succ_right(k, n) in refl(S(plus(k, S(n))))
  fn plus_comm(m: Nat, n: Nat) -> Eq(Nat, plus(m, n), plus(n, m)) = match m
    Z() -> rewrite plus_zero_right(n) in refl(n)
    S(k) -> rewrite plus_succ_right(n, k) in rewrite plus_comm(k, n) in refl(S(plus(k, n)))
end
```
Create `$WT/test/oracle/rewrite/rw04_plus_comm.idr`:
```idris
%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

plusSuccRight : (m : N) -> (n : N) -> plus m (S n) = S (plus m n)
plusSuccRight Z n = Refl
plusSuccRight (S k) n = rewrite plusSuccRight k n in Refl

plusComm : (m : N) -> (n : N) -> plus m n = plus n m
plusComm Z n = rewrite plusZeroRight n in Refl
plusComm (S k) n = rewrite plusSuccRight n k in rewrite plusComm k n in Refl
```

- [ ] **Step 7: rw05 — rewrite with a non-`Eq` proof (expected reject: `NotRewriteRule`)**

Create `$WT/test/oracle/rewrite/rw05_non_eq_proof.cure`:
```
mod Rw05
  type Nat = Z | S(Nat)
  fn non_eq_proof(n: Nat, m: Nat) -> Eq(Nat, m, m) = rewrite n in refl(m)
end
```
Create `$WT/test/oracle/rewrite/rw05_non_eq_proof.idr`:
```idris
%default total

data N = Z | S N

nonEqProof : (n : N) -> (m : N) -> m = m
nonEqProof n m = rewrite n in Refl
```

- [ ] **Step 8: rw06 — restated zero-right via an extra rewrite layer (expected accept/accept) and rw07 — conversion-occurrence probe**

`rw06` deliberately does *not* pair a wrong Cure proof against a correct Idris one: a `.cure`/`.idr` pair with different proof bodies for the same signature would not be a faithful transliteration, and its divergence would tell Task 5's audit nothing about `rewrite_plan/5` vs `elabRewrite` (it would just be a probe-authoring bug being triaged as if it were a language gap). Instead `rw06` restates `plus_zero_right` through an extra `rewrite`, so the rewritten goal is `n = n` on both sides — a same/same accept regression pair, matching Idris' `restatedZeroRight n = rewrite plusZeroRight n in Refl` (`Refl`'s implicit argument unifies with the rewritten goal, `n`, exactly as Cure's `refl(n)` does).

Create `$WT/test/oracle/rewrite/rw06_restated_zero_right.cure`:
```
mod Rw06
  type Nat = Z | S(Nat)
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  fn plus_zero_right(n: Nat) -> Eq(Nat, plus(n, Z), n) = match n
    Z() -> refl(Z)
    S(k) -> rewrite plus_zero_right(k) in refl(S(k))
  fn restated_zero_right(n: Nat) -> Eq(Nat, plus(n, Z), n) = rewrite plus_zero_right(n) in refl(n)
end
```
Create `$WT/test/oracle/rewrite/rw06_restated_zero_right.idr`:
```idris
%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

restatedZeroRight : (n : N) -> plus n Z = n
restatedZeroRight n = rewrite plusZeroRight n in Refl
```

Create `$WT/test/oracle/rewrite/rw07_conv_occurrence.cure`:
```
mod Rw07
  type Nat = Z | S(Nat)
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  fn plus_zero_right(n: Nat) -> Eq(Nat, plus(n, Z), n) = match n
    Z() -> refl(Z)
    S(k) -> rewrite plus_zero_right(k) in refl(S(k))
  fn conv_occurrence(n: Nat) -> Eq(Nat, plus(plus(Z, n), Z), n) = rewrite plus_zero_right(n) in refl(n)
end
```
Create `$WT/test/oracle/rewrite/rw07_conv_occurrence.idr`:
```idris
%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

convOccurrence : (n : N) -> plus (plus Z n) Z = n
convOccurrence n = rewrite plusZeroRight n in Refl
```

- [ ] **Step 9: Run live regen (needs idris2 from Task 2), then triage**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix cure.oracle rewrite`
Expected: one `cure=… idris=…` line per probe and a `wrote test/oracle/rewrite/verdicts.json`. Any line ending `<-- TRIAGE` is a divergence the harness will not silently bless.

Triage each `<-- TRIAGE` line, per the global triage rule:
- **Cure-rejects / Idris-accepts** (e.g. plausibly rw04, rw07): this is the exact input Task 5 exists for. Leave the fixture at `relation: "same"` (so replay stays red) and carry the case into Task 5. Only after Task 5 concludes the divergence is a *deliberate, documented* Cure restriction do you set `relation: "cure_stricter"` + a one-line `reason` (by editing `verdicts.json`'s relation/reason fields — not the verdicts) and re-run `mix cure.oracle rewrite` to confirm the verdicts are preserved.
- **Cure-accepts / Idris-rejects**: a soundness-relevant surprise — STOP and report; never label it benign.
- **Agree** (both accept or both reject): no action; `relation: "same"` is already consistent.

- [ ] **Step 10: Run the replay test — green for all non-Task-5 pairs**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/oracle_replay_test.exs`
Expected: PASS for every pair whose relation is settled. If a pair is deferred to Task 5, its `relation: "same"` + divergent verdicts keep that one assertion red **by design** — record which pair(s) are red-pending-Task-5 in the task note, finish Task 5, then return here for green. Do NOT commit a red replay suite as "done": Step 11 commits only once replay is green (either all agree, or divergences are documented `cure_stricter` after Task 5).

- [ ] **Step 11: Commit the corpus + fixtures + replay test**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
git add -- test/oracle/rewrite test/oracle_replay_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): seven-probe rewrite corpus + committed verdicts + offline replay" \
  -- test/oracle/rewrite test/oracle_replay_test.exs
```
Expected: one commit with the 14 corpus files, `verdicts.json`, and the replay test.

---

### Task 5: Audit `rewrite_plan/5` against `elabRewrite` (cure-lang worktree)

Diff Cure's `Cure.Elab.Elaborator.rewrite_plan/5` (`lib/cure/elab/elaborator.ex:174`) against the vendored `TTImp/Elab/Rewrite.idr` (`elabRewrite`, `getRewriteTerms`, the `RewriteNoChange` post-check). Fix each *confirmed* behavioral delta red-green. Candidate deltas below; a candidate that is not real gets a one-line "no delta" note in the commit body, not a change.

**Files:**
- Modify (only if a delta is confirmed): `$WT/lib/cure/elab/elaborator.ex` (`rewrite_plan/5` region, lines ~168–233)
- Test: `$WT/test/cure/elab/rewrite_plan_audit_test.exs` (create for each confirmed delta)

**Interfaces:**
- Consumes: Task 4's triaged corpus (rw04/rw07 outcomes drive which candidates are real; rw06 is a same/same regression pair, not a triage input — see Task 4 Step 8).

**Candidate deltas (from the source diff):**
1. **Error vocabulary** — Idris distinguishes `NotRewriteRule` (proof is not an equality; `getRewriteTerms` throws it) from `RewriteNoChange` (the rewritten type converts with the original; `elabRewrite` line 98–99). Cure already has two codes: `:rewrite_proof_not_equality` (from `eq_parts/1`, `elaborator.ex:169`) ≈ `NotRewriteRule`, and `:rewrite_no_match` (from `rewrite_plan/5`'s `true ->` branch, `elaborator.ex:187`) ≈ `RewriteNoChange`. **Likely already at parity** — confirm via rw05 (→ `:rewrite_proof_not_equality`) and rw03 (→ `:rewrite_no_match`); if both fire the right code, record "no delta".
2. **Occurrence up to conversion vs. syntactic-on-normal-forms** — Idris calls `replace` on the NF (matches up to conversion — confirmed in the vendored clone: `Core/Normalise.idr`'s `replace'` tests `convert defs env lhs tm` at every subterm of the congruence traversal, not raw equality). Cure normalizes the goal AND both endpoints first (`elaborator.ex:145–147`) then matches with structural `contains_term?`/`replace_term` (`==` on normal forms). rw07 probes whether normal-form syntactic matching diverges from Idris' conversion matching. If rw07 diverges (Cure rejects, Idris accepts), the delta is real; if both accept, record "no delta (pre-normalization subsumes the conversion match for this corpus)".
3. **Motive abstraction under binders** — Idris uses `refsToLocals`/proper weakening. Cure's `abstract_term/3` (`elaborator.ex:214–233`) increments `depth` for `:pi`/`:lam`/`:sigma` but its generic tuple clause (`elaborator.ex:227`) recurses into children **without** incrementing depth. This is not merely a hypothetical future gap: `Cure.Core.Term` (`term.ex:80–84`) documents a second, existing binder form — a `:case` branch `{ctor, arity, body}` binds `arity` variables directly in `body` — and `Kernel.normalize`'s "preserve stuck case" δ-gate (`kernel.ex:27–30`) means a certified-total recursive call applied to a bound (neutral) argument normalizes to exactly such a live `:case` term, not an opaque application spine. So the open question is empirical, not "could a future form exist": does any goal in this corpus actually reify a stuck `:case` after normalization, and if so does `abstract_term`'s generic clause corrupt the branch bodies' indices? rw04's nested-goal bodies (recursive calls applied to the induction variable) are the stress input most likely to surface this. If no capture is observed, record "no delta"; if a delta is real, the fix adds an explicit `:case` clause to `abstract_term` that increments `depth` by each branch's `arity` before recursing into that branch's body.

- [ ] **Step 1: Confirm which candidates are real from Task 4's triage**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
cat test/oracle/rewrite/verdicts.json
```
For each `<-- TRIAGE` pair recorded in Task 4, map it to a candidate above. Also directly probe the error codes for the reject cases (candidate 1) with a throwaway `iex` check:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
mix run -e 'IO.inspect(Cure.Elab.Program.elaborate(File.read!("test/oracle/rewrite/rw05_non_eq_proof.cure")))'
mix run -e 'IO.inspect(Cure.Elab.Program.elaborate(File.read!("test/oracle/rewrite/rw03_no_occurrence.cure")))'
```
Expected: rw05 error mentions `:rewrite_proof_not_equality`; rw03 mentions `:rewrite_no_match`. Record the actual tags. (Serialize concern from the repo history: `mix run` may hit the pipeline-events registry — if it raises `unknown registry: Cure.Pipeline.Events.Registry`, run the same probe as a one-off ExUnit test instead, per the repo's known workaround.)

- [ ] **Step 2: For each CONFIRMED delta, write a failing test first**

Create `$WT/test/cure/elab/rewrite_plan_audit_test.exs` with one test per confirmed delta. Template (fill the assertion to the confirmed behavior — this shows the shape; the concrete expected error/term comes from Step 1):
```elixir
defmodule Cure.Elab.RewritePlanAuditTest do
  @moduledoc "Behavioral deltas found auditing rewrite_plan/5 vs Idris' elabRewrite (P0 Task 5)."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # EXAMPLE (candidate 1). Keep ONLY if Step 1 shows Cure does NOT already
  # distinguish the two error families; delete otherwise with a "no delta" note.
  test "a non-equality rewrite proof is a distinct error from a no-op rewrite" do
    non_eq = """
    type Nat = Z | S(Nat)
    fn f(n: Nat, m: Nat) -> Eq(Nat, m, m) = rewrite n in refl(m)
    """

    no_change = """
    type Nat = Z | S(Nat)
    fn g(p: Eq(Nat, Z, Z), m: Nat) -> Eq(Nat, m, m) = rewrite p in refl(m)
    """

    assert {:error, e1} = Program.elaborate(non_eq)
    assert {:error, e2} = Program.elaborate(no_change)
    refute error_tag(e1) == error_tag(e2), "NotRewriteRule and RewriteNoChange must be distinct codes"
  end

  # Extracts the leading classification atom from a tagged error term, e.g.
  # `:rewrite_proof_not_equality` stays as-is, `{:rewrite_no_match, a, b, exp}`
  # -> `:rewrite_no_match`. This is the actual comparison the test needs: the
  # raw error terms carry different payload shapes/arities regardless of
  # whether their *codes* differ, so comparing raw terms would not prove the
  # families are distinct. If Step 1 shows the error arrives wrapped in an
  # outer context tuple (e.g. a function/location wrapper), adjust this to
  # unwrap to the inner rewrite-specific reason first, then take its tag.
  defp error_tag(err) when is_atom(err), do: err
  defp error_tag(err) when is_tuple(err), do: elem(err, 0)
end
```
If Step 1 shows **no** real delta for every candidate, create no test; instead write a short `docs/superpowers/ports/p0-rewrite-audit.md` note stating each candidate was checked and found at parity, citing the source lines. (This satisfies the audit-first gate's "ledger claims verified" without a spurious test.)

- [ ] **Step 3: Run the failing test(s)**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/cure/elab/rewrite_plan_audit_test.exs`
Expected: FAIL for each confirmed delta (documents the gap before the fix).

- [ ] **Step 4: Fix `rewrite_plan/5` minimally to close each confirmed delta**

Edit only the confirmed region of `lib/cure/elab/elaborator.ex`. Keep the change minimal and elaborator-local (no kernel edit — charter D2). Re-run until green:
`cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/cure/elab/rewrite_plan_audit_test.exs`
Expected: PASS.

- [ ] **Step 5: Re-run the oracle for any pair deferred from Task 4**

If a pair was left red-pending in Task 4 Step 10 because the audit resolves it, either (a) the fix makes Cure agree with Idris — re-run `mix cure.oracle rewrite`, verdicts now agree, `relation: "same"` is consistent; or (b) the divergence is a confirmed deliberate restriction — set that pair's `relation`/`reason` in `verdicts.json` to `cure_stricter` + a one-line reason and re-run `mix cure.oracle rewrite` to confirm preservation. Then:
`cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/oracle_replay_test.exs`
Expected: PASS (replay fully green).

- [ ] **Step 6: Commit (explicit pathspec, ghost author)**

Stage only the files this task actually changed (the audit test and/or the doc note, `elaborator.ex` if edited, and `verdicts.json` if a relation/reason was settled):
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
# adjust the pathspec to exactly what changed:
git add -- test/cure/elab/rewrite_plan_audit_test.exs lib/cure/elab/elaborator.ex test/oracle/rewrite/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "fix(elab): rewrite_plan/5 parity with elabRewrite (P0 audit)" \
  -- test/cure/elab/rewrite_plan_audit_test.exs lib/cure/elab/elaborator.ex test/oracle/rewrite/verdicts.json
```
If the audit found no delta, commit only the audit note:
```bash
git add -- docs/superpowers/ports/p0-rewrite-audit.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(ports): P0 rewrite audit — rewrite_plan/5 at parity with elabRewrite" \
  -- docs/superpowers/ports/p0-rewrite-audit.md
```

---

### Task 6: Ledger §2 corrections (cure-lang worktree)

Correct the parity roadmap's **§2 ledger only** to match the tree (charter D5, findings 2/3/4/6). §3 is reserved for the banking plan so the two parallel worktrees never edit the same section — do NOT touch §3.

**Files:**
- Modify: `$WT/docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` (§2 table + the two prose paragraphs after it; §1, §3, §4, §5 untouched)

**Edits (finding-by-finding):**
- Row **#7** (Propositional equality / rewrite motive inference): status is stale `⬜`. Per finding 2, `rewrite_plan/5` substantially implements `elabRewrite`; P0's audit (Task 5) closes any residual delta. Change the work-item wording to reflect *reach* (what remains), and set status to `✅` if Task 5 confirmed parity, else `🔵` with a note. Default: `✅` (audit-complete).
- Row **#13** (Mutual recursion): status is stale `🔴`. Per finding 3, the hole is closed on this branch (`d13d718`); `diverging_mutual_pair` replays `:ok`. Reword from "confirmed hole; checker must be fixed" to reach wording ("well-founded mutual / lexicographic descent currently rejected, not unsoundly accepted — P1 reach"), and change `🔴` → the not-a-hole state. Since the *reach* remains open, use `⬜` with the reach wording (NOT `✅` — multi-arg/lexicographic descent is still rejected). Per finding 4, the row's `Layer` column is also stale: it reads `E`, but the descent check the row actually describes is `Cure.Core.Certificate.terminating?/3` (K) — `Cure.Elab.TotalityClosure` (E) only decides which globals need certification. Change `Layer` from `E` to `K, E` (this is a ledger-accuracy fix, independent of P1; it does not imply any code change here).
- Rows **#2, #8, #16** (④ pieces): currently `🔵 ④` (in flight). Per finding 6, ④'s pieces are committed (`3b24829`, `d770aa1`, `f068943`). Change each `🔵 ④` → `✅`.
- **Headline recount** (the "The honest headline" paragraph and the "Already at parity" list): recompute. Before: "6 at parity, 4 ride in on ④ (in flight), 15 remain." After flipping #2/#8/#16 → ✅ (that is 3 of the 4 ④ rows; #7 also → ✅), recount so the totals are internally consistent with the new markers. Compute the new counts from the actual table after edits — do not guess.

- [ ] **Step 1: Verify the finding claims against the tree before editing (audit-first)**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
git log --oneline | grep -E "d13d718|3b24829|d770aa1|f068943|decc93f" || true
mix test test/antigen/assays/totality_test.exs 2>&1 | tail -3
grep -n "def terminating?" lib/cure/core/certificate.ex
grep -n "TotalityClosure" lib/cure/elab/totality_closure.ex | head -3
```
Expected: the commits are present in history; the totality assay (with `diverging_mutual_pair`) is green; `terminating?` is defined in `lib/cure/core/certificate.ex` (K); `TotalityClosure` is defined in `lib/cure/elab/totality_closure.ex` (E). This confirms findings 2/3/4/6 before touching the ledger.

- [ ] **Step 2: Edit the §2 table rows**

In `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`, change these five table rows. Row #2:
```
| 2 | Dependent case surface | Impossible clauses (omit + verified `-> impossible`) + constructor-headed motive completeness (verbatim-reuse case) | E, P, C | additive | ✅ |
```
Row #7:
```
| 7 | Propositional equality | Automatic `rewrite` motive inference (abstract LHS occurrences in the goal, à la Idris `rewrite … in`) — implemented in `rewrite_plan/5`, audited to parity with `elabRewrite` (P0) | E | additive | ✅ |
```
Row #8:
```
| 8 | Equality / absurdity | `Void`/absurd elimination at the surface (`{:absurd}`) | K (leaf), E | additive | ✅ |
```
Row #13:
```
| 13 | Totality — termination | **Mutual recursion**: soundness hole closed (`d13d718`; `diverging_mutual_pair` replays `:ok`). Remaining is *reach* — well-founded mutual / lexicographic descent is conservatively rejected, not unsoundly accepted (P1/#14) | K, E | reach | ⬜ |
```
Row #16:
```
| 16 | Totality — coverage | Surface exhaustiveness diagnostics accounting for discharged/impossible branches | E | additive | ✅ |
```

- [ ] **Step 3: Update the status legend usage / prose to remove the stale live-hole claim**

The legend line (§1 end) may keep `🔴 live soundness hole` as a legend entry, but the prose must no longer assert one exists. In "### The honest headline", replace the sentence asserting two soundness rows and the `#13` reference: after the edits, the only remaining soundness-relevant open row is **#19** (nested positivity) — #13's hole is closed. Recompute the headline counts from the post-edit table (count `✅`, `🔵`, `⬜`, `🔴` rows across all 25) and rewrite the paragraph with the new numbers. Likewise update "### Already at parity — no work" if its row list changes (it enumerates ✅ rows).

- [ ] **Step 4: Structural verification**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
grep -nE "^\| (2|7|8|13|16) \|" docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
grep -c "🔴" docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
```
Expected: rows 2/7/8/16 show `✅`, row 13 shows `⬜` with reach wording; the `🔴` count is `1` (legend only) or `0` — never on a data row. Confirm §3/§4/§5 are byte-identical to before (`git diff` touches only §1 legend prose + §2).

- [ ] **Step 5: Commit (explicit pathspec, ghost author)**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
git add -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(roadmap): §2 ledger to tree — #2/#8/#16 ✅, #7 ✅ (audited), #13 hole closed→reach" \
  -- docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
```

---

### Task 7: Final gate — full suite + oracle replay green + closing report

**Files:**
- Create: `$WT/docs/superpowers/reports/2026-07-02-transliteration-p0-report.md`

- [ ] **Step 1: Run the full suite ONCE (serialized — no other build running)**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test`
Expected: green (the pre-P0 baseline was 2185 passing = 2182 tests + 3 doctests; P0 adds the oracle unit tests, the replay tests, and any audit test — the new total must be ≥ baseline with zero failures). If any pre-existing `--warnings-as-errors` warnings surface, note them in the report as pre-existing branch-hygiene debt (out of P0 scope), do not fix them here.

- [ ] **Step 2: Confirm oracle replay is green standalone**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0 && mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 3: Write the closing report**

Create `$WT/docs/superpowers/reports/2026-07-02-transliteration-p0-report.md` summarizing: each task's outcome + commit SHA; the oracle corpus (7 probes, final verdict relations); the Task-5 audit conclusion (deltas found/fixed, or parity confirmed with source citations); the ledger rows flipped (#2/#7/#8/#16 → ✅, #13 hole-closed→reach); any TCB diff (expected: none in P0); pre-existing warnings noted; and the P0 gate checklist (charter §8) marked. List the next clusters (pre-port banking run, then P1) as remaining.

- [ ] **Step 4: Commit the report (explicit pathspec, ghost author)**

Run:
```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/transliteration-p0
git add -- docs/superpowers/reports/2026-07-02-transliteration-p0-report.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(report): transliteration P0 closing report" \
  -- docs/superpowers/reports/2026-07-02-transliteration-p0-report.md
```

---

## Self-Review

- **Spec coverage:** P0 charter §6 scope (a) snapshot refresh → Task 1; (b) build idris2 + oracle skeleton + rewrite corpus → Tasks 2/3/4; (c) audit `rewrite_plan` vs `elabRewrite` → Task 5; (d) ledger rows #7/#13 + flip 2/8/16 → Task 6. Gates (§8): audit-first (Task 1 Step 1, Task 5 Step 1, Task 6 Step 1), red-green (Tasks 3/4/5), kernel green + replay (Task 7), oracle fixtures banked (Task 4). All covered.
- **Placeholder scan:** every code step has complete file content or an exact edit; the one deliberately open spot (Task 5's fix) is gated on the audit outcome with a decision procedure and example test, not a placeholder — its shape is fully specified and its "no delta" branch is explicit.
- **Type/interface consistency:** `Cure.Oracle` function names/arities in Task 3's Interfaces block match the mix task (Task 3 Step 5) and both test files (Tasks 3/4). `cure_verdict/1` returns `:accept|:reject` (atoms); fixtures store `"accept"|"reject"` (strings) via `Atom.to_string`; `consistent/1` matches on the string forms — consistent across producer and consumers.
