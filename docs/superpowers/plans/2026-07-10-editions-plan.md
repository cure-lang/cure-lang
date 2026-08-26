# Cure Editions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a Rust-style "editions" layer over the existing migration facility: a declared, calendar-named compatibility line that parameterizes parsing, gives every migration rule since/enforced-in provenance and an applicability tier, and lets `cure migrate` carry a file/project across an edition boundary via a verified fixpoint.

**Architecture:** A new `Cure.Edition` module owns edition identity, ordering, and resolution (pragma > `Cure.toml` > default-latest). The lexer computes its keyword set as a function of the resolved edition, deriving the retired-keyword set from the migration registry (single source of truth). The `Cure.Migrate.Rule` struct's binary `tolerate_safe?` becomes a `tier` (`:machine`/`:review`/`:manual`) plus `since`/`enforced_in`/`retires_keywords` provenance. `cure migrate` gains a fixpoint driver (`run_to_fixpoint/2`) that reparses + checks comment-preservation each pass, and a two-phase edition-crossing CLI that rewrites to a fixpoint then bumps the declared edition.

**Tech Stack:** Elixir; the Cure compiler (`lib/cure/compiler/{lexer,parser,printer}.ex`), the migration facility (`lib/cure/migrate*.ex`), the project manifest (`lib/cure/project.ex`), the CLI (`lib/cure/cli.ex`), ExUnit tests, Antigen coverage probes.

## Global Constraints

- **Commits are authored as the user only — never add `Co-Authored-By` or any AI trailer** (repo policy in `/Users/ch/Develop/CLAUDE.md`).
- **Work entirely in the worktree** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/editions` on branch `autopilot/editions`. All paths below are relative to that worktree root. All git ops land on `autopilot/editions`.
- **Editions start at `"2026"`**; the compiler default when a file declares none is **latest** (`Cure.Edition.current/0` = `"2026"`).
- **Declaration precedence: file `@edition("YYYY")` pragma > `Cure.toml` `[project].edition` > compiler default.**
- **`tier` is the single warn/rewrite/normalize authority.** `:machine` may be normalized in-memory by `cure build`; `:review` and `:manual` may **not**. This replaces `tolerate_safe?` — it is a deliberate capability change, not a rename (three rules gain in-build normalization they never had).
- **Verify = reparse + comment-preservation only** (no elaboration). **Monotone-rewrite law**: a second full pass over a fixpoint's output must be byte-identical. `@max_passes` (8) is a backstop, not load-bearing.
- **`cure build` stays single-pass**; fixpoint iteration is exclusive to `cure migrate`.
- **Keep the hand-rolled Pratt parser** (no NimbleParsec).
- **Every rewrite is lossless** — comments survive.
- **Run tests with** `MIX_ENV=test mix test <path>` from the worktree root. Only ever one full/suite run at a time.
- **Tests are immutable once they correctly encode intended behavior.** A red test goes green only by changing implementation code — never by deleting it, skipping/`@tag :skip`-ing it, loosening its assertions, or rewriting it to match whatever the code currently does. The sole exception is a test that is itself provably wrong (a bug in the test, or a misunderstanding of the intended behavior) — and in that case the step touching it must say *why* before changing it, not merely that it was failing. This applies equally to a pre-existing test a task's changes legitimately obsolete (e.g. Task 11 Step 5's `--strict` pin): replace it with an assertion of the *new*, spec-mandated contract, stated as such, never silently.

---

## File Structure

- **Create** `lib/cure/edition.ex` — `Cure.Edition`: identity (`@known`/`current/0`), total order (`compare/2`, `all/0`), validation (`parse/1`), resolution (`resolve/1`, `pragma_edition/1`), and (added in Phase 3) `retired_keywords/1..2`.
- **Modify** `lib/cure/project.ex` — add `:edition` field to the struct + parse it from the `[project]` table.
- **Modify** `lib/cure/migrate/rule.ex` — replace `tolerate_safe?` with `tier`; add `since`, `enforced_in`, `retires_keywords`.
- **Modify** `lib/cure/migrate.ex` — repoint `commit/4` onto `tier`; add `run_to_fixpoint/2`.
- **Modify** the five rule files under `lib/cure/migrate/rules/` — add tier/provenance to each `%Rule{}`.
- **Create** `lib/cure/migrate/rules/proto_to_interface.ex` — the first `retires_keywords` rule.
- **Modify** `lib/cure/compiler/lexer.ex` — `:edition` option → edition-derived keyword set.
- **Modify** `lib/cure/compiler/parser.ex` — thread `:edition`; enforce `@edition` pragma placement.
- **Modify** `lib/cure/cli.ex` — edition-aware two-phase `cure migrate`.
- **Create/Modify** tests: `test/cure/edition_test.exs`, `test/cure/project_edition_test.exs`, `test/cure/migrate/{rule_tier,run_to_fixpoint,monotone_property,proto_to_interface,edition_crossing}_test.exs`, `test/cure/compiler/{edition_lexer,edition_pragma,parser_impl_for_type}_test.exs`, `test/cure/cli/migrate_edition_cli_test.exs`, and an Antigen probe pair.

---

## Phase 1 — `Cure.Edition` + resolution + manifest field

### Task 1: `Cure.Edition` identity, ordering, validation

**Files:**
- Create: `lib/cure/edition.ex`
- Test: `test/cure/edition_test.exs`

**Interfaces:**
- Produces: `Cure.Edition.current/0 :: String.t()`, `Cure.Edition.known/0 :: [String.t()]`, `Cure.Edition.all/0 :: [String.t()]` (oldest-first), `Cure.Edition.valid?/1 :: boolean`, `Cure.Edition.parse/1 :: {:ok, String.t()} | {:error, {:unknown_edition, String.t()}}`, `Cure.Edition.compare/2 :: :lt | :eq | :gt`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/edition_test.exs
defmodule Cure.EditionTest do
  use ExUnit.Case, async: true
  alias Cure.Edition

  test "current is the newest known edition and is valid" do
    assert Edition.current() == "2026"
    assert Edition.valid?("2026")
    assert Edition.all() == ["2026"]
  end

  test "parse accepts a known edition and rejects an unknown one" do
    assert Edition.parse("2026") == {:ok, "2026"}
    assert Edition.parse("2062") == {:error, {:unknown_edition, "2062"}}
  end

  test "compare orders editions by integer year" do
    assert Edition.compare("2026", "2026") == :eq
    # a hypothetical newer edition compares greater (compare must not itself
    # gate on the allow-list, so ordering logic is testable ahead of minting)
    assert Edition.compare("2025", "2026") == :lt
    assert Edition.compare("2027", "2026") == :gt
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/edition_test.exs`
Expected: FAIL — `Cure.Edition` is undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# lib/cure/edition.ex
defmodule Cure.Edition do
  @moduledoc """
  Cure editions: a coarse, declared, calendar-named compatibility line a file or
  project is read against (design: docs/superpowers/specs/roadmap/2026-07-10-editions-design.md).

  An edition is a 4-digit calendar-year string. The set of real editions is the
  closed allow-list `@known`; `current/0` is the newest. Ordering is by integer
  year and is deliberately independent of the allow-list so ordering logic is
  usable for editions not yet minted.
  """

  @known ["2026"]
  @current "2026"

  @type t :: String.t()

  @doc "All known editions, oldest-first."
  @spec all() :: [t()]
  def all, do: Enum.sort(@known, &(year(&1) <= year(&2)))

  @doc "Every known edition (declaration set; unordered)."
  @spec known() :: [t()]
  def known, do: @known

  @doc "The newest known edition — the compiler default when none is declared."
  @spec current() :: t()
  def current, do: @current

  @doc "True iff `edition` is a known edition."
  @spec valid?(term()) :: boolean()
  def valid?(edition), do: edition in @known

  @doc "Validate an edition string against the allow-list."
  @spec parse(term()) :: {:ok, t()} | {:error, {:unknown_edition, term()}}
  def parse(edition) do
    if valid?(edition), do: {:ok, edition}, else: {:error, {:unknown_edition, edition}}
  end

  @doc "Total order on editions by integer year (allow-list-independent)."
  @spec compare(t(), t()) :: :lt | :eq | :gt
  def compare(a, b) do
    cond do
      year(a) < year(b) -> :lt
      year(a) > year(b) -> :gt
      true -> :eq
    end
  end

  defp year(<<y::binary-size(4)>>), do: String.to_integer(y)
  defp year(other) when is_binary(other), do: String.to_integer(other)
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/edition_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/edition.ex test/cure/edition_test.exs
git commit -m "feat(edition): Cure.Edition identity, ordering, validation"
```

### Task 2: Pragma scan + `resolve/1` precedence

**Files:**
- Modify: `lib/cure/edition.ex`
- Modify: `lib/cure/project.ex:48-60` (defstruct), `lib/cure/project.ex:740-742` (struct build), `lib/cure/project.ex:772` (`apply_kv` project table — no change needed, it already stores every project key into `acc.project`, so `edition` is captured; the struct build is where it must be lifted out and validated)
- Test: `test/cure/project_edition_test.exs`, extend `test/cure/edition_test.exs`

**Interfaces:**
- Consumes: `Cure.Edition.parse/1`, `Cure.Edition.current/0` (Task 1); `Cure.Project.load/1` (existing, `lib/cure/project.ex:68`).
- Produces: `Cure.Edition.pragma_edition/1 :: String.t() | nil`; `Cure.Edition.resolve/1` where the arg is `%{optional(:source) => String.t(), optional(:project_dir) => Path.t()}` returning `{:ok, t()} | {:error, term()}`; `Cure.Project` struct gains `:edition` (a validated edition string or `nil`). Per spec §3.2 point 2, a project with a `Cure.toml` but no `edition` key also emits a **one-time** advisory (`Cure.Edition.reset_advisory!/0` clears the once-flag for test isolation).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/project_edition_test.exs
defmodule Cure.ProjectEditionTest do
  use ExUnit.Case, async: true

  defp write_toml(body) do
    dir = Path.join(System.tmp_dir!(), "cureproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "Cure.toml"), body)
    dir
  end

  test "loads a validated edition from the [project] table" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2026\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  test "absent edition key yields nil (the default path is applied at resolution, not load)" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == nil
  end

  test "an unknown edition in the manifest is a load-time error" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2062\"\n")
    assert {:error, {:unknown_edition, "2062"}} = Cure.Project.load(dir)
  end
end
```

```elixir
# append to test/cure/edition_test.exs
  describe "pragma_edition/1" do
    test "reads a file-leading @edition pragma, skipping comments and blanks" do
      src = "## header comment\n\n@edition(\"2026\")\nmod M\n"
      assert Cure.Edition.pragma_edition(src) == "2026"
    end

    test "returns nil when the first non-trivia item is not an @edition pragma" do
      assert Cure.Edition.pragma_edition("mod M\n@edition(\"2026\")\n") == nil
    end
  end

  describe "resolve/1 precedence" do
    test "a file pragma wins over everything" do
      assert Cure.Edition.resolve(%{source: "@edition(\"2026\")\nmod M\n"}) == {:ok, "2026"}
    end

    test "an unknown pragma edition is an error" do
      assert {:error, {:unknown_edition, "2062"}} =
               Cure.Edition.resolve(%{source: "@edition(\"2062\")\nmod M\n"})
    end

    test "no pragma and no project dir falls back to the latest edition" do
      assert Cure.Edition.resolve(%{source: "mod M\n"}) == {:ok, Cure.Edition.current()}
    end
  end

  describe "missing-edition advisory (spec §3.2 point 2)" do
    setup do
      Cure.Edition.reset_advisory!()
      :ok
    end

    defp write_toml_no_edition do
      dir = Path.join(System.tmp_dir!(), "cureadv_#{System.unique_integer([:positive])}")
      File.mkdir_p!(dir)
      File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
      dir
    end

    test "a Cure.toml with no edition key logs a one-time advisory" do
      dir = write_toml_no_edition()

      log =
        ExUnit.CaptureLog.capture_log(fn ->
          assert {:ok, _} = Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
        end)

      assert log =~ "no `edition` declared"
    end

    test "the advisory fires only once across repeated resolutions" do
      dir = write_toml_no_edition()

      log =
        ExUnit.CaptureLog.capture_log(fn ->
          Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
          Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
        end)

      assert length(Regex.scan(~r/no `edition` declared/, log)) == 1
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/project_edition_test.exs test/cure/edition_test.exs`
Expected: FAIL — `pragma_edition/1`, `resolve/1`, and `project.edition` are undefined.

- [ ] **Step 3: Write minimal implementation**

Add to `lib/cure/edition.ex`:

```elixir
  @doc """
  The edition named by a file-leading `@edition("YYYY")` pragma, or `nil`. Uses a
  lightweight pre-parse line scan (not the full parser) because the edition must
  be known BEFORE parsing selects the keyword set. Skips leading blank lines and
  `#`/`##` comment lines; the first substantive line must be the pragma or there
  is none.
  """
  @spec pragma_edition(String.t()) :: t() | nil
  def pragma_edition(source) when is_binary(source) do
    source
    |> String.split("\n")
    |> Enum.drop_while(&trivia_line?/1)
    |> case do
      [first | _] -> pragma_capture(first)
      [] -> nil
    end
  end

  defp trivia_line?(line) do
    t = String.trim(line)
    t == "" or String.starts_with?(t, "#")
  end

  defp pragma_capture(line) do
    case Regex.run(~r/^\s*@edition\(\s*"(\d{4})"\s*\)/, line) do
      [_, year] -> year
      nil -> nil
    end
  end

  @doc """
  Resolve the effective edition for a source/project per precedence:
  file `@edition` pragma > `Cure.toml` `[project].edition` > compiler default.
  """
  @spec resolve(map()) :: {:ok, t()} | {:error, term()}
  def resolve(input) do
    case pragma_edition(Map.get(input, :source, "")) do
      nil -> resolve_project(Map.get(input, :project_dir))
      pragma -> parse(pragma)
    end
  end

  defp resolve_project(nil), do: {:ok, current()}

  defp resolve_project(dir) do
    case Cure.Project.load(dir) do
      {:ok, %{edition: nil}} ->
        maybe_advise_missing_edition()
        {:ok, current()}

      {:ok, %{edition: edition}} ->
        {:ok, edition}

      {:error, :no_project_file} ->
        {:ok, current()}

      {:error, _} = err ->
        err
    end
  end

  @advisory_key {__MODULE__, :missing_edition_advisory_shown?}

  # Spec §3.2 point 2: a project with a Cure.toml but no `edition` key still
  # resolves (to `current/0`) rather than hard-failing, but logs a one-time
  # advisory so projects converge on an explicit edition. "Once" is
  # process-lifetime via :persistent_term (mirrors the existing memoisation
  # pattern in lib/cure/types/stdlib.ex), not per-file — a whole-project
  # build touching many undeclared files must not spam one warning per file.
  defp maybe_advise_missing_edition do
    case :persistent_term.get(@advisory_key, false) do
      true ->
        :ok

      false ->
        :persistent_term.put(@advisory_key, true)
        Logger.warning("no `edition` declared in Cure.toml — add `edition = \"#{current()}\"` under [project] to pin the language surface this project reads against")
    end
  end

  @doc false
  # Test-only: clears the one-time advisory flag so tests asserting on it are
  # isolated from each other and from resolve/1 calls made by other tests.
  @spec reset_advisory!() :: :ok
  def reset_advisory! do
    :persistent_term.erase(@advisory_key)
    :ok
  end
```

Add `require Logger` near the top of `lib/cure/edition.ex`, alongside the moduledoc.

In `lib/cure/project.ex`, add `:edition` to the defstruct (after `:version`):

```elixir
  defstruct [
    :name,
    :version,
    :edition,
    dependencies: [],
    # ... rest unchanged
  ]
```

Lift+validate it in two steps (there is only ONE working approach — do not branch on this; `parse_toml/1` cannot return `{:error, _}` today, and `apply_kv({:table, "project"}, ...)` already stores every `[project]` key including an unrecognized `edition` into `acc.project`, confirmed at `lib/cure/project.ex:772-790`):

1. In the struct build inside `parse_toml/1` (the `%__MODULE__{...}` literal at `lib/cure/project.ex:740-750`, built from the local `parsed = parse_lines(lines, nil, acc)`), add one field carrying the raw string through unvalidated:

```elixir
    %__MODULE__{
      name: Map.get(parsed.project, "name", "unnamed"),
      version: Map.get(parsed.project, "version", "0.1.0"),
      edition: Map.get(parsed.project, "edition"),
      # ...rest unchanged
```

2. In `load/1` (`lib/cure/project.ex:68-82`), validate that raw value after `parse_toml/1` returns, since `load/1` — unlike `parse_toml/1` — already returns `{:error, _}`:

```elixir
      {:ok, content} ->
        project = parse_toml(content)

        case project.edition do
          nil -> {:ok, %{project | root: dir}}
          ed ->
            case Cure.Edition.parse(ed) do
              {:ok, _} -> {:ok, %{project | root: dir}}
              {:error, _} = err -> err
            end
        end
```

There is no `parse_toml_project/1` function in the codebase and none should be introduced — `parsed.project` (available only inside `parse_toml/1`, where step 1 runs) and `project.edition` (available in `load/1`, where step 2 runs) are the only two data sources this needs.

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/project_edition_test.exs test/cure/edition_test.exs`
Expected: PASS.

- [ ] **Step 5: Regression — the existing project suite still loads**

Run: `MIX_ENV=test mix test test/cure/project_test.exs` (if present) or `MIX_ENV=test mix test --only project`
Expected: PASS (no regressions in manifest parsing).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/edition.ex lib/cure/project.ex test/cure/project_edition_test.exs test/cure/edition_test.exs
git commit -m "feat(edition): resolve/1 precedence + Cure.toml [project].edition field"
```

---

## Phase 2 — Rule model refactor (tier + provenance)

### Task 3: Extend the `Rule` struct; repoint `commit/4` onto `tier`

**Files:**
- Modify: `lib/cure/migrate/rule.ex:49-82`
- Modify: `lib/cure/migrate.ex:88-94` (`commit/4`), `lib/cure/migrate.ex:60-62` (docstring for `:safe_only`)
- Test: `test/cure/migrate/rule_tier_test.exs`

**Interfaces:**
- Produces: `%Cure.Migrate.Rule{}` with new fields `tier :: :machine | :review | :manual` (required), `since :: Cure.Edition.t()` (required), `enforced_in :: Cure.Edition.t() | nil` (default `nil`), `retires_keywords :: [String.t()]` (default `[]`); `tolerate_safe?` removed. `Cure.Migrate.commit/4` normalizes in `:safe_only` mode iff `tier == :machine`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/migrate/rule_tier_test.exs
defmodule Cure.Migrate.RuleTierTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule

  # A rewrite rule at a given tier that appends a marker to a top-level block.
  defp marker_rule(tier) do
    %Rule{
      id: :W_test_tier,
      description: "test tier rule",
      phase: :syntactic,
      tier: tier,
      since: "2026",
      detect_and_rewrite: fn {:block, m, ex}, _ctx ->
        {:rewrite, {:block, m, ex ++ [{:literal, [subtype: :string], "M"}]}}
      end,
      warning_template: "marker appended"
    }
  end

  defp parse!(src) do
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
    ast
  end

  test "in :safe_only (build) mode, a :machine rewrite is normalized in-memory" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, warns} = Migrate.run(ast, rules: [marker_rule(:machine)], apply: :safe_only)
    assert new_ast != ast
    assert Enum.any?(warns, &(&1.rule == :W_test_tier))
  end

  test "in :safe_only mode, a :review rewrite warns but is NOT normalized" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, warns} = Migrate.run(ast, rules: [marker_rule(:review)], apply: :safe_only)
    assert new_ast == ast
    assert Enum.any?(warns, &(&1.rule == :W_test_tier))
  end

  test "in :all (migrate) mode, every tier's rewrite is applied" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    {new_ast, _} = Migrate.run(ast, rules: [marker_rule(:review)], apply: :all)
    assert new_ast != ast
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/migrate/rule_tier_test.exs`
Expected: FAIL — `%Rule{}` rejects `tier:`/`since:` (unknown keys) and/or `commit/4` still keys on `tolerate_safe?`.

- [ ] **Step 3: Write minimal implementation**

Replace `lib/cure/migrate/rule.ex`'s `@enforce_keys`/`defstruct`/`@type`:

```elixir
  @enforce_keys [:id, :description, :phase, :detect_and_rewrite, :warning_template, :tier, :since]
  defstruct [
    :id,
    :description,
    :phase,
    :detect_and_rewrite,
    :warning_template,
    :tier,
    :since,
    enforced_in: nil,
    retires_keywords: []
  ]

  @type tier :: :machine | :review | :manual

  @type t :: %__MODULE__{
          id: atom(),
          description: String.t(),
          phase: :syntactic | :needs_resolution,
          detect_and_rewrite: (ast(), ctx() -> result()),
          warning_template: String.t(),
          tier: tier(),
          since: Cure.Edition.t(),
          enforced_in: Cure.Edition.t() | nil,
          retires_keywords: [String.t()]
        }
```

Update the moduledoc `:tolerate_safe?` bullet to describe `tier` (machine normalizes in build; review/manual do not).

Replace `commit/4` in `lib/cure/migrate.ex:92-94`:

```elixir
  defp commit(_rule, :all, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{tier: :machine}, :safe_only, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{}, :safe_only, old_ast, _new_ast), do: old_ast
```

Update the `:safe_only` docstring at `lib/cure/migrate.ex:60-62` to say "only the rewrites of `:machine`-tier rules".

- [ ] **Step 4: Run test — it will NOT pass yet, and that's expected**

Run: `MIX_ENV=test mix test test/cure/migrate/rule_tier_test.exs`
Expected: **compile failure**, not a test failure — `@enforce_keys` is checked by the Elixir compiler at the point every `%Rule{...}` struct literal is expanded (verified: a literal missing an enforced key raises `** (ArgumentError) the following keys must also be given when building struct ...` during compilation, before any test runs), and `lib/cure/migrate/rules/{if_elif_to_pickup,uppercase_type_var,group_hoist,module_rename,removed_module}.ex` all still construct `%Rule{}` without `tier:`/`since:` at this point. `mix test` compiles the whole `lib/` tree first, so this one `@enforce_keys` change breaks the build project-wide, not just the new test. **Do not commit Task 3 on its own** — proceed directly to Task 4, which re-tags all five files; only Task 4's Step 4 run is expected to actually go green. Task 3 has no standalone commit; its diff is committed together with Task 4's (see Task 4 Step 6).

### Task 4: Re-tag the five existing rules; pin their behavior

Continues directly from Task 3 without an intervening commit — Task 3's `@enforce_keys` addition and this task's five re-tagged rule files are one atomic change (the codebase does not compile with one but not the other; see Task 3 Step 4).

**Files:**
- Modify: `lib/cure/migrate/rules/if_elif_to_pickup.ex`, `uppercase_type_var.ex`, `group_hoist.ex`, `module_rename.ex`, `removed_module.ex` (each rule's `%Rule{}` literal)
- Test: `test/cure/migrate/rule_tier_test.exs` (extend)

**Interfaces:**
- Consumes: the extended `%Rule{}` (Task 3).
- Produces: the registry rules carry the §5.3 tags: if/elif→pickup `:machine`, uppercase-type-var `:review`, @group hoist `:machine`, module rename `:machine`/`enforced_in: "2026"`, removed module `:manual`/`enforced_in: "2026"`. All `since: "2026"`.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/cure/migrate/rule_tier_test.exs
  describe "registry rule tags (spec §5.3)" do
    setup do
      by_id = for r <- Cure.Migrate.rules(), into: %{}, do: {r.id, r}
      {:ok, rules: by_id}
    end

    test "each rule has the tier and provenance the spec fixes", %{rules: r} do
      assert r[:W_if_elif_pickup].tier == :machine
      assert r[:W_uppercase_type_var].tier == :review
      assert r[:W_group_hoist].tier == :machine
      assert r[:W_module_rename].tier == :machine
      assert r[:W_module_rename].enforced_in == "2026"
      assert r[:W_removed_module].tier == :manual
      assert r[:W_removed_module].enforced_in == "2026"
      for {_id, rule} <- r, do: assert(rule.since == "2026")
    end

    test "cure build normalizes the three :machine rewrite rules that were previously never normalized" do
      # module rename is :machine → :safe_only mode now folds it in-memory.
      src = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"
      {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
      {new_ast, _} = Cure.Migrate.run(ast, apply: :safe_only)
      refute new_ast == ast, "module rename (:machine) must normalize under :safe_only"
    end

    test "cure build does NOT normalize the :review uppercase-type-var rule" do
      src = "mod M\n  fn id(x: T) -> T = x\n"
      {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false)
      {new_ast, warns} = Cure.Migrate.run(ast, apply: :safe_only)
      assert new_ast == ast, ":review must not normalize under :safe_only"
      assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/migrate/rule_tier_test.exs`
Expected: FAIL — rules lack `tier`/`since` (they still use `tolerate_safe?`), so `Cure.Migrate.rules()` raises on the missing enforced keys.

- [ ] **Step 3: Write minimal implementation**

In each rule's `%Rule{}` literal, remove any `tolerate_safe?:` entry and add the tags. Exact edits:

`if_elif_to_pickup.ex`: add `tier: :machine, since: "2026"`.
`group_hoist.ex`: add `tier: :machine, since: "2026"`.
`uppercase_type_var.ex`: add `tier: :review, since: "2026"`.
`module_rename.ex`: add `tier: :machine, since: "2026", enforced_in: "2026"`.
`removed_module.ex`: add `tier: :manual, since: "2026", enforced_in: "2026"`.

Example (module_rename.ex, at `lib/cure/migrate/rules/module_rename.ex:44`):

```elixir
    %Rule{
      id: :W_module_rename,
      description: "a reference to a renamed stdlib module is updated to its new name",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      enforced_in: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "renamed stdlib module: reference updated to its new name"
    }
```

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/migrate/rule_tier_test.exs`
Expected: PASS.

- [ ] **Step 5: Full migrate-suite regression**

Run: `MIX_ENV=test mix test test/cure/migrate/ test/cure/cli/migrate_cli_test.exs test/mix/tasks/cure_rewrite_test.exs`
Expected: PASS — the warn/rewrite behavior and warning text of every existing rule are unchanged (only the build-normalization capability of the three `:machine` rules changed, which the new tests cover).

- [ ] **Step 6: Commit (covers Task 3 + Task 4 together — see Task 3 Step 4)**

```bash
git add lib/cure/migrate/rule.ex lib/cure/migrate.ex lib/cure/migrate/rules/ test/cure/migrate/rule_tier_test.exs
git commit -m "refactor(migrate): tier + edition provenance replace tolerate_safe? on Rule"
```

---

## Phase 3 — Edition-parameterized lexing/parsing

### Task 5: Edition-derived keyword set in the lexer

**Files:**
- Modify: `lib/cure/edition.ex` (add `retired_keywords/1..2`)
- Modify: `lib/cure/compiler/lexer.ex:60` (`@keyword_strings`), `:109` (`tokenize/2` opts), and the three keyword checks at `:691`, `:700`, `:718`
- Test: `test/cure/compiler/edition_lexer_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.rules/0` (rules carry `retires_keywords`/`enforced_in`, Task 4); `Cure.Edition.compare/2`.
- Produces: `Cure.Edition.retired_keywords/1 :: [String.t()]` (default rules) and `/2` (explicit rule list); `Cure.Lexer.tokenize/2` honors an `:edition` option that removes retired keywords from the effective keyword set.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/edition_lexer_test.exs
defmodule Cure.Compiler.EditionLexerTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer
  alias Cure.Migrate.Rule

  # A fixture rule that retires the keyword "fsm" starting at edition "2027".
  defp retire_fsm_2027 do
    %Rule{
      id: :W_test_retire, description: "retire fsm", phase: :syntactic,
      tier: :machine, since: "2026", enforced_in: "2027", retires_keywords: ["fsm"],
      detect_and_rewrite: fn _ast, _ctx -> :no_change end,
      warning_template: "fsm retired"
    }
  end

  defp kinds(src, edition, rules) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false, edition: edition, migrate_rules: rules)
    for t <- toks, t.value in [:fsm, "fsm"], do: {t.type, t.value}
  end

  test "a keyword retired at 2027 is still a keyword at 2026 and an identifier at 2027" do
    rules = [retire_fsm_2027()]
    assert [{:keyword, :fsm}] = kinds("fsm x\n", "2026", rules)
    assert [{:identifier, "fsm"}] = kinds("fsm x\n", "2027", rules)
  end

  test "retired_keywords is derived from the registry, not hardcoded" do
    assert Cure.Edition.retired_keywords("2027", [retire_fsm_2027()]) == ["fsm"]
    assert Cure.Edition.retired_keywords("2026", [retire_fsm_2027()]) == []
  end

  test "proto/impl stay keywords in every edition (enforced_in: nil once the real rule ships)" do
    # with no retiring rule for them, they are never removed
    assert Cure.Edition.retired_keywords("2026", []) == []
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/compiler/edition_lexer_test.exs`
Expected: FAIL — `retired_keywords/2` undefined; `tokenize/2` ignores `:edition`.

- [ ] **Step 3: Write minimal implementation**

Add to `lib/cure/edition.ex`:

```elixir
  @doc """
  The keywords retired at or before `edition`, derived from the migration
  registry (single source of truth). A rule retires each of its
  `retires_keywords` at its `enforced_in` edition: present for editions before
  it, absent at/after. `enforced_in: nil` never retires.
  """
  @spec retired_keywords(t(), [Cure.Migrate.Rule.t()]) :: [String.t()]
  def retired_keywords(edition, rules \\ Cure.Migrate.rules()) do
    for r <- rules,
        r.enforced_in != nil,
        compare(edition, r.enforced_in) in [:eq, :gt],
        kw <- r.retires_keywords,
        uniq: true,
        do: kw
  end
```

(If the `uniq:` comprehension option is unavailable, wrap the comprehension in `|> Enum.uniq()`.)

In `lib/cure/compiler/lexer.ex`, read the option and compute the effective set. After the existing `trivia? = ...` line in `tokenize/2` (~`:113`):

```elixir
    edition = Keyword.get(opts, :edition, Cure.Edition.current())
    migrate_rules = Keyword.get(opts, :migrate_rules, Cure.Migrate.rules())
    retired = MapSet.new(Cure.Edition.retired_keywords(edition, migrate_rules))
    keyword_set = MapSet.difference(@keyword_string_set, retired)
```

Add a compile-time set beside `@keyword_strings` (`:60`):

```elixir
  @keyword_string_set MapSet.new(@keyword_strings)
```

Thread `keyword_set` into the lexer state (add a `keyword_set` field to the `%__MODULE__{}` state struct, defaulting to `@keyword_string_set`) and replace the three `word ... @keyword_strings` checks (`:691`, `:700`, `:718`) with the state's set:

- `:691`: `state.fsm_transition_depth > 0 and not MapSet.member?(state.keyword_set, word) ->`
- `:700`: `not MapSet.member?(state.keyword_set, word) and peek(state) == ?? ->`
- `:718`: `if MapSet.member?(state.keyword_set, word) do`

Set `keyword_set: keyword_set` when building the initial `state` in `tokenize/2`.

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/compiler/edition_lexer_test.exs`
Expected: PASS.

- [ ] **Step 5: Lexer regression**

Run: `MIX_ENV=test mix test test/cure/compiler/`
Expected: PASS — default edition (latest) with the real registry retires nothing yet (no rule has a non-nil `enforced_in` that names a keyword), so tokenization is byte-for-byte unchanged.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/edition.ex lib/cure/compiler/lexer.ex test/cure/compiler/edition_lexer_test.exs
git commit -m "feat(edition): edition-derived keyword set in the lexer"
```

### Task 6: Thread `:edition` through the parser; enforce `@edition` pragma placement

**Files:**
- Modify: `lib/cure/compiler/parser.ex:92` (`parse/2` opts) and the top-level statement loop where decorators are handled
- Test: extend `test/cure/compiler/edition_lexer_test.exs` (add a parser describe block) or `test/cure/compiler/edition_pragma_test.exs`

**Interfaces:**
- Consumes: `Cure.Lexer.tokenize/2` `:edition` (Task 5).
- Produces: `Cure.Parser.parse/2` accepts `:edition` (passed to any re-lex/keyword recheck) and rejects a non-file-leading `@edition(...)` pragma with a hard parse error `{:edition_pragma_placement, line, col}`; a file-leading pragma parses (as an ordinary decorator node) without error.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/edition_pragma_test.exs
defmodule Cure.Compiler.EditionPragmaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  test "a file-leading @edition pragma parses without error" do
    assert {:ok, _ast} = parse("@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n")
  end

  test "an @edition pragma that is not file-leading is a hard parse error" do
    assert {:error, errors} = parse("mod M\n  @edition(\"2026\")\n  fn f() -> Int = 1\n")
    assert Enum.any?(errors, &match?({:edition_pragma_placement, _, _}, &1))
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/compiler/edition_pragma_test.exs`
Expected: FAIL — the misplaced pragma currently parses as an ordinary decorator (no placement error).

- [ ] **Step 3: Write minimal implementation**

In `parse/2` accept `:edition` (`edition = Keyword.get(opts, :edition, Cure.Edition.current())`) and store it on the parser state so any keyword recheck uses it (mirror the lexer). For placement: `parse_at/1` (`lib/cure/compiler/parser.ex:4967+`) binds `dec_name = to_string(name_token.value)` two lines into the function — `dec_name` is a **string** (`"edition"`), not the atom `:edition`; `@module_level_decorators` is likewise a string list (`~w(group)`, i.e. `["group"]`, at `:71`). Add the placement check as its own branch **ahead of** the existing `if dec_name in @module_level_decorators do` (`:5002`), because it must fire for `@edition(...)` regardless of what token follows — `@edition` is not itself a module-level decorator that attaches to `mod`, it is a standalone pragma:

```elixir
    if dec_name == "edition" do
      unless file_leading?(state) do
        state = add_error(state, {:edition_pragma_placement, token.line, token.col})
      end

      ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
      {ast, state}
    else
      if dec_name in @module_level_decorators do
        # ...existing @group handling, unchanged...
      else
        parse_at_attach(state, token, dec_name, args)
      end
    end
```

`file_leading?/1` is true iff no substantive (non-decorator, non-comment) statement has yet been consumed — track a boolean `seen_stmt?` on the parser state, set once the first `mod`/`fn`/type/etc. statement is parsed, checked here. If a `seen_stmt?` flag is impractical to thread, an equivalent: the pragma is file-leading iff the token's `line` is `<=` the line of the first non-trivia token recorded at lex time. Use whichever the parser state already makes available; the test only asserts the two outcomes.

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/compiler/edition_pragma_test.exs`
Expected: PASS.

- [ ] **Step 5: Parser regression**

Run: `MIX_ENV=test mix test test/cure/compiler/`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/parser.ex test/cure/compiler/edition_pragma_test.exs
git commit -m "feat(edition): thread :edition through the parser; enforce @edition placement"
```

---

## Phase 4 — Fixpoint + verify engine

### Task 7: `run_to_fixpoint/2` with reparse+comment verify and `@max_passes`

**Files:**
- Modify: `lib/cure/migrate.ex` (add `run_to_fixpoint/2`)
- Test: `test/cure/migrate/run_to_fixpoint_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run/2` (existing), `Cure.Compiler.Printer.quoted_to_string/2` (`lib/cure/compiler/printer.ex:45`), `Cure.Compiler.{Lexer,Parser}` for the reparse check.
- Produces: `Cure.Migrate.run_to_fixpoint(ast, opts) :: {:ok, ast, [Warning.t()]} | {:error, {:no_convergence, [atom()]}} | {:error, {:verify_failed, atom()}}`. `opts` accepts everything `run/2` does plus `:max_passes` (default 8) and `:file`. Verify = the reprinted output reparses AND every source comment survives.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/migrate/run_to_fixpoint_test.exs
defmodule Cure.Migrate.RunToFixpointTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule
  alias Cure.Compiler.{Lexer, Parser, Trivia}

  defp parse!(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  # Rule A: append marker :a. Rule B: append :b ONLY once :a is present.
  # A single-pass fold in [A, B] order handles this; but in [B, A] order B's
  # trigger is exposed only after A runs — proving the fixpoint re-scans.
  defp append_when(id, needle, mark) do
    %Rule{
      id: id, description: "t", phase: :syntactic, tier: :machine, since: "2026",
      warning_template: "m",
      detect_and_rewrite: fn {:block, m, ex}, _ctx ->
        has = Enum.any?(ex, &match?({:literal, _, ^needle}, &1))
        want = needle == nil or has
        already = Enum.any?(ex, &match?({:literal, _, ^mark}, &1))
        if want and not already,
          do: {:rewrite, {:block, m, ex ++ [{:literal, [subtype: :string], mark}]}},
          else: :no_change
      end
    }
  end

  test "a chained rewrite (B exposed only by A) converges via fixpoint even in B-before-A order" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    rules = [append_when(:b, "a", "b"), append_when(:a, nil, "a")]
    {:ok, out, _warns} = Migrate.run_to_fixpoint(ast, rules: rules)
    {:block, _, ex} = out
    assert Enum.any?(ex, &match?({:literal, _, "a"}, &1))
    assert Enum.any?(ex, &match?({:literal, _, "b"}, &1))
  end

  test "a non-monotone rule set (A:x->y, B:y->x) hits max_passes and errors with the culprits" do
    flip = fn from, to, id ->
      %Rule{id: id, description: "t", phase: :syntactic, tier: :machine, since: "2026",
        warning_template: "m",
        detect_and_rewrite: fn {:block, m, ex}, _ctx ->
          if Enum.any?(ex, &match?({:literal, _, ^from}, &1)) do
            ex2 = Enum.map(ex, fn {:literal, meta, ^from} -> {:literal, meta, to}; o -> o end)
            {:rewrite, {:block, m, ex2}}
          else
            :no_change
          end
        end}
    end
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    seed = {:block, elem(ast, 1), [{:literal, [subtype: :string], "x"}]}
    rules = [flip.("x", "y", :A), flip.("y", "x", :B)]
    assert {:error, {:no_convergence, culprits}} =
             Migrate.run_to_fixpoint(seed, rules: rules, max_passes: 4)
    assert :A in culprits or :B in culprits
  end

  test "a rule that drops a comment fails verify and aborts without further passes" do
    # Realistic rule-author bug: the rewrite rebuilds the node's meta from
    # scratch and forgets to carry its :leading trivia across (spec §5.2 names
    # Trivia.carry/2 for exactly this; a rule that skips it loses the comment).
    src = "mod M\n  ## a doc comment on f\n  fn f(x: Int) -> Int = 1\n"
    ast = parse!(src)

    # detect_and_rewrite receives the WHOLE-FILE ast (run/2 does not walk for
    # rules — each rule walks itself, per every other rule in this plan), so
    # this recurses to find the :function_def node and strips its :leading
    # trivia there, rather than pattern-matching the top-level node directly.
    drop_comment_rule = %Rule{
      id: :W_test_drops_comment, description: "t", phase: :syntactic, tier: :machine,
      since: "2026", warning_template: "m",
      detect_and_rewrite: fn ast, _ctx ->
        case strip_leading(ast, false) do
          {new_ast, true} -> {:rewrite, new_ast}
          {_ast, false} -> :no_change
        end
      end
    }

    assert {:error, {:verify_failed, :W_test_drops_comment}} =
             Migrate.run_to_fixpoint(ast, rules: [drop_comment_rule])
  end

  # Recurse to the first :function_def carrying :leading trivia and delete
  # that key; returns {new_ast, changed?}.
  defp strip_leading({:function_def, meta, body}, false) when is_list(meta) do
    if Keyword.has_key?(meta, :leading) do
      {{:function_def, Keyword.delete(meta, :leading), body}, true}
    else
      {{:function_def, meta, body}, false}
    end
  end

  defp strip_leading({k, meta, ch}, changed?) when is_list(ch) do
    {new_ch, changed?} = strip_leading(ch, changed?)
    {{k, meta, new_ch}, changed?}
  end

  defp strip_leading(l, changed?) when is_list(l) do
    Enum.map_reduce(l, changed?, fn node, acc ->
      if acc, do: {node, acc}, else: strip_leading(node, acc)
    end)
  end

  defp strip_leading(other, changed?), do: {other, changed?}
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/migrate/run_to_fixpoint_test.exs`
Expected: FAIL — `run_to_fixpoint/2` undefined (and, once it exists, the comment-drop test specifically would still fail against a `verify/2` that only reparse-checks: `Keyword.delete(meta, :leading)` still reparses fine, since dropping a comment doesn't break syntax — only a comment-diffing verify catches it).

- [ ] **Step 3: Write minimal implementation**

Add to `lib/cure/migrate.ex`:

```elixir
  @max_passes 8

  @doc """
  Run the registry to a fixpoint (spec §6.1): repeatedly apply `run/2` until a
  full pass changes nothing. After each changing pass, verify the reprinted
  output reparses and preserves every comment; a verify failure aborts. If the
  AST is still changing at `:max_passes`, return `{:error, {:no_convergence,
  culprit_rule_ids}}` (a rule-set bug, not a user error).
  """
  @spec run_to_fixpoint(Rule.ast(), keyword()) ::
          {:ok, Rule.ast(), [Warning.t()]}
          | {:error, {:no_convergence, [atom()]}}
          | {:error, {:verify_failed, atom()}}
  def run_to_fixpoint(ast, opts \\ []) do
    max = Keyword.get(opts, :max_passes, @max_passes)
    baseline_comments = comment_texts(Cure.Compiler.Printer.quoted_to_string(ast))
    do_fixpoint(ast, opts, max, [], [], baseline_comments)
  end

  defp do_fixpoint(ast, _opts, 0, warns, fired, _baseline) do
    if fired == [], do: {:ok, ast, warns}, else: {:error, {:no_convergence, Enum.uniq(fired)}}
  end

  defp do_fixpoint(ast, opts, passes_left, warns, _prev_fired, baseline) do
    {new_ast, pass_warns} = run(ast, opts)

    if new_ast == ast do
      {:ok, ast, warns ++ pass_warns}
    else
      case verify(new_ast, baseline) do
        :ok ->
          fired = Enum.map(pass_warns, & &1.rule)
          do_fixpoint(new_ast, opts, passes_left - 1, warns ++ pass_warns, fired, baseline)

        {:error, _reason} ->
          culprit = pass_warns |> List.last() |> then(&(&1 && &1.rule))
          {:error, {:verify_failed, culprit}}
      end
    end
  end

  # Reprint → reparse (fail if the output no longer parses) AND diff comments
  # against `baseline` — the ORIGINAL input's comment texts, captured once by
  # `run_to_fixpoint/2` before the first pass, not the previous pass's output.
  # Checking against the true original (not pass-to-pass) is what makes this
  # catch a comment a rule drops on pass 3 even though passes 1-2 preserved
  # everything — re-basing to each intermediate pass would let that slip
  # through as "no *new* loss this pass".
  defp verify(ast, baseline_comments) do
    src = Cure.Compiler.Printer.quoted_to_string(ast)

    with {:ok, toks} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false),
         {:ok, _} <- Cure.Compiler.Parser.parse(toks, emit_events: false) do
      if baseline_comments -- comment_texts(src) == [] do
        :ok
      else
        {:error, :comment_dropped}
      end
    else
      _ -> {:error, :reparse}
    end
  end

  # Mirrors Cure.CLI's migrate_comments/1 (lib/cure/cli.ex:1317): every `#`-led
  # comment body, trimmed, sorted — the same coarse-but-adequate lossless check
  # the file-mode `cure migrate` pipeline already uses.
  defp comment_texts(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
  end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/migrate/run_to_fixpoint_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex test/cure/migrate/run_to_fixpoint_test.exs
git commit -m "feat(migrate): run_to_fixpoint/2 with reparse verify + max_passes backstop"
```

### Task 8: Monotone property test over the stdlib corpus

**Files:**
- Test: `test/cure/migrate/monotone_property_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run_to_fixpoint/2` (Task 7), `Cure.Compiler.{Lexer,Parser,Trivia,Printer}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/migrate/monotone_property_test.exs
defmodule Cure.Migrate.MonotonePropertyTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp fixpoint_string(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, out, _} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia))
    Printer.quoted_to_string(out)
  end

  test "migrating a fixpoint output again is byte-identical (monotone law) across the stdlib" do
    for path <- Path.wildcard("lib/std/*.cure") do
      once = fixpoint_string(File.read!(path))
      twice = fixpoint_string(once)
      assert once == twice, "non-monotone on #{path}"
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails or passes**

Run: `MIX_ENV=test mix test test/cure/migrate/monotone_property_test.exs`
Expected: PASS if the registry is already monotone (likely — every seed rule is idempotent). If it FAILS, that is a real finding: identify the non-idempotent rule from the failing path, fix that rule to be idempotent (rewrite only when not already canonical), and re-run. Do not weaken the assertion.

- [ ] **Step 3: Commit**

```bash
git add test/cure/migrate/monotone_property_test.exs
git commit -m "test(migrate): monotone-rewrite property gate over the stdlib corpus"
```

---

## Phase 5 — `proto`→`interface` rule

### Task 9: The first `retires_keywords` rule

**Files:**
- Create: `lib/cure/migrate/rules/proto_to_interface.ex`
- Modify: `lib/cure/migrate.ex` (register the rule in `rules/0`), `lib/cure/compiler/parser.ex` (`parse_impl/1`'s meta gains `for_type`, the Step 4 prerequisite)
- Test: `test/cure/compiler/parser_impl_for_type_test.exs`, `test/cure/migrate/proto_to_interface_test.exs`

**Interfaces:**
- Consumes: the extended `%Rule{}` (Task 3); the confirmed AST shapes for `proto`/`impl`/`interface`/`implementation` (Step 1).
- Produces: (prerequisite) `impl`'s meta retains `for_type`; rule `:W_proto_to_interface`, tier `:machine`, `since: "2026"`, `enforced_in: nil`, `retires_keywords: ["proto", "impl"]`. Rewrites the `proto`/`impl` AST nodes to their `interface`/`implementation` equivalents by building correctly-keyed new meta, preserving bodies and trivia.

- [ ] **Step 1: The AST shapes are already confirmed — they are NOT a simple tag swap**

`:proto` routes via `parse_proto` (`lib/cure/compiler/parser.ex:1377-1378` dispatches to the function defined at `:3536`); `:impl` via `parse_impl` (dispatch `:1381-1382`, defined `:3574`); `:interface` via `parse_interface` (dispatch `:1386-1387`, defined `:3632`); `:implementation` via `parse_implementation` (dispatch `:1389-1390`, defined `:3679`). (There is no `parse_protocol` function — do not search for one.)

Confirmed shapes (read directly from the parser):

- `proto P(t) ...` → `{:container, meta, body}` where `meta` has `container_type: :protocol`, `name: "P"` (string), `type_params: ["t"]`, `line:`, `col:`. The outer tag is the generic `:container` used by every container form (mod/rec/enum/proto/impl); `container_type` is the real discriminator.
- `impl P for Int ...` → `{:container, meta, body}` where `meta` has `container_type: :trait`, `name: "P.Int"` (protocol+type pre-joined into one string), `protocol: "P"`, `for: "Int"` (a **string** derived from the type expression), `line:`, `col:`. Critically, `parse_impl` (`:3574-3617`) computes `for_name` from the parsed `for_type` AST and then **discards `for_type`** — it is not stored in meta anywhere. The old form's AST therefore does not retain enough information to losslessly reconstruct the new form (see Step 3).
- `interface P(t) ...` (target) → a **distinct** outer tag `{:interface, meta, body}` (confirmed by `Printer.to_string({:interface, meta, body}, ...)` at `lib/cure/compiler/printer.ex:968`), where `meta` has `name:`, `params: ["t"]` (**not** `type_params` — the printer reads `Keyword.get(meta, :params, [])` at `printer.ex:970`, so leaving the old `type_params` key in place silently renders `interface P` with no `(t)`), and `defaults:` — a map of `name => default_body_expr` computed by scanning `body` for `{:function_def, m, [expr | _]}` entries (`parser.ex:3654-3660`), which `proto`'s meta has no equivalent of at all.
- `implementation P for Int ...` (target) → a distinct outer tag `{:implementation, meta, body}` (`printer.ex:988`), where `meta` has `interface:` (**not** `protocol:`), `for:`, `for_type:` — an actual type-expression AST the printer renders via `render(for_type, ...)` (`printer.ex:990-991`; `Keyword.get(meta, :for_type)` on a node missing that key is `nil`, and rendering `nil` breaks the `for` clause) — and `as:` (named-instance support `impl` has no equivalent of).

Net effect: a rewrite that merely swaps the outer tag and reuses `impl`/`proto`'s `meta` as-is (renaming nothing) produces `{:interface, meta, body}`/`{:implementation, meta, body}` nodes the printer cannot render correctly — `params`/`defaults`/`interface`/`for_type` would all read as missing. The rewrite in Step 3 below builds new, correctly-keyed meta rather than copying it.

- [ ] **Step 2: Prerequisite red test — `impl`'s meta must retain `for_type`**

```elixir
# test/cure/compiler/parser_impl_for_type_test.exs
defmodule Cure.Compiler.ParserImplForTypeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  test "impl's meta retains the parsed for_type AST, not just its derived name" do
    src = "mod M\n  impl P for Int\n    fn e(a: Int) -> Bool = true\n"
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    [{:container, meta, _}] = find_impl(ast)
    assert match?({:variable, _, "Int"}, Keyword.get(meta, :for_type))
  end

  defp find_impl({:container, meta, ch} = node) do
    if Keyword.get(meta, :container_type) == :trait,
      do: [node],
      else: Enum.flat_map(ch, &find_impl/1)
  end

  defp find_impl({_, _, ch}) when is_list(ch), do: Enum.flat_map(ch, &find_impl/1)
  defp find_impl(_), do: []
end
```

- [ ] **Step 3: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/compiler/parser_impl_for_type_test.exs`
Expected: FAIL — `Keyword.get(meta, :for_type)` is `nil` (`parse_impl` doesn't store it yet).

- [ ] **Step 4: Write minimal implementation (prerequisite)**

Because `parse_impl` discards the parsed `for_type` AST (Step 1), add it to `impl`'s meta so the migration rule has a real type-expression node to carry over instead of reconstructing a lossy synthetic one. In `lib/cure/compiler/parser.ex`'s `parse_impl/1`, in the `meta = [...]` literal (`:3608-3615`), add `for_type: for_type`:

```elixir
    meta = [
      container_type: :trait,
      name: "#{proto_name}.#{for_name}",
      protocol: proto_name,
      for: for_name,
      for_type: for_type,
      line: token.line,
      col: token.col
    ]
```

This is additive — existing consumers of `impl` meta read specific keys and ignore unknown ones.

- [ ] **Step 5: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/compiler/parser_impl_for_type_test.exs`
Expected: PASS.

- [ ] **Step 6: Write the failing test (rewrite rule)**

```elixir
# test/cure/migrate/proto_to_interface_test.exs
defmodule Cure.Migrate.ProtoToInterfaceTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp migrate(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, out, warns} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia))
    {Printer.quoted_to_string(out), warns}
  end

  defp reparses?(src) do
    match?({:ok, _}, (with {:ok, t} <- Lexer.tokenize(src, emit_events: false), do: Parser.parse(t, emit_events: false)))
  end

  test "proto/impl are rewritten to interface/implementation and the output reparses" do
    src = "mod M\n  proto P(t)\n    fn e(a: t) -> Bool\n  impl P for Int\n    fn e(a: Int) -> Bool = true\n"
    {out, warns} = migrate(src)
    assert out =~ ~r/\binterface\s+P\(t\)/
    assert out =~ ~r/\bimplementation\s+P\s+for\s+Int/
    refute out =~ ~r/\bproto\s+P/
    refute out =~ ~r/\bimpl\s+P\s+for/
    assert Enum.any?(warns, &(&1.rule == :W_proto_to_interface))
    assert reparses?(out)
  end
end
```

- [ ] **Step 7: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/migrate/proto_to_interface_test.exs`
Expected: FAIL — `Cure.Migrate.Rules.ProtoToInterface` is undefined and unregistered.

- [ ] **Step 8: Write minimal implementation**

Create `lib/cure/migrate/rules/proto_to_interface.ex`. Build **new** meta for the target nodes rather than reusing `proto`/`impl`'s meta — the key names differ (Step 1):

```elixir
defmodule Cure.Migrate.Rules.ProtoToInterface do
  @moduledoc """
  Migration rule: rewrite the legacy `proto`/`impl` keyword forms to the
  canonical `interface`/`implementation` forms (spec §5.3, the first
  `retires_keywords` rule). Semantics-preserving spelling change; body and
  trivia are preserved. The two forms are NOT structurally symmetric
  (confirmed in Task 9 Step 1): `proto`/`impl` share the generic `:container`
  tag discriminated by `container_type`, while `interface`/`implementation`
  are their own distinct tags with differently-named and, in `interface`'s
  case, partly *derived* (`defaults`) meta — so this rule constructs fresh
  meta for the target node rather than relabeling the source node's meta.
  `enforced_in: nil` — the keyword stays live until a future edition
  schedules its retirement.
  """
  alias Cure.Migrate.Rule

  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_proto_to_interface,
      description: "legacy `proto`/`impl` is rewritten to `interface`/`implementation`",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      enforced_in: nil,
      retires_keywords: ["proto", "impl"],
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "`proto`/`impl` will be rewritten to `interface`/`implementation`"
    }
  end

  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, _ctx) do
    {new_ast, lines} = walk(ast, [])
    case lines do
      [] -> :no_change
      _ -> {:rewrite, new_ast, lines |> Enum.reverse() |> Enum.uniq()}
    end
  end

  # `proto`/`impl` are both `{:container, meta, body}`; `container_type`
  # (`:protocol` / `:trait`) is the real discriminator (Task 9 Step 1). Any
  # other `:container` (mod/rec/enum/...) recurses unchanged.
  defp walk({:container, meta, body}, lines) do
    case Keyword.get(meta, :container_type) do
      :protocol ->
        {new_body, lines} = walk(body, lines)

        new_meta = [
          name: Keyword.fetch!(meta, :name),
          params: Keyword.get(meta, :type_params, []),
          defaults: interface_defaults(new_body),
          line: Keyword.get(meta, :line),
          col: Keyword.get(meta, :col)
        ]

        {{:interface, new_meta, new_body}, [Keyword.get(meta, :line) | lines]}

      :trait ->
        {new_body, lines} = walk(body, lines)

        new_meta =
          [
            interface: Keyword.fetch!(meta, :protocol),
            for: Keyword.fetch!(meta, :for),
            for_type: Keyword.fetch!(meta, :for_type),
            as: nil,
            line: Keyword.get(meta, :line),
            col: Keyword.get(meta, :col)
          ]
          |> maybe_put(:constraints, Keyword.get(meta, :constraints))

        {{:implementation, new_meta, new_body}, [Keyword.get(meta, :line) | lines]}

      _ ->
        {new_body, lines} = walk(body, lines)
        {{:container, meta, new_body}, lines}
    end
  end

  defp walk({k, meta, ch}, lines) when is_list(ch) do
    {ch, lines} = walk(ch, lines)
    {{k, meta, ch}, lines}
  end

  defp walk({k, meta, name, inner}, lines) when is_binary(name) do
    {inner, lines} = walk(inner, lines)
    {{k, meta, name, inner}, lines}
  end

  defp walk(l, lines) when is_list(l), do: Enum.map_reduce(l, lines, &walk/2)
  defp walk(other, lines), do: {other, lines}

  # Mirrors parse_interface's own `defaults` derivation (parser.ex:3654-3660):
  # a method with a `= body` (a non-empty function_def) is a default.
  defp interface_defaults(body) do
    body
    |> Enum.flat_map(fn
      {:function_def, m, [expr | _]} -> [{Keyword.get(m, :name), expr}]
      _ -> []
    end)
    |> Map.new()
  end

  defp maybe_put(kw, _key, nil), do: kw
  defp maybe_put(kw, key, val), do: Keyword.put(kw, key, val)
end
```

If confirmation at implementation time turns up further meta differences beyond those Step 1 already found (e.g. an interior key spelled slightly differently), adjust the two `new_meta` builders accordingly — the test asserts the *rendered* output via `Printer.quoted_to_string/2`, which is the real contract, not the meta shape itself.

Register it in `Cure.Migrate.rules/0` (append after `RemovedModule.rule()`):

```elixir
      Cure.Migrate.Rules.RemovedModule.rule(),
      Cure.Migrate.Rules.ProtoToInterface.rule()
```

- [ ] **Step 9: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/migrate/proto_to_interface_test.exs`
Expected: PASS.

- [ ] **Step 10: Monotone + lexer regression**

Run: `MIX_ENV=test mix test test/cure/migrate/monotone_property_test.exs test/cure/compiler/edition_lexer_test.exs test/cure/compiler/ test/cure/migrate/`
Expected: PASS — the new rule is idempotent (a file already using `interface`/`implementation` yields `:no_change`), `retired_keywords("2026")` is still `[]` because this rule's `enforced_in` is `nil`, and the broader `test/cure/compiler/` run confirms adding `for_type` to `impl`'s meta (Step 4) didn't disturb any existing parser test that pattern-matches or enumerates that meta's keys.

- [ ] **Step 11: Commit**

```bash
git add lib/cure/migrate/rules/proto_to_interface.ex lib/cure/migrate.ex test/cure/migrate/proto_to_interface_test.exs
git commit -m "feat(migrate): proto/impl -> interface/implementation rule (first retires_keywords rule)"
```

---

## Phase 6 — Edition-crossing `cure migrate`

### Task 10: Edition-aware rule selection + two-phase migrate + edition bump

**Files:**
- Modify: `lib/cure/migrate.ex` (add `rules_for_crossing/2`, `blocking_manual/2`)
- Modify: `lib/cure/project.ex` (add a lossless `set_edition/2` writer)
- Modify: `lib/cure/cli.ex:139` (`cure migrate` command → edition-aware two-phase)
- Test: `test/cure/migrate/edition_crossing_test.exs`, `test/cure/cli/migrate_edition_cli_test.exs`

**Interfaces:**
- Consumes: `Cure.Edition.compare/2`, `Cure.Migrate.run_to_fixpoint/2`, `Cure.Migrate.git_guard/1`.
- Produces: `Cure.Migrate.rules_for_crossing(target_edition, rules) :: [Rule.t()]` (mandatory `enforced_in != nil and <= target`, plus all `:machine`/`:review` with `since <= target`); `Cure.Migrate.blocking_manual(target, rules) :: [Rule.t()]` (the `:manual` rules with `enforced_in <= target`); `Cure.Project.set_edition(path, edition) :: :ok | {:error, term}` (lossless insert/replace of `edition = "…"` under `[project]`).

- [ ] **Step 1: Write the failing test (rule selection + bump writer)**

```elixir
# test/cure/migrate/edition_crossing_test.exs
defmodule Cure.Migrate.EditionCrossingTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate

  test "rules_for_crossing includes every rule relevant to reaching the target, :manual included" do
    picked = Migrate.rules_for_crossing("2026", Migrate.rules()) |> Enum.map(& &1.id)
    assert :W_module_rename in picked          # :machine, proactive (since <= target)
    assert :W_uppercase_type_var in picked     # :review, proactive — must be included (§5.1/§7.2)

    # :manual is included too — NOT because it's tier-eligible for the
    # proactive clause (it isn't), but because its `enforced_in: "2026"` makes
    # it spec §7.2's "mandatory" bullet, which is tier-unrestricted. It has to
    # run through run_to_fixpoint so its {:warn, _} result actually fires and
    # lands in `warns` — that firing is the ONLY way Task 11's
    # plan_migration_source can detect it via blocking_manual and refuse the
    # edition bump. Excluding :manual rules here would make that detection
    # permanently vacuous (removed_module.ex's detect_and_rewrite always
    # returns {:warn, _}, never {:rewrite, _}, so its presence in this list
    # can never mutate the AST — only surface the warning).
    assert :W_removed_module in picked
  end

  test "blocking_manual reports :manual rules enforced at/before the target" do
    ids = Migrate.blocking_manual("2026", Migrate.rules()) |> Enum.map(& &1.id)
    assert :W_removed_module in ids
  end

  test "set_edition inserts an edition key under [project] losslessly" do
    dir = Path.join(System.tmp_dir!(), "cureset_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "Cure.toml")
    File.write!(path, "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
    # existing keys preserved
    assert project.name == "demo"
    assert project.version == "0.1.0"
  end

  test "set_edition replaces an existing edition key rather than duplicating it" do
    dir = Path.join(System.tmp_dir!(), "cureset2_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "Cure.toml")
    File.write!(path, "[project]\nname = \"demo\"\nedition = \"2026\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    body = File.read!(path)
    assert length(Regex.scan(~r/^edition = /m, body)) == 1
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/migrate/edition_crossing_test.exs`
Expected: FAIL — `rules_for_crossing/2`, `blocking_manual/2`, `set_edition/2` undefined.

- [ ] **Step 3: Write minimal implementation (selection + writer)**

Add to `lib/cure/migrate.ex`:

```elixir
  @doc "Rules to apply when crossing to `target` (spec §7.2)."
  @spec rules_for_crossing(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def rules_for_crossing(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      mandatory = r.enforced_in != nil and Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
      proactive = r.tier in [:machine, :review] and Cure.Edition.compare(r.since, target) in [:lt, :eq]
      mandatory or proactive
    end)
  end

  @doc "The :manual rules whose old form is illegal at `target` (block the bump)."
  @spec blocking_manual(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def blocking_manual(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      r.tier == :manual and r.enforced_in != nil and
        Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
    end)
  end
```

Add to `lib/cure/project.ex` a lossless writer:

```elixir
  @doc """
  Insert or replace `edition = "<edition>"` under the `[project]` table of the
  `Cure.toml` at `path`, preserving all other lines. Lossless line edit — does
  not reformat the file.
  """
  @spec set_edition(Path.t(), Cure.Edition.t()) :: :ok | {:error, term()}
  def set_edition(path, edition) do
    with {:ok, body} <- File.read(path) do
      lines = String.split(body, "\n")
      new = upsert_edition(lines, edition)
      File.write(path, Enum.join(new, "\n"))
    end
  end

  defp upsert_edition(lines, edition) do
    kv = "edition = \"#{edition}\""

    cond do
      Enum.any?(lines, &Regex.match?(~r/^\s*edition\s*=/, &1)) ->
        Enum.map(lines, fn l -> if Regex.match?(~r/^\s*edition\s*=/, l), do: kv, else: l end)

      true ->
        insert_after_project_header(lines, kv)
    end
  end

  defp insert_after_project_header(lines, kv) do
    idx = Enum.find_index(lines, &Regex.match?(~r/^\s*\[project\]\s*$/, &1))
    if idx, do: List.insert_at(lines, idx + 1, kv), else: ["[project]", kv | lines]
  end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/migrate/edition_crossing_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex lib/cure/project.ex test/cure/migrate/edition_crossing_test.exs
git commit -m "feat(migrate): edition-crossing rule selection + lossless Cure.toml edition writer"
```

### Task 11: Wire the two-phase behavior into the `cure migrate` CLI

**`cmd_migrate` already exists and is not a blank slate.** `cure migrate` (`lib/cure/cli.ex:1212`, dispatched from `:139`) already has a full pipeline this task must integrate with, not duplicate:

- `migrate_targets/1` (`:1231`) — path/glob selection.
- `migrate_git_guard/3` (`:1247`) — the existing preflight guard, `--check`/`--print`-exempt.
- `migrate_preflight_all/1` → `migrate_preflight_file/1` (`:1262`, `:1278`) — **single-pass** `Cure.Migrate.run/2` per file, then its own manual reparse+comment-diff check (`migrate_output_ok?/3` at `:1304`, `migrate_reparses?/2` at `:1309`, `migrate_comments/1` at `:1317`).
- `migrate_strict_gate/2` (`:1333`) — **today, ANY fired warning blocks** ("`--strict`: any fired migration warning becomes an error; write nothing"), pinned by `test/cure/cli/migrate_cli_test.exs:168-175` (`assert {:error, {:strict_warnings, [^f]}} = CLI.cmd_migrate([f], strict: true)`).
- `migrate_apply/3` (`:1345`) — check/print/write.

Spec §6.1 (bounded fixpoint, not single-pass) and §8 (`--strict` promotes only fixable tiers, never `:manual`) are incompatible with `migrate_preflight_file/1` and `migrate_strict_gate/2` as they stand today. This task **replaces** those two functions (not the whole pipeline — `migrate_targets/1`, `migrate_git_guard/3`, `migrate_apply/3` keep their shape) and, because the change is deliberately observable, requires updating `test/cure/cli/migrate_cli_test.exs:168-175`'s assertion to the new tier-based behavior — this is the same kind of disclosed, tested behavior change Phase 2 made to `cure build` normalization, not a silent regression, and the old assertion must not simply be deleted: replace it with one that pins the *new* contract (a `:machine`/`:review` warning promotes under `--strict`; a lone `:manual` warning does not).

**Files:**
- Modify: `lib/cure/cli.ex:69` (switches schema — add `edition: :string`), `:1212` `cmd_migrate` and its `migrate_preflight_file/1`/`migrate_strict_gate/2` helpers
- Test: `test/cure/cli/migrate_edition_cli_test.exs`; update `test/cure/cli/migrate_cli_test.exs:168-175`'s `--strict` assertion (Step 5)

**Interfaces:**
- Consumes: `Cure.Migrate.{rules_for_crossing/2, blocking_manual/2, run_to_fixpoint/2, git_guard/1}`, `Cure.Edition.{current/0, parse/1, compare/2}`, `Cure.Project.{load/1, set_edition/2}`.
- Produces: `cure migrate [--edition YYYY] [--check] [--print] [--strict] [paths…]` that (phase 1) rewrites targets to a fixpoint under the target edition's rule set, then (phase 2) bumps the edition marker — refusing the bump if a `blocking_manual` item remains, and refusing a downgrade target. `--strict` now promotes only fixable-tier (`:machine`/`:review`) warnings; `:manual` warnings are never promoted (they already block phase 2 regardless of `--strict`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/cli/migrate_edition_cli_test.exs
defmodule Cure.CLI.MigrateEditionCLITest do
  use ExUnit.Case
  # These exercise the migrate command's pure planning path. Use the exposed
  # helper Cure.CLI is refactored to call (cmd_migrate delegates planning to a
  # testable function) rather than shelling out.

  test "a downgrade target is refused" do
    # "2025" is not a minted edition, but Cure.Edition.compare/2 is deliberately
    # allow-list-independent (Task 1) so a hypothetical older edition is a valid
    # probe here — plan_migration/1 only compares, it never validates target
    # against the known-editions allow-list (that happens earlier, when the
    # CLI's --edition flag is parsed via Cure.Edition.parse/1).
    assert {:error, :downgrade} = Cure.CLI.plan_migration(target: "2025", current: "2026")
  end

  test "a blocking :manual item prevents the edition bump" do
    # Build a source that references a removed module (Std.Refine) → :manual fires.
    src = "mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n"
    assert {:blocked, ids} = Cure.CLI.plan_migration_source(src, target: "2026")
    assert :W_removed_module in ids
  end

  test "a clean source migrates and reports a pending edition bump" do
    src = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"
    assert {:ok, out, _warns, bump} = Cure.CLI.plan_migration_source(src, target: "2026")
    assert out =~ "Std.Equatable"
    assert bump == "2026"
  end

  test "--strict promotes fixable-tier (:machine/:review) warnings but never :manual (spec §8)" do
    # a :machine warning (module rename) is promoted under strict
    fixable = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"
    assert {:error, {:strict_violation, ids}} =
             Cure.CLI.plan_migration_source(fixable, target: "2026", strict: true)
    assert :W_module_rename in ids

    # a :manual warning (removed module) is NOT promoted — it stays a block, not a strict error
    manual = "mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n"
    assert {:blocked, ids2} = Cure.CLI.plan_migration_source(manual, target: "2026", strict: true)
    assert :W_removed_module in ids2
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `MIX_ENV=test mix test test/cure/cli/migrate_edition_cli_test.exs`
Expected: FAIL — `plan_migration/1`, `plan_migration_source/2` undefined.

- [ ] **Step 3: Write minimal implementation**

Refactor `cmd_migrate` in `lib/cure/cli.ex` to delegate its decision logic to two pure, testable functions, keeping the IO (git-guard, file read/write, printing) in the command:

```elixir
  @doc false
  # Pure planning: refuse a downgrade target (target older than the project's
  # current declared edition).
  def plan_migration(opts) do
    target = Keyword.fetch!(opts, :target)
    current = Keyword.get(opts, :current, Cure.Edition.current())
    if Cure.Edition.compare(target, current) == :lt, do: {:error, :downgrade}, else: {:ok, target}
  end

  @doc false
  # Pure planning for one source: run the crossing rule set to a fixpoint; if a
  # blocking :manual item fired, report it; else return the migrated source and
  # the pending edition bump.
  def plan_migration_source(src, opts) do
    target = Keyword.fetch!(opts, :target)
    {:ok, toks, trivia} = Cure.Compiler.Lexer.tokenize(src, trivia: true, edition: target)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, emit_events: false, edition: target)
    attached = Cure.Compiler.Trivia.attach(ast, trivia)
    rules = Cure.Migrate.rules_for_crossing(target)

    case Cure.Migrate.run_to_fixpoint(attached, rules: rules) do
      {:ok, out_ast, warns} ->
        blocking =
          Cure.Migrate.blocking_manual(target)
          |> Enum.map(& &1.id)
          |> Enum.filter(fn id -> Enum.any?(warns, &(&1.rule == id)) end)

        strict? = Keyword.get(opts, :strict, false)
        fixable_fired = fixable_tier_warnings(warns, target)

        cond do
          blocking != [] ->
            # :manual blocks the bump regardless of --strict (never promoted, §8)
            {:blocked, blocking}

          strict? and fixable_fired != [] ->
            # --strict promotes fixable-tier (:machine/:review) warnings to errors
            {:error, {:strict_violation, fixable_fired}}

          true ->
            {:ok, Cure.Compiler.Printer.quoted_to_string(out_ast), warns, target}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  # The ids of fired warnings whose rule is a fixable tier (:machine/:review).
  defp fixable_tier_warnings(warns, target) do
    fixable_ids =
      Cure.Migrate.rules_for_crossing(target)
      |> Enum.filter(&(&1.tier in [:machine, :review]))
      |> Enum.map(& &1.id)
      |> MapSet.new()

    warns |> Enum.map(& &1.rule) |> Enum.filter(&MapSet.member?(fixable_ids, &1)) |> Enum.uniq()
  end
```

The `:blocked` clause is checked **before** `strict?`, so a `:manual` item is never promoted to a `:strict_violation` — it stays a block (spec §8: `--strict` does not promote `:manual`).

Then wire `plan_migration/1`/`plan_migration_source/2` into the **existing** pipeline rather than beside it:

- Add `edition: :string` to the switches list in `lib/cure/cli.ex:69` (next to the existing `strict: :boolean`) so `--edition YYYY` parses.
- In `cmd_migrate` (`:1212`): resolve the raw target string via `Keyword.get(opts, :edition)`, defaulting to `Cure.Edition.current()` when `--edition` was not given. **Validate a user-supplied value through `Cure.Edition.parse/1` before anything else** and abort with its `{:error, {:unknown_edition, _}}` — do not let an unvalidated `--edition` string reach `plan_migration_source/2` or `Cure.Project.set_edition/2`: `set_edition/2` writes whatever string it is given verbatim (it does not itself validate), so an unchecked typo (e.g. `--edition 2062`) would otherwise get written into `Cure.toml` and only surface as a broken project on the *next* `Cure.Project.load/1` call, far from the command that caused it. Only after that validation passes, call `plan_migration/1` with the validated target and abort on `{:error, :downgrade}` before touching any file.
- **Replace** `migrate_preflight_file/1`'s body (`:1278-1294`) to call `plan_migration_source/2` instead of `Cure.Migrate.run/2` + its own `migrate_output_ok?/3` check — `run_to_fixpoint/2` (Task 7) already performs the reparse+comment verify `migrate_output_ok?/3` duplicated, so that private helper (and `migrate_reparses?/2`/`migrate_comments/1`) can be deleted once nothing calls them. `migrate_preflight_all/1` keeps its shape (map + partition on `:ok`/`:error`), it just now also has to route `{:blocked, ids}` results the same way `plan_migration_source/2` reports them (as a phase-1 failure that skips the write, not a hard `{:error, file}`, so the CLI can report the hand-port sites per file rather than a bare `{:error, {:preflight_failed, [...]}}`).
- **Replace** `migrate_strict_gate/2` (`:1333-1343`) to promote via `fixable_tier_warnings/2` instead of "any warning blocks": iterate `results`, and for any file whose warnings include a fixable-tier id, return `{:error, {:strict_violation, ids}}`; a file blocked only by `:manual` warnings is reported by the existing `:blocked` path, not promoted here.
- On success (no downgrade, no `:blocked`, no `:strict_violation`) and not `--check`/`--print`: `migrate_apply/3` writes the files as today, then (only if every targeted file succeeded) bump the edition — `Cure.Project.set_edition/2` for a whole-project run, or splice/replace the `@edition` pragma for a single standalone file. `--check` additionally lists the pending bump; `--print` additionally prints it.

Note: `blocking_manual` currently matches `Std.Refine`/`Std.Equal` references. The `plan_migration_source` filter above only treats a `:manual` rule as blocking **if it actually fired** on this source (its id appears in `warns`) — a clean file with no removed-module reference is not blocked.

- [ ] **Step 4: Run test to verify it passes**

Run: `MIX_ENV=test mix test test/cure/cli/migrate_edition_cli_test.exs`
Expected: PASS.

- [ ] **Step 5: Update the stale `--strict` pin, then run the CLI regression**

`test/cure/cli/migrate_cli_test.exs:168-175` asserts today's "any warning blocks" `--strict` behavior; replace that assertion with one pinning the new tier-based contract (a fixable-tier warning still blocks; add a sibling case showing a lone `:manual`-only warning does *not* trigger `{:error, {:strict_violation, _}}` under `--strict` — it still blocks via the ordinary `:blocked`/phase-2-refusal path, per §8). This is the one pre-existing assertion this task is expected to change; every other pre-existing `cure migrate` behavior (in-place/`--check`/`--print` writing, git-guard) is unaffected.

Run: `MIX_ENV=test mix test test/cure/cli/ test/mix/tasks/cure_rewrite_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/cli.ex test/cure/cli/migrate_edition_cli_test.exs
git commit -m "feat(cli): edition-aware two-phase cure migrate (fixpoint rewrite + edition bump)"
```

---

## Phase 7 — Antigen coverage + final gate

### Task 12: Antigen coverage probes for the new lexer/fixpoint paths

**Files:**
- Modify: `lib/antigen/assays/kernel_probe.ex` (or the migration-facing assay module — locate the one that exercises `Cure.Migrate`/lexer), plus the generator + challenge registration
- Test: the existing Antigen coverage-baseline gate

**Interfaces:**
- Consumes: `Cure.Edition.retired_keywords/2`, `Cure.Migrate.run_to_fixpoint/2`.

- [ ] **Step 1: Identify the coverage-baseline gate and current floor**

Run: `MIX_ENV=test mix test test/antigen/ 2>&1 | tail -20`
Expected: the coverage gate passes at the current floor; note the modules whose lines the new code adds (`lib/cure/edition.ex`, the new `run_to_fixpoint` lines in `lib/cure/migrate.ex`).

- [ ] **Step 2: Add probes exercising the new paths**

Following the existing probe pattern in `lib/antigen/assays/kernel_probe.ex` (an `evaluate/1` clause + a `matches?/2` oracle + registration in the generator `@probes` and challenge `@known_atoms`), add two probes:
- `edition_retired_keywords` — calls `Cure.Edition.retired_keywords("2027", [fixture_rule])` and asserts the retired list; warms `lib/cure/edition.ex`.
- `migrate_fixpoint_converges` — calls `Cure.Migrate.run_to_fixpoint/2` on a two-rule chain and asserts convergence; warms the `do_fixpoint` lines.

(Use the same helper/registration mechanics the Phase-3 value-surface probes used — grep `@probes` in `lib/antigen/generators/kernel_probe.ex` and `@known_atoms` in `lib/antigen/challenge.ex`.)

- [ ] **Step 3: Re-record the coverage baseline**

Run: `MIX_ENV=test mix antigen cover --record-new-coverage-baseline`
Then: `MIX_ENV=test mix test test/antigen/`
Expected: PASS at the new (raised) floor.

- [ ] **Step 4: Commit**

```bash
git add lib/antigen/ test/antigen/
git commit -m "test(antigen): coverage probes for edition keyword-set + migrate fixpoint"
```

### Task 13: Full-suite gate

- [ ] **Step 1: Run the whole suite once**

Run: `MIX_ENV=test mix test`
Expected: PASS — target `0 failures`. (Baseline before this work was 3778 passed.) If any pre-existing test now fails, it is either a real regression (fix it) or a test that legitimately must change because tier semantics changed `cure build` normalization (update it only if it asserts the *old* non-normalizing behavior for a now-`:machine` rule, and note why).

- [ ] **Step 2: Commit any test-fixups discovered**

```bash
git add -A
git commit -m "test(edition): reconcile suite with tier-driven build normalization"
```

---

## Self-Review

**Spec coverage:**
- §2.1 scope C (rewrite both, no stdlib resolver) → Tasks 4/9 (rewrite rules), no resolver task (correctly absent). ✓
- §2.2/§3.1 identity + order → Task 1. ✓
- §2.3/§3.2 precedence + resolve → Task 2. ✓
- §2.4 default latest → Task 1 (`current/0`) + Task 2 (`resolve_project` fallbacks). ✓
- §2.5/§5 tier replaces tolerate_safe? → Task 3; re-tag → Task 4. ✓
- §2.6/§8 error-later = edition boundary + `--strict` fixable-only → §8 is policy realized by tiers (Task 4) + lexer retirement (Task 5); `--strict` promotion is realized in Task 11 (`plan_migration_source/2` `strict:` path + `fixable_tier_warnings/2`, with the `:blocked` clause ordered before the strict clause so `:manual` is never promoted) and gated by Task 11 Step 1's `--strict` test. ✓
- §2.7/§6 verify + fixpoint + monotone → Tasks 7/8. ✓
- §4 edition-parameterized lexer/parser → Tasks 5/6. ✓
- §5.3 exemplar `proto`→`interface` → Task 9. ✓
- §7 edition-crossing two-phase → Tasks 10/11. ✓
- §9 testing gates → each realized in the task that builds the feature; monotone property (Task 8), resolution (Task 2), lexer (Task 5), tier (Tasks 3/4), fixpoint (Task 7), two-phase (Tasks 10/11), exemplar (Task 9), Antigen (Task 12). ✓

**Placeholder scan:** Task 9 Step 1 was rewritten during the recursive-skeptical-review pass below to state the parser's real `proto`/`impl`/`interface`/`implementation` node shapes (confirmed by direct source read, not a runtime discovery command) — they are asymmetric (shared `:container`/`container_type` tag vs. distinct tags with renamed and partly-derived meta), which the original placeholder-swap sketch did not account for; Task 9 Steps 6-8 build correctly-keyed new meta instead of relabeling the source node. No `TBD`/`handle edge cases`/`similar to` remain.

**Type consistency:** `tier` values `:machine|:review|:manual`, edition strings `"2026"`, and function names (`retired_keywords/2`, `run_to_fixpoint/2`, `rules_for_crossing/2`, `blocking_manual/2`, `set_edition/2`, `plan_migration_source/2`, `fixable_tier_warnings/2`) are used identically across the tasks that define and consume them. Rule ids (`:W_module_rename`, `:W_uppercase_type_var`, `:W_removed_module`, `:W_proto_to_interface`) match the existing registry and Task 9's new rule.

**Fix applied inline:** the `--strict` gap is closed for real — Task 11 Step 1 gains a `--strict` test (fixable promoted, `:manual` not) and Task 11 Step 3 gains the `strict:`/`fixable_tier_warnings/2` implementation with `:blocked` ordered before the strict clause.

**Recursive-skeptical-review hardening (this pass):** twelve confirmed defects fixed against the real worktree source, none of them present in the spec — all were plan-authoring errors introduced while translating the spec into task-level code:
1. Task 2 Step 3 contained two mutually-exclusive snippets, the first calling a `parse_toml_project/1` function that does not exist anywhere in the codebase — collapsed to the one working two-step approach (raw value captured in `parse_toml/1`, validated in `load/1`).
2. Task 6's `@edition` placement-check snippet matched the atom `:edition` against `dec_name`, which `parse_at/1` binds to a **string** (`to_string(name_token.value)`) — fixed to `dec_name == "edition"` and moved ahead of the `@module_level_decorators` branch it must not be shadowed by.
3. Task 9's rewrite was designed against invented tags (`:protocol`, `:impl_block`) and a nonexistent `parse_protocol` function; the real `proto`/`impl` share the generic `:container` tag (discriminated by `container_type`) while `interface`/`implementation` are distinct tags whose meta the printer reads under different key names (`params` not `type_params`, `interface` not `protocol`) and partly-derived fields (`defaults`) — a bare tag swap would silently drop the rendered `(t)` type-parameter list and crash-render the `for` clause (`for_type` is nil). Also found and fixed a real data-loss gap: `parse_impl` never stored the parsed `for_type` AST, only a derived string — added as a red-test-led prerequisite step (Task 9 Steps 2-5) before the rewrite rule itself.
4. Task 11 invented a disconnected `plan_migration`/`plan_migration_source` pair without reconciling them with `cmd_migrate`'s existing, working pipeline (`migrate_preflight_file/1`, `migrate_strict_gate/2`), and its regression step falsely claimed pre-existing `--strict` behavior ("any warning blocks", pinned by `test/cure/cli/migrate_cli_test.exs:168-175`) would be "preserved" when spec §8 requires it to change to tier-based promotion — rewrote Task 11 to explicitly replace those two helpers and to require updating (not silently orphaning) the stale pin.
5. The plan had no blanket instruction that tests, once correct, are changed only by fixing the implementation — added as a Global Constraint, since Task 11's now-explicit legitimate test update (finding 4) needs that rule stated to not read as licence for expedient rewrites elsewhere.
6. Task 3's `@enforce_keys` addition (`tier`/`since` required) and Task 4's re-tag of the five existing rule files were two separate commits, but Elixir checks `@enforce_keys` at compile time for literal `%Struct{}` construction (confirmed by direct `elixir` repro) — landing Task 3 alone makes the whole project fail to *compile*, so Task 3's own Step 4 ("run test to verify it passes") could never actually pass in isolation. Fixed by making Task 3 explicitly not commit on its own; it and Task 4 land as one atomic commit.
7. Spec §3.2 point 2 ("a project with a Cure.toml but no edition key... emits a one-time advisory") was mapped to Task 2 in the spec-coverage table but never implemented or tested there. Added a `:persistent_term`-backed one-time advisory (mirroring the existing memoisation pattern in `lib/cure/types/stdlib.ex`) with red tests for both "fires" and "fires once."
8. Task 7's `run_to_fixpoint/2` docstring and spec §6.1/§9 both require verify to check comment-preservation, but the implementation's `verify/2` only reparse-checked, with an inline comment admitting it punted comment-checking to "the caller-level lossless gate in tests" — which no test in Task 7 (or anywhere) actually exercised. Added a red test (a rule that drops a node's `:leading` trivia) and rewrote `verify/2` to diff comment texts against the true original baseline (captured once, not pass-to-pass, so a loss on pass 3 isn't masked by passes 1-2 being clean).
9. Task 10's own `rules_for_crossing/2` test asserted `refute :W_removed_module in picked` (a `:manual` rule) even though its own test description said "excludes nothing tier-wise" and spec §7.2's "mandatory" bullet is tier-unrestricted (any rule with `enforced_in <= target` runs, precisely so a `:manual` rule's `{:warn, _}` result can fire). Had this test been implemented literally, `rules_for_crossing`'s output would exclude `:manual` rules from the fixpoint's rule set entirely — silently making Task 11's `blocking_manual` cross-check against `warns` permanently vacuous (a file referencing a removed module would never be blocked), contradicting Task 11's own Step 1 test for that exact scenario. Fixed the assertion to include `:W_removed_module` with an explanation of why.
10. Task 9's steps were renumbered when the AST-shape rewrite inserted a new prerequisite (Steps 2-5), but the final "Commit" step was left as "Step 6" — colliding with the already-existing Step 6 ("Write the failing test (rewrite rule)") earlier in the same task. Renumbered the commit step to Step 11, matching the task's actual 1-through-10 sequence.
11. Task 11 Step 1's downgrade test called `Cure.CLI.plan_migration(target: "2026", current: "2026", downgrade_probe: "2025")` expecting `{:error, :downgrade}`, but Step 3's own implementation compares `target` against `probe` (`Cure.Edition.compare(target, probe) == :lt`) — with `target: "2026"` and `probe: "2025"`, `compare("2026", "2025")` is `:gt`, so the function as specified returns `{:ok, "2026"}`, not `{:error, :downgrade}`; the test could never pass against the implementation it was paired with. The `:downgrade_probe` indirection (distinct from `:current`) added confusion without adding capability — `Cure.Edition.compare/2` is already deliberately allow-list-independent (Task 1), so an unminted lower edition works directly as `:current`. Simplified `plan_migration/1` to compare `target` against `current` only, and fixed the test to `plan_migration(target: "2025", current: "2026")`, a value pairing that is actually a downgrade under the stated comparison.
12. Task 11's CLI-wiring prose resolved `--edition`'s raw string via `Keyword.get(opts, :edition) |> ... |> Cure.Edition.current()` fallback but never specified validating it against `Cure.Edition.parse/1` before use. `Cure.Project.set_edition/2` (Task 10) writes whatever string it is given verbatim with no validation of its own, so a typo'd `--edition 2062` would silently write an invalid edition into `Cure.toml`, surfacing only on the *next*, unrelated `Cure.Project.load/1` call as `{:error, {:unknown_edition, "2062"}}` — far from the command that caused it. Fixed the wiring prose to validate the user-supplied value through `Cure.Edition.parse/1` and abort immediately on `{:error, {:unknown_edition, _}}`, before it reaches `plan_migration_source/2` or `set_edition/2`.
