# `use`-Propagated Fixity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make operator fixity (precedence groups + `infix`/`prefix`/`postfix` declarations) propagate through `use`, uniformly for user modules and the stdlib, with `@prelude` making the core operators ambient — replacing the location-based built-in-rebind rule with a single per-module conflict invariant.

**Architecture:** A module `M`'s parse-time fixity table becomes `fixity(M) = own(M) ∪ ⋃ own(X for X in use_reach(M)) ∪ ⋃ own(P-closures for prelude providers)`. Extraction of a module's own declarations is *table-independent* (a tolerant harvest pass), so no dependency-ordered parse is needed — only on-demand, name-based `use`-graph BFS. Assembly happens inside `Parser.parse/2` between its existing harvest and authoritative passes. Protection stops being a privileged list and becomes "at most one fixity per lexeme per slot, and one body per precedence-group name, within any assembled table."

**Tech Stack:** Elixir; `Cure.Compiler.Parser` and friends. No new deps.

## Global Constraints

- **Zero TCB change.** Nothing under `lib/cure/core/**` is modified. Every task below lives in `lib/cure/compiler/**`, `lib/cure/elab/**`, `lib/std/operators.cure`, `lib/cure/compiler.ex`, `lib/cure/cli.ex`, `lib/cure/project.ex` (Task 10's driver-threading needs the latter three — direct siblings of, not inside, `lib/cure/compiler/`, so `lib/cure/compiler/**` alone doesn't cover them), or `test/**`.
- **Fixity is syntactic**, resolved at parse time. It must not depend on elaboration, type-checking, or name resolution.
- **Fixity extraction for a module must never fail because that module's function bodies fail to parse** — declarations are inert and extracted via the tolerant harvest pass with `synchronize_to_statement` recovery.
- **Overloading (multiple `fn <op>`) is orthogonal to fixity and never produces a fixity conflict.** The conflict check keys on `{:fixity, ...}` / `{:precedencegroup, ...}` declaration nodes only, never on function definitions.
- **use_reach and target-module scanning use only the tolerant harvest, never a full `Parser.parse` of the target** — this both honors table-independence and prevents unbounded resolution recursion.
- **Commits authored as the user only, no co-sign trailer.** Verify with `git show -s --format='%an <%ae>'` → `Made In Heaven <madeinheaven@madeinheaven.com>`.
- **One build/test run at a time.** Never launch concurrent `mix test`.
- Full gate (`mix test`) green before merge.
- **Work inside the worktree** `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity` on branch `autopilot/use-propagated-fixity`. All paths below are worktree-relative.

## Verified current-state anchors (read before starting)

Exact signatures/line numbers as of the branch HEAD (`73533a50`). Confirm they still hold before editing.

- `lib/cure/compiler/parser.ex`
  - `def parse(tokens, opts \\ [])` at **:181**; reads `:file`,`:emit_events`,`:edition`,`:prelude_macros`,`:builtin_macros` at **:182-186**. **No `:fixity` / `:prelude_providers` option exists.**
  - Phase 1 harvest builds `harvest_state` (**:192-201**), `{harvest_exprs, _} = parse_program(harvest_state)` (**:203**), `module_fixity = session_extend_fixity_table(builtin_fixity, harvest_exprs)` (**:207**). ← **injection point.**
  - `builtin_fixity = session_builtin_fixity_table()` (**:190**).
  - Phase 2 builds fresh state with `fixity_table: module_fixity` (**:238**), returns `{:ok, ast}` or `{:error, Enum.reverse(errors)}` (**:255-258**).
  - `defp parse_program(state)` **:2164**; `defp synchronize_to_statement(state)` **:8972-8983**; `@definition_keywords` **:77-90**.
  - `defp session_builtin_fixity_table` **:2249** (returns `FixityTable.new()` when `Process.get(:cure_building_fixity_table)`, else `BuiltinFixity.table()`); `defp session_extend_fixity_table(base, ast)` **:2258**.
  - `alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable, Precedence}` **:40**. `put_tokens/2` exists. State struct **:49-72** has `fixity_table: nil` field.
- `lib/cure/compiler/parser/fixity_table.ex`
  - struct `defstruct groups: %{}, ops: %{}, ranks: %{}, reach: %{}` **:42**; `@type fixity :: :infix | :prefix | :postfix` **:40**; `@type group_name :: atom()` **:38**.
  - `def new` **:54**; `def add_group(table, name, opts \\ [])` **:67** (last-write-wins `Map.put`, `|> recompute()`); `def add_infix/add_prefix/add_postfix(table, lexeme, group, opts \\ [])` **:86/90/94** → `defp add_op(...)` **:96** stores `%{group: group}` at `ops[lexeme][fixity]`; `def declares?/2` **:168**; `def group_of/2` **:212**; `def cyclic_groups/1` **:234**; `def incomparable?/3` **:176**.
- `lib/cure/compiler/parser/builtin_fixity.ex` (full file, 163 lines)
  - `@fixity_table_key` **:24**; `@stdlib_source_dir Path.expand("../../../std", __DIR__)` **:27**; `def table()` **:31** (persistent_term memo); `def extend(base, ast)` **:49**; `defp compute` **:55** (re-entrancy guard `Process.put(:cure_building_fixity_table, true)` **:56**, `try/after` restore **:72-77**); `defp operators_source_path` **:83**; `defp build(ast, base)` **:100** (groups via `add_group` then fixity via `add_fixity_op`); `defp add_fixity_op(table, meta)` **:125**; `defp collect_fixity_nodes/1` **:144**.
- `lib/cure/compiler/dep_graph.ex`
  - `def scan(paths, opts \\ [])` **:50**; struct `defstruct nodes: %{}, modules: %{}` **:27**; `modules` keyed **name→path**, built only from `is_binary(m)` nodes **:60**; prelude via `Map.put(:prelude_provider?, prelude_decorated?(ast))` **:210**, aggregated **:64-68**.
  - `defp scan_file(path)` **:181-220**; the error path `case Cure.Compiler.parse_source(source, file: path) do {:error, reason} -> %{base | parse_error: reason}` **:200-202** (module stays nil → file dropped).
  - `base` map **:182-190**: `%{path, module: nil, line: nil, blank?: false, parse_error: nil, order_deps: [], closure_deps: []}`; `order_deps` entries `%{target, line}`.
  - `defp collect_uses(ast)` **:284** (matches `{:import, meta, _}`, `meta[:source]`); `defp prelude_decorated?(ast)` **:242**; `def order(%__MODULE__{...})` **:82** returns `{:ok, ordered, cycles}`.
- `lib/cure/compiler.ex`: `def compile_file(path, opts \\ [])` **:45**; `def compile_string(source, opts \\ [])` **:85** (unpacks `file/output_dir/emit?/declared_phases` **:86-89**; internal `defp parse(tokens, file, emit?, edition)` **:249** → `Parser.parse(tokens, file:, emit_events:, edition:)` **:250** — no fixity/prelude thread); `def parse_source(source, opts \\ [])` **:166** (`{:ok, list()} | {:error, term()}`).
- `lib/cure/cli.ex`: `DepGraph.scan(files)` **:450**, `order` **:452**, `Enum.each(ordered, &compile_one(&1, compile_opts, verbose?))` **:465**, `defp compile_one(path, opts, verbose?)` **:468** → `Cure.Compiler.compile_file(path, opts)` **:471**.
- `lib/cure/project.ex`: `DepGraph.scan(discovered)` **:765**, `order` **:767**; `defp compile_all_files(files, output_dir, emit?, check?, declared_phases, source_roots)` **:940** builds `opts` **:941-952**, `Cure.Compiler.compile_file(file, opts)` **:957**.
- `lib/cure/compiler/printer.ex`: `def quoted_to_string(ast, opts \\ [])` **:61**, default `table = Keyword.get(opts, :fixity) || BuiltinFixity.table()` **:63**; `defp current_fixity_table` **:1705**, default `Process.get(@fixity_key) || BuiltinFixity.table()` **:1706**.
- `lib/cure/elab/program.ex`: `def elaborate(source)` **:18**; `defp check_declarations(ast)` **:110** (`check_no_builtin_rebind` at **:115**, `check_no_precedence_cycle` at **:116**); `defp check_no_precedence_cycle(ast)` **:130** (`base = BuiltinFixity.table(); table = BuiltinFixity.extend(base, ast)`); `defp check_no_builtin_rebind(ast)` **:148** (location rule); `defp fixity_decl_nodes/1` **:168** (`:fixity` only, no `:precedencegroup`); `defp find_module_name/1` **:1301** (used by `user_source_path` too — keep); `defp import_source_path(source)` **:1961**; `defp user_source_path(source)` **:2013** (`Process.get(:cure_source_roots, [])`); `defp stdlib_source_path?(path)` **:1678**.
- `lib/std/operators.cure`: `@group(:core)` **:1**, `mod Std.Operators` **:2**; **no `@prelude` yet**. Declares `infix ... : Group` (e.g. `+`,`|>`,`==`,`✉`,`<-|`,`.`).
- `test/cure/compiler/operator_flip_test.exs`: harness `run/2`,`eval/1`,`eval_in/2`,`assert_error_tag/2` (**:35-46**, matches `{^tag,_,_}` or `{^tag,_}`, in a bare tuple or a parser error LIST). Three tests assert `{:builtin_operator_not_overloadable, atom}` at **:105-113**, **:115-126**, **:128-138** via a **bare** `assert {:error, {...}} = elaborate(src)` (NOT via `assert_error_tag`).

---

## File Structure

**New files**

- `lib/cure/compiler/parser/fixity_scan.ex` — `Cure.Compiler.Parser.FixityScan`. Table-independent extraction: deep collectors over an AST/expr-list (`collect_fixity/1`, `collect_use_targets/1`, `collect_uses/1`, `prelude?/1`, `module_name/1`) plus `harvest_source/3` that tokenizes a file and runs the tolerant harvest. One responsibility: "what does this source declare, structurally."
- `lib/cure/compiler/source_resolver.ex` — `Cure.Compiler.SourceResolver`. `module_path/1`: resolve a module name to a source path (stdlib candidates via `Cure.Stdlib.Paths.source_dir()`; user modules via `:cure_source_roots`, matched by declared module name using the tolerant harvest). One responsibility: "where does this module's source live."
- `lib/cure/compiler/parser/fixity_resolver.ex` — `Cure.Compiler.Parser.FixityResolver`. `assemble/5`: BFS over `use_reach`, union `own(X)` into a base table via conflict-aware merges, detect conflicts. One responsibility: "assemble `fixity(M)`."

**Modified files**

- `lib/cure/compiler/parser/fixity_table.ex` — add conflict-aware `merge_op/4` and `merge_group/3`.
- `lib/cure/compiler/parser.ex` — expose `harvest/4`; refactor Phase 1 to use it; replace the line-207 assembly with `FixityResolver.assemble/5`; add `:prelude_providers` option.
- `lib/cure/compiler/parser/builtin_fixity.ex` — reimplement `table/0`/`compute` as the fixity union over the compiler-bundled `@prelude` stdlib closure with the generalized re-entrancy guard.
- `lib/cure/elab/program.ex` — repoint `check_no_precedence_cycle/1` at `fixity(M)`; delete `check_no_builtin_rebind/1` and its call site; delete now-unused `fixity_decl_nodes/1`.
- `lib/cure/compiler/dep_graph.ex` — harden `scan_file/1` to recover module identity / `use` edges / prelude flag from a tolerant harvest when `parse_source` errors.
- `lib/cure/cli.ex`, `lib/cure/project.ex` — extract the `prelude_provider?` module-name set from the `DepGraph` scan and thread it into `compile_file` → `Parser.parse` as `:prelude_providers`.
- `lib/cure/compiler.ex` — thread `:prelude_providers` from `compile_string`/`compile_file` opts into the internal `parse/4`.
- `lib/std/operators.cure` — add `@prelude`.
- Tests: `test/cure/compiler/fixity_scan_test.exs`, `source_resolver_test.exs`, `fixity_resolver_test.exs`, `fixity_propagation_test.exs`, `dep_graph_resilience_test.exs` (new); `operator_flip_test.exs` (migrate 3 assertions + add group-cycle-cross-module).

---

## Task 1: Conflict-aware `FixityTable.merge_op/4` and `merge_group/3`

**Files:**
- Modify: `lib/cure/compiler/parser/fixity_table.ex` (add after `add_postfix/4`, ~:94)
- Test: `test/cure/compiler/fixity_table_merge_test.exs` (create)

**Interfaces:**
- Produces:
  - `FixityTable.merge_op(t(), String.t(), fixity(), group_name()) :: {:ok, t()} | {:error, {:conflicting_operator_fixity, {String.t(), group_name(), group_name()}}}` — payload is `{lexeme, existing_group, new_group}`.
  - `FixityTable.merge_group(t(), group_name(), keyword()) :: {:ok, t()} | {:error, {:conflicting_precedence_group, {group_name(), map(), map()}}}` — payload is `{name, existing_body, new_body}`.
  - Rule: absent → add; identical → `{:ok, table}` no-op; different → `{:error, ...}`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/fixity_table_merge_test.exs`:

```elixir
defmodule Cure.Compiler.FixityTableMergeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  defp base do
    FixityTable.new()
    |> FixityTable.add_group(:Additive, assoc: :left)
    |> FixityTable.add_group(:Multiplicative, assoc: :left)
  end

  test "merge_op into an empty slot adds the operator" do
    {:ok, t} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)
    assert FixityTable.group_of(t, "<?>") == :Additive
  end

  test "merge_op with the identical group is a no-op" do
    {:ok, t1} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)
    assert {:ok, ^t1} = FixityTable.merge_op(t1, "<?>", :infix, :Additive)
  end

  test "merge_op with a different group in the same slot conflicts" do
    {:ok, t1} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)
    assert {:error, {:conflicting_operator_fixity, {"<?>", :Additive, :Multiplicative}}} =
             FixityTable.merge_op(t1, "<?>", :infix, :Multiplicative)
  end

  test "merge_op does not conflict across different slots (prefix vs infix)" do
    {:ok, t1} = FixityTable.merge_op(base(), "-", :infix, :Additive)
    assert {:ok, _} = FixityTable.merge_op(t1, "-", :prefix, :Multiplicative)
  end

  test "merge_group into an empty name adds it" do
    {:ok, t} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left)
    assert Map.has_key?(t.groups, :G)
  end

  test "merge_group with an identical body is a no-op" do
    {:ok, t1} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left, higher_than: [], lower_than: [])
    assert {:ok, ^t1} = FixityTable.merge_group(t1, :G, assoc: :left, higher_than: [], lower_than: [])
  end

  test "merge_group with a different body conflicts" do
    {:ok, t1} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left)
    assert {:error, {:conflicting_precedence_group, {:G, _existing, _new}}} =
             FixityTable.merge_group(t1, :G, assoc: :right)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_table_merge_test.exs`
Expected: FAIL — `merge_op`/`merge_group` undefined.

- [ ] **Step 3: Implement `merge_op/4` and `merge_group/3`**

In `lib/cure/compiler/parser/fixity_table.ex`, add after `add_postfix/4` (~:94). **Before writing `group_body/1`, open `add_group/3` (~:67) and read the exact map it stores** — `merge_group`'s `new_body` MUST be byte-identical to what `add_group` puts into `groups`, or the identical-body no-op test will wrongly report a conflict. If `add_group` normalizes (e.g. sorts `higher_than`), mirror that normalization in `group_body/1`.

```elixir
@spec merge_op(t(), String.t(), fixity(), group_name()) ::
        {:ok, t()} | {:error, {:conflicting_operator_fixity, {String.t(), group_name(), group_name()}}}
def merge_op(%__MODULE__{ops: ops} = table, lexeme, fixity, group)
    when is_binary(lexeme) and is_atom(group) and fixity in [:infix, :prefix, :postfix] do
  case ops |> Map.get(lexeme, %{}) |> Map.get(fixity) do
    nil -> {:ok, add_op(table, lexeme, fixity, group, [])}
    %{group: ^group} -> {:ok, table}
    %{group: other} -> {:error, {:conflicting_operator_fixity, {lexeme, other, group}}}
  end
end

@spec merge_group(t(), group_name(), keyword()) ::
        {:ok, t()} | {:error, {:conflicting_precedence_group, {group_name(), map(), map()}}}
def merge_group(%__MODULE__{groups: groups} = table, name, opts) when is_atom(name) do
  new_body = group_body(opts)

  case Map.get(groups, name) do
    nil -> {:ok, add_group(table, name, opts)}
    ^new_body -> {:ok, table}
    existing -> {:error, {:conflicting_precedence_group, {name, existing, new_body}}}
  end
end

# Mirror EXACTLY the map `add_group/3` stores in `groups` (read add_group first).
defp group_body(opts) do
  %{
    assoc: Keyword.get(opts, :assoc, :left),
    higher_than: Keyword.get(opts, :higher_than, []),
    lower_than: Keyword.get(opts, :lower_than, [])
  }
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_table_merge_test.exs`
Expected: PASS (7 tests). If the `merge_group` identical-body test fails, `group_body/1` doesn't match `add_group`'s stored shape — align it and re-run.

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/parser/fixity_table.ex test/cure/compiler/fixity_table_merge_test.exs
git commit -m "feat(fixity): conflict-aware merge_op/merge_group on FixityTable"
```

---

## Task 2: Expose the tolerant harvest pass — `Parser.harvest/4`

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (add `harvest/4`; refactor Phase 1 at ~:192-203 to call it)
- Test: `test/cure/compiler/parser_harvest_test.exs` (create)

**Interfaces:**
- Produces: `Cure.Compiler.Parser.harvest(tokens :: [term()], file :: String.t(), base :: FixityTable.t(), edition :: term()) :: [tuple()]` — the top-level expr list from a single tolerant `parse_program` pass seeded with `base`, with per-statement `synchronize_to_statement` recovery (already inside `parse_program`). Never raises; returns whatever declaration nodes survived.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/parser_harvest_test.exs`:

```elixir
defmodule Cure.Compiler.ParserHarvestTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable}

  defp harvest(src, base \\ nil) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.harvest(tokens, "test.cure", base || BuiltinFixity.table(), Cure.Edition.current())
  end

  test "harvest returns fixity declaration nodes even when a later body uses an unknown operator" do
    src = """
    mod M
      use Std.Operators
      infix `<?>` : Additive
      fn go() -> Int = 1 <?> 2
    end
    """

    nodes = harvest(src)
    fixities = for {:fixity, meta, _} <- deep(nodes), do: Keyword.get(meta, :operator)
    assert "<?>" in fixities
  end

  test "harvest surfaces import (use) nodes" do
    src = "mod M\n  use Std.Operators\nend\n"
    sources = for {:import, meta, _} <- deep(harvest(src)), do: Keyword.get(meta, :source)
    assert "Std.Operators" in sources
  end

  # deep-walk helper: flatten the AST into a node list
  defp deep(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &deep/1)
  defp deep({_t, _m, children} = node) when is_list(children), do: [node | deep(children)]
  defp deep(other) when is_tuple(other), do: other |> Tuple.to_list() |> deep()
  defp deep(_), do: []
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/parser_harvest_test.exs`
Expected: FAIL — `Parser.harvest/4` undefined.

- [ ] **Step 3: Add `harvest/4` and refactor Phase 1 to use it**

In `lib/cure/compiler/parser.ex`, add a public `harvest/4` near `parse/2` (after ~:259):

```elixir
@doc """
Run the table-independent harvest pass over `tokens`: a single `parse_program`
seeded with `base`, with per-statement recovery. Returns the surviving
top-level declaration/expression nodes. Never raises — used to extract a
module's own fixity/`use`/`@prelude`/module-name structure without a fully
successful body parse.
"""
@spec harvest([term()], String.t(), FixityTable.t(), term()) :: [tuple()]
def harvest(tokens, file, base, edition \\ nil) do
  edition = edition || Cure.Edition.current()

  harvest_state =
    put_tokens(
      %__MODULE__{file: file, emit_events: false, edition: edition, fixity_table: base},
      tokens
    )

  {exprs, _state} = parse_program(harvest_state)
  exprs
end
```

Then refactor Phase 1 inside `parse/2` (currently ~:192-203) to delegate, preserving behavior exactly:

```elixir
# Phase 1 (harvest) — was an inline harvest_state + parse_program
harvest_exprs = harvest(tokens, file, builtin_fixity, edition)
```

Delete the now-redundant inline `harvest_state = put_tokens(...)` / `{harvest_exprs, _harvest_state} = parse_program(harvest_state)` lines (~:192-203) that this replaces. Leave lines :207-210 (`session_extend_fixity_table`, `harvest_active_macros`, etc.) untouched for now — Task 6 changes :207.

- [ ] **Step 4: Run the harvest test AND the existing parser suite (behavior preserved)**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/parser_harvest_test.exs test/cure/compiler/parser_test.exs`
Expected: PASS. The refactor must not change any existing parser behavior.

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/parser.ex test/cure/compiler/parser_harvest_test.exs
git commit -m "refactor(parser): expose tolerant harvest pass as Parser.harvest/4"
```

---

## Task 3: `FixityScan` — table-independent structural extraction

**Files:**
- Create: `lib/cure/compiler/parser/fixity_scan.ex`
- Test: `test/cure/compiler/fixity_scan_test.exs`

**Interfaces:**
- Consumes: `Parser.harvest/4` (Task 2), `Lexer.tokenize/2`.
- Produces (all deep-walk an AST node / list / expr-list; safe on any tuple tree):
  - `FixityScan.collect_fixity(ast) :: [tuple()]` — every `{:fixity, _, _}` and `{:precedencegroup, _, _}` node, source order.
  - `FixityScan.collect_use_targets(ast) :: [String.t()]` — every `{:import, meta, _}`'s `meta[:source]` (name only).
  - `FixityScan.collect_uses(ast) :: [%{target: String.t(), line: pos_integer()}]` — rich form for DepGraph.
  - `FixityScan.prelude?(ast) :: boolean()` — true iff a `@prelude` decorator is present (same recognition as `DepGraph.prelude_decorated?/1`).
  - `FixityScan.module_name(ast) :: String.t() | nil` — the container module name.
  - `FixityScan.harvest_source(source :: String.t(), file :: String.t(), base :: FixityTable.t()) :: %{fixity: [tuple()], uses: [%{target: String.t(), line: pos_integer()}], prelude?: boolean(), module: String.t() | nil}` — tokenize + `Parser.harvest` + the collectors. On lex failure returns the empty map `%{fixity: [], uses: [], prelude?: false, module: nil}`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/fixity_scan_test.exs`:

```elixir
defmodule Cure.Compiler.Parser.FixityScanTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.{FixityScan, BuiltinFixity, FixityTable}

  @src """
  @prelude
  mod M
    use Std.Operators
    use Other.Mod
    precedencegroup G
      associativity: left
    infix `<?>` : G
    fn go() -> Int = 1 <?> 2
  end
  """

  defp scan(src), do: FixityScan.harvest_source(src, "m.cure", BuiltinFixity.table())

  test "extracts fixity + precedencegroup nodes despite a body using <?>" do
    s = scan(@src)
    ops = for {:fixity, meta, _} <- s.fixity, do: Keyword.get(meta, :operator)
    groups = for {:precedencegroup, meta, _} <- s.fixity, do: Keyword.get(meta, :name)
    assert "<?>" in ops
    assert :G in groups
  end

  test "extracts use targets" do
    targets = Enum.map(scan(@src).uses, & &1.target)
    assert "Std.Operators" in targets
    assert "Other.Mod" in targets
  end

  test "detects @prelude and module name" do
    s = scan(@src)
    assert s.prelude? == true
    assert s.module == "M"
  end

  test "a lexer error yields the empty scan rather than raising" do
    s = FixityScan.harvest_source(~s|mod M\n  fn f() = "unterminated|, "m.cure", FixityTable.new())
    assert s == %{fixity: [], uses: [], prelude?: false, module: nil}
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_scan_test.exs`
Expected: FAIL — module `FixityScan` undefined.

- [ ] **Step 3: Implement `FixityScan`**

Create `lib/cure/compiler/parser/fixity_scan.ex`. **Copy the `@prelude` recognition exactly from `DepGraph.prelude_decorated?/1` (dep_graph.ex:242-253)** and the `:import` source read exactly from `DepGraph.collect_uses`'s `use_collector` (dep_graph.ex:286-296), so detection can't drift between the two call sites.

```elixir
defmodule Cure.Compiler.Parser.FixityScan do
  @moduledoc """
  Table-independent structural extraction from Cure source. Given a module's
  source (or an already-harvested node list), reports its own fixity /
  precedence-group declarations, `use` targets, `@prelude` flag, and module
  name — WITHOUT requiring a fully successful parse of its function bodies.
  Declarations are inert (their parse never consults the fixity table), so
  `synchronize_to_statement` recovery inside the harvest pass guarantees they
  survive even when surrounding expressions misparse.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.FixityTable

  @empty %{fixity: [], uses: [], prelude?: false, module: nil}

  @spec harvest_source(String.t(), String.t(), FixityTable.t()) :: %{
          fixity: [tuple()],
          uses: [%{target: String.t(), line: pos_integer()}],
          prelude?: boolean(),
          module: String.t() | nil
        }
  def harvest_source(source, file, base) do
    case Lexer.tokenize(source, emit_events: false) do
      {:ok, tokens} ->
        exprs = Parser.harvest(tokens, file, base, Cure.Edition.current())

        %{
          fixity: collect_fixity(exprs),
          uses: collect_uses(exprs),
          prelude?: prelude?(exprs),
          module: module_name(exprs)
        }

      _ ->
        @empty
    end
  end

  @spec collect_fixity(term()) :: [tuple()]
  def collect_fixity(ast), do: deep_collect(ast, fn
    {:fixity, _, _} = n -> [n]
    {:precedencegroup, _, _} = n -> [n]
    _ -> []
  end)

  @spec collect_uses(term()) :: [%{target: String.t(), line: pos_integer()}]
  def collect_uses(ast), do: deep_collect(ast, fn
    {:import, meta, _} when is_list(meta) ->
      case Keyword.get(meta, :source) do
        s when is_binary(s) -> [%{target: s, line: Keyword.get(meta, :line, 1)}]
        _ -> []
      end
    _ -> []
  end)

  @spec collect_use_targets(term()) :: [String.t()]
  def collect_use_targets(ast), do: ast |> collect_uses() |> Enum.map(& &1.target)

  @spec prelude?(term()) :: boolean()
  def prelude?(ast) do
    deep_reduce(ast, false, fn
      {:property, meta, _}, false when is_list(meta) -> Keyword.get(meta, :name) == "prelude"
      {_t, meta, _}, false when is_list(meta) -> match?({:prelude, _}, Keyword.get(meta, :decorator))
      _, acc -> acc
    end)
  end

  # Mirrors `DepGraph.find_module/1`'s filter exactly: `:container` is also
  # emitted for non-module constructs (`:struct`, `:primitive`, `:opaque`,
  # `:enum`, `:protocol`, `:trait` — parser.ex :5746/:5874/:5914/:5997/:6499/
  # :6547), so matching on the tag alone risks returning a nested type's name
  # instead of the module's, especially on a `synchronize_to_statement`-
  # recovered harvest of malformed source where node order/nesting can't be
  # assumed well-formed.
  @module_container_types [:module, :proof]

  @spec module_name(term()) :: String.t() | nil
  def module_name(ast) do
    deep_reduce(ast, nil, fn
      {:container, meta, _}, nil when is_list(meta) ->
        if Keyword.get(meta, :container_type) in @module_container_types,
          do: Keyword.get(meta, :name),
          else: nil

      _, acc -> acc
    end)
  end

  # -- deep walkers (mirror BuiltinFixity.collect_fixity_nodes shape) --------

  defp deep_collect(node, f) when is_tuple(node) do
    f.(node) ++ (node |> Tuple.to_list() |> deep_collect(f))
  end

  defp deep_collect(list, f) when is_list(list), do: Enum.flat_map(list, &deep_collect(&1, f))
  defp deep_collect(_other, _f), do: []

  defp deep_reduce(node, acc, f) when is_tuple(node) do
    acc = f.(node, acc)
    node |> Tuple.to_list() |> deep_reduce(acc, f)
  end

  defp deep_reduce(list, acc, f) when is_list(list),
    do: Enum.reduce(list, acc, fn el, a -> deep_reduce(el, a, f) end)

  defp deep_reduce(_other, acc, _f), do: acc
end
```

**Note on `module_name`:** `Program.find_module_name/1` matches `{:container, meta, _}` (program.ex:1301). Confirm the container tag your harvest emits is `:container` (grep `parse_program`/module production). If the top-level module node uses a different tag, match that tag instead — the `fixity_scan_test.exs` `s.module == "M"` assertion is the guard. Also confirm `@module_container_types` (`[:module, :proof]`) still matches `DepGraph`'s own list (dep_graph.ex:46) — keep the two in sync so a module recognized by one is recognized by the other.

- [ ] **Step 4: Run test to verify it passes**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_scan_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/parser/fixity_scan.ex test/cure/compiler/fixity_scan_test.exs
git commit -m "feat(fixity): table-independent FixityScan extraction"
```

---

## Task 4: `SourceResolver.module_path/1`

**Files:**
- Create: `lib/cure/compiler/source_resolver.ex`
- Test: `test/cure/compiler/source_resolver_test.exs`

**Interfaces:**
- Consumes: `Cure.Stdlib.Paths.source_dir/0`, `:cure_source_roots` (process dict), `FixityScan.harvest_source/3` (for user-module name matching).
- Produces: `SourceResolver.module_path(name :: String.t()) :: {:ok, Path.t()} | :not_found`. For `"Std.X.Y"` names, tries `Paths.source_dir()` candidates (`Enum.map_join(segs, "_", &Macro.underscore/1)` and `String.downcase(Enum.join(segs, "_"))`, mirroring `Program.import_source_path/1`); for others, scans `:cure_source_roots` and returns the file whose declared module name equals `name` (via `FixityScan`). Returns `:not_found` on no match OR ambiguous (>1) match.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/source_resolver_test.exs`:

```elixir
defmodule Cure.Compiler.SourceResolverTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.SourceResolver

  test "resolves a stdlib module name to its .cure source" do
    assert {:ok, path} = SourceResolver.module_path("Std.Operators")
    assert String.ends_with?(path, "operators.cure")
    assert File.exists?(path)
  end

  test "returns :not_found for an unknown module" do
    assert :not_found = SourceResolver.module_path("Totally.Bogus.Module")
  end

  @tag :tmp_dir
  test "resolves a user module by declared name from a source root", %{tmp_dir: dir} do
    file = Path.join(dir, "weird_name.cure")
    File.write!(file, "mod My.Widget\n  fn go() -> Int = 1\nend\n")

    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])

    try do
      assert {:ok, ^file} = SourceResolver.module_path("My.Widget")
    after
      Process.put(:cure_source_roots, prev)
    end
  end
end
```

**Note on the fix above:** the original draft of this test destructured `%{tmp_dir: _} = ctx` with no `@tag :tmp_dir` and no `setup` populating `:tmp_dir` — that pattern-match crashes with `FunctionClauseError` on every run (ExUnit only injects a real `:tmp_dir` into the test context when the test or module carries the `:tmp_dir` tag), regardless of whether `SourceResolver` exists, contradicting this task's own Step 2 (“FAIL — module `SourceResolver` undefined”) and Step 4 (“PASS”) expectations. `@tag :tmp_dir` is this codebase's existing convention for exactly this need (see `test/cure/compiler/dep_graph_test.exs`'s `@moduletag :tmp_dir`) — ExUnit creates and removes the directory automatically, so the manual `mkdir_p!`/`rm_rf!` calls are dropped too.

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/source_resolver_test.exs`
Expected: FAIL — module `SourceResolver` undefined.

- [ ] **Step 3: Implement `SourceResolver`**

Create `lib/cure/compiler/source_resolver.ex`. The stdlib candidate logic mirrors `Program.import_source_path/1` (program.ex:1961) — keep the two candidate spellings identical so a name resolves to the same file both paths would pick.

```elixir
defmodule Cure.Compiler.SourceResolver do
  @moduledoc """
  Resolve a Cure module NAME to a source PATH, on demand, by name only —
  the same resolution `Cure.Elab.Program.import_source_path/1` performs for
  `use` imports, reduced to the path (no elaboration-layer return tags).
  Used by the fixity resolver to walk the `use`-closure at parse time
  without a precomputed dependency graph. User-module matching uses the
  tolerant harvest (never a full parse), so it cannot recurse into fixity
  resolution.
  """

  alias Cure.Stdlib.Paths
  alias Cure.Compiler.Parser.FixityScan
  alias Cure.Compiler.Parser.FixityTable

  @spec module_path(String.t()) :: {:ok, Path.t()} | :not_found
  def module_path(name) when is_binary(name) do
    case stdlib_path(name) do
      {:ok, _} = ok -> ok
      :not_found -> user_path(name)
    end
  end

  defp stdlib_path("Std." <> _ = name) do
    case Paths.source_dir() do
      nil ->
        :not_found

      dir ->
        segments = name |> String.split(".") |> tl()

        [
          Enum.map_join(segments, "_", &Macro.underscore/1),
          String.downcase(Enum.join(segments, "_"))
        ]
        |> Enum.uniq()
        |> Enum.map(&Path.join(dir, &1 <> ".cure"))
        |> Enum.find(&File.exists?/1)
        |> case do
          nil -> :not_found
          path -> {:ok, path}
        end
    end
  end

  defp stdlib_path(_), do: :not_found

  defp user_path(name) do
    Process.get(:cure_source_roots, [])
    |> Enum.flat_map(fn root -> Path.wildcard(Path.join(root, "**/*.cure")) end)
    |> Enum.uniq()
    |> Enum.filter(fn path -> declared_module(path) == name end)
    |> case do
      [path] -> {:ok, path}
      _ -> :not_found
    end
  end

  defp declared_module(path) do
    case File.read(path) do
      {:ok, source} -> FixityScan.harvest_source(source, path, FixityTable.new()).module
      _ -> nil
    end
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/source_resolver_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/source_resolver.ex test/cure/compiler/source_resolver_test.exs
git commit -m "feat(fixity): name->path SourceResolver for use-closure walk"
```

---

## Task 5: `FixityResolver.assemble/5` — use-closure union + conflict detection

**Files:**
- Create: `lib/cure/compiler/parser/fixity_resolver.ex`
- Test: `test/cure/compiler/fixity_resolver_test.exs`

**Interfaces:**
- Consumes: `SourceResolver.module_path/1` (Task 4), `FixityScan.harvest_source/3` (Task 3), `FixityTable.merge_op/4` + `merge_group/3` (Task 1).
- Produces: `FixityResolver.assemble(base :: FixityTable.t(), own_fixity :: [tuple()], own_uses :: [String.t()], prelude_providers :: [String.t()], opts :: keyword()) :: {:ok, FixityTable.t()} | {:error, {:conflicting_operator_fixity, tuple()}} | {:error, {:conflicting_precedence_group, tuple()}}`.
  - `base` is the prelude/builtin seed table (already contains the compiler-bundled prelude closure). `own_fixity`/`own_uses` are `M`'s own declarations/imports. `prelude_providers` is the driver-threaded user-`@prelude` name set (stdlib prelude is already in `base`). All reached modules AND `M`'s own nodes are folded onto `base`; **precedence groups are merged before operators** (ops reference groups); conflicts short-circuit.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/fixity_resolver_test.exs`:

```elixir
defmodule Cure.Compiler.Parser.FixityResolverTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.Parser.{FixityResolver, FixityTable}

  setup do
    dir = Path.join(System.tmp_dir!(), "fr_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])
    on_exit(fn -> Process.put(:cure_source_roots, prev); File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  defp write(dir, file, body), do: File.write!(Path.join(dir, file), body)

  # own_fixity/own_uses of M are supplied directly (as the parser will, from harvest).
  defp assemble(uses), do: FixityResolver.assemble(FixityTable.new(), [], uses, [])

  test "an operator declared in a used module is present in the assembled table", %{dir: dir} do
    write(dir, "a.cure", """
    mod A
      precedencegroup G
        associativity: left
      infix `<?>` : G
    end
    """)

    {:ok, table} = assemble(["A"])
    assert FixityTable.group_of(table, "<?>") == :G
  end

  test "propagation is transitive: C use B, B use A", %{dir: dir} do
    write(dir, "a.cure", "mod A\n  precedencegroup G\n    associativity: left\n  infix `<?>` : G\nend\n")
    write(dir, "b.cure", "mod B\n  use A\nend\n")

    # C's own_uses = ["B"]
    {:ok, table} = assemble(["B"])
    assert FixityTable.group_of(table, "<?>") == :G
  end

  test "two used modules declaring <?> in different groups conflict", %{dir: dir} do
    write(dir, "a.cure", "mod A\n  precedencegroup Ga\n    associativity: left\n  infix `<?>` : Ga\nend\n")
    write(dir, "b.cure", "mod B\n  precedencegroup Gb\n    associativity: left\n  infix `<?>` : Gb\nend\n")

    assert {:error, {:conflicting_operator_fixity, {"<?>", _, _}}} = assemble(["A", "B"])
  end

  test "two used modules declaring the same group name with different bodies conflict", %{dir: dir} do
    write(dir, "a.cure", "mod A\n  precedencegroup G\n    associativity: left\nend\n")
    write(dir, "b.cure", "mod B\n  precedencegroup G\n    associativity: right\nend\n")

    assert {:error, {:conflicting_precedence_group, {:G, _, _}}} = assemble(["A", "B"])
  end

  test "an unresolved use contributes nothing (no crash)", %{dir: _dir} do
    assert {:ok, _table} = assemble(["No.Such.Module"])
  end

  test "identical redeclaration across modules is accepted", %{dir: dir} do
    write(dir, "a.cure", "mod A\n  precedencegroup G\n    associativity: left\n  infix `<?>` : G\nend\n")
    write(dir, "b.cure", "mod B\n  use A\n  precedencegroup G\n    associativity: left\n  infix `<?>` : G\nend\n")

    assert {:ok, table} = assemble(["B"])
    assert FixityTable.group_of(table, "<?>") == :G
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_resolver_test.exs`
Expected: FAIL — module `FixityResolver` undefined.

- [ ] **Step 3: Implement `FixityResolver`**

Create `lib/cure/compiler/parser/fixity_resolver.ex`. **The `{:fixity,...}` and `{:precedencegroup,...}` meta reads in `merge_node/2` MUST mirror `BuiltinFixity.build/2` + `add_fixity_op/2` (builtin_fixity.ex:100-133) exactly** — same keyword keys (`:name`,`:assoc`,`:higher_than`,`:lower_than` for groups; `:operator`,`:group`,`:fixity` for ops) and the same `is_atom(group) and not is_nil(group)` guard — so a declaration means the same thing whether it flows through `BuiltinFixity` (base) or the resolver (propagated).

```elixir
defmodule Cure.Compiler.Parser.FixityResolver do
  @moduledoc """
  Assemble `fixity(M) = base ∪ ⋃ own(X) over use_reach(M) ∪ own(M) ∪ user
  prelude providers`, resolving the `use`-closure on demand by name (no
  precomputed DepGraph). Groups are merged before operators; a same-lexeme/
  different-group or same-name/different-body clash is a hard conflict.
  Reachability uses set-union, so `use` cycles need no special handling.
  Target modules are scanned with the tolerant harvest only — never a full
  `Parser.parse` — so this never recurses into itself.
  """

  alias Cure.Compiler.Parser.{FixityTable, FixityScan}
  alias Cure.Compiler.SourceResolver

  @spec assemble(FixityTable.t(), [tuple()], [String.t()], [String.t()], keyword()) ::
          {:ok, FixityTable.t()} | {:error, term()}
  def assemble(base, own_fixity, own_uses, prelude_providers, _opts \\ []) do
    seeds = Enum.uniq(own_uses ++ prelude_providers)

    with {:ok, reached_fixity} <- gather(seeds, MapSet.new(), [], base) do
      # own(M) is folded LAST so M's own declarations are still subject to the
      # same conflict rule against everything it imports.
      fold(base, reached_fixity ++ own_fixity)
    end
  end

  # BFS over the use-closure, accumulating each reached module's own fixity
  # nodes. `base` seeds each target's harvest so built-in operators in the
  # target's bodies don't misparse (Component 1).
  defp gather([], _seen, acc, _base), do: {:ok, acc}

  defp gather([name | rest], seen, acc, base) do
    if MapSet.member?(seen, name) do
      gather(rest, seen, acc, base)
    else
      seen = MapSet.put(seen, name)

      case SourceResolver.module_path(name) do
        {:ok, path} ->
          case File.read(path) do
            {:ok, source} ->
              scan = FixityScan.harvest_source(source, path, base)
              next = rest ++ Enum.map(scan.uses, & &1.target)
              gather(next, seen, acc ++ scan.fixity, base)

            {:error, _} ->
              gather(rest, seen, acc, base)
          end

        :not_found ->
          gather(rest, seen, acc, base)
      end
    end
  end

  # Groups first (ops reference them), then operators. Short-circuit on conflict.
  defp fold(base, nodes) do
    groups = Enum.filter(nodes, &match?({:precedencegroup, _, _}, &1))
    ops = Enum.filter(nodes, &match?({:fixity, _, _}, &1))

    with {:ok, t1} <- reduce_merge(base, groups),
         {:ok, t2} <- reduce_merge(t1, ops) do
      {:ok, t2}
    end
  end

  defp reduce_merge(table, nodes) do
    Enum.reduce_while(nodes, {:ok, table}, fn node, {:ok, t} ->
      case merge_node(t, node) do
        {:ok, t2} -> {:cont, {:ok, t2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp merge_node(table, {:precedencegroup, meta, _}) when is_list(meta) do
    FixityTable.merge_group(table, Keyword.fetch!(meta, :name),
      assoc: Keyword.get(meta, :assoc, :left),
      higher_than: Keyword.get(meta, :higher_than, []),
      lower_than: Keyword.get(meta, :lower_than, [])
    )
  end

  defp merge_node(table, {:fixity, meta, _}) when is_list(meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)
    fixity = Keyword.get(meta, :fixity)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) and
         fixity in [:infix, :prefix, :postfix] do
      FixityTable.merge_op(table, lexeme, fixity, group)
    else
      {:ok, table}
    end
  end

  defp merge_node(table, _), do: {:ok, table}
end
```

**Confirm the `:precedencegroup` meta keys** against `parse_precedencegroup` (parser.ex:5632) and `BuiltinFixity.build/2` (builtin_fixity.ex:100-110): if the group's associativity/relations live under different meta keys than `:assoc`/`:higher_than`/`:lower_than`, use those keys (and match them in `FixityTable.group_body/1` from Task 1). The `fixity_resolver_test.exs` group tests are the guard.

- [ ] **Step 4: Run test to verify it passes**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_resolver_test.exs`
Expected: PASS (6 tests).

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/parser/fixity_resolver.ex test/cure/compiler/fixity_resolver_test.exs
git commit -m "feat(fixity): use-closure resolver with conflict detection"
```

---

## Task 6: Wire `FixityResolver` into `Parser.parse/2` + `:prelude_providers` option

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (option read ~:186; assembly ~:207; error handling)
- Test: `test/cure/compiler/fixity_propagation_test.exs` (create)

**Interfaces:**
- Consumes: `FixityResolver.assemble/5`, `FixityScan.collect_fixity/1`, `FixityScan.collect_use_targets/1`.
- Produces: `Parser.parse/2` now (a) reads a new `:prelude_providers` option (`[String.t()]`, default `[]`); (b) assembles `fixity(M)` = `FixityResolver.assemble(builtin_fixity, own_fixity, own_uses, prelude_providers)`; (c) on a conflict, returns `{:error, [conflict]}` without attempting the authoritative pass. A single-file parse with no source universe still binds core operators (via `builtin_fixity` base + `own(M)`).

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/fixity_propagation_test.exs`:

```elixir
defmodule Cure.Compiler.FixityPropagationTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.{Lexer, Parser}

  setup do
    dir = Path.join(System.tmp_dir!(), "fp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])
    on_exit(fn -> Process.put(:cure_source_roots, prev); File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  defp parse(src, opts \\ []) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(tokens, [emit_events: false] ++ opts)
  end

  test "a module that uses A can parse A's operator; assembly succeeds", %{dir: dir} do
    File.write!(Path.join(dir, "a.cure"), """
    mod A
      precedencegroup G
        associativity: left
      infix `<?>` : G
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    src = "mod B\n  use A\n  fn go() -> Int = 1 <?> 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end

  test "conflicting fixity across two used modules is a parse error", %{dir: dir} do
    File.write!(Path.join(dir, "a.cure"), "mod A\n  precedencegroup Ga\n    associativity: left\n  infix `<?>` : Ga\nend\n")
    File.write!(Path.join(dir, "b.cure"), "mod B\n  precedencegroup Gb\n    associativity: left\n  infix `<?>` : Gb\nend\n")

    src = "mod C\n  use A\n  use B\nend\n"
    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:conflicting_operator_fixity, {"<?>", _, _}}, &1))
  end

  test "single-file parse with no source universe still binds core operators" do
    # No :cure_source_roots entries resolve; the built-in prelude still applies.
    Process.put(:cure_source_roots, [])
    src = "mod M\n  fn f(a: Int, b: Int) -> Int = a + b * 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_propagation_test.exs`
Expected: FAIL — the "use A" module can't parse `<?>` (assembly not wired), and the conflict isn't raised.

- [ ] **Step 3: Wire the resolver into `parse/2`**

In `lib/cure/compiler/parser.ex`:

1. Add the alias `FixityScan, FixityResolver` to line :40's `alias Cure.Compiler.Parser.{...}` group (→ `alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable, FixityScan, FixityResolver, Precedence}`).

2. Read the new option near :186:

```elixir
prelude_providers = Keyword.get(opts, :prelude_providers, [])
```

3. Replace the line-207 assembly. Where it currently reads:

```elixir
module_fixity = session_extend_fixity_table(builtin_fixity, harvest_exprs)
```

replace with:

```elixir
own_fixity = FixityScan.collect_fixity(harvest_exprs)
own_uses = FixityScan.collect_use_targets(harvest_exprs)

module_fixity =
  case FixityResolver.assemble(builtin_fixity, own_fixity, own_uses, prelude_providers) do
    {:ok, table} -> table
    {:error, conflict} -> {:__fixity_conflict__, conflict}
  end
```

4. Guard the authoritative pass. Immediately AFTER the `module_fixity = ...` block and BEFORE Phase 2 builds its state (~:212), short-circuit on conflict:

```elixir
case module_fixity do
  {:__fixity_conflict__, conflict} ->
    {:error, [conflict]}

  %FixityTable{} = module_fixity ->
    # ... existing Phase 2 body (build state with fixity_table: module_fixity,
    #     parse_program, wrap block, return {:ok, ast} | {:error, ...}) ...
end
```

Wrap the existing Phase 2 code (currently ~:212-258) inside the `%FixityTable{} = module_fixity ->` branch unchanged. `session_extend_fixity_table/2` (:2258) becomes unused — remove it to avoid a compiler warning.

**Do NOT** thread `module_fixity` back to `harvest_active_macros`/`harvest_computed_macros`/`harvest_literal_macros` (:208-210) — those already read `harvest_exprs` and are unaffected.

- [ ] **Step 4: Run the propagation test AND the parser suite**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_propagation_test.exs test/cure/compiler/parser_test.exs test/cure/compiler/operator_flip_test.exs`
Expected: `fixity_propagation_test` PASS. `parser_test` PASS. `operator_flip_test` — the 3 built-in-rebind tests may now FAIL differently (conflict is raised at parse, not elaboration); that is expected and fixed in Task 8. The two `precedence_cycle` tests and the propagation tests must still pass. **If any NON-rebind operator_flip test regresses, stop and fix before continuing.**

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/parser.ex test/cure/compiler/fixity_propagation_test.exs
git commit -m "feat(fixity): assemble use-propagated table in Parser.parse"
```

---

## Task 7: `@prelude` on operators.cure + reimplement `BuiltinFixity.table/0`

**Files:**
- Modify: `lib/std/operators.cure` (add `@prelude` between :1 and :2)
- Modify: `lib/cure/compiler/parser/builtin_fixity.ex` (`compute/0`)
- Test: `test/cure/compiler/builtin_fixity_prelude_test.exs` (create)

**Interfaces:**
- Produces: `BuiltinFixity.table/0` now computes the union of `own(P)`-closures over the **compiler-bundled** `@prelude` stdlib modules (located via `@stdlib_source_dir`), using `FixityScan` + `FixityResolver`-style folding under the generalized re-entrancy guard. Content is unchanged today (only `operators.cure` declares fixity, and it is now `@prelude`), so `declares?(table(), "+")` etc. stay true. Persistent-term memo is retained; caching is guarded to compiler-bundled (stdlib) paths only.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/builtin_fixity_prelude_test.exs`:

```elixir
defmodule Cure.Compiler.BuiltinFixityPreludeTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable}

  test "operators.cure carries @prelude" do
    {:ok, src} = File.read("lib/std/operators.cure")
    assert src =~ ~r/@prelude\s*\n\s*mod Std\.Operators/
  end

  test "the built-in table still declares the core operators" do
    t = BuiltinFixity.table()
    for op <- ["+", "*", "|>", "==", "✉", "<-|", "."] do
      assert FixityTable.declares?(t, op), "expected built-in table to declare #{op}"
    end
  end

  test "the built-in table is memoized (same term on repeat)" do
    assert BuiltinFixity.table() == BuiltinFixity.table()
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/builtin_fixity_prelude_test.exs`
Expected: FAIL on the `@prelude` regex (not added yet). The other two may pass under the old `compute`.

- [ ] **Step 3a: Add `@prelude` to operators.cure and fix its now-stale header comment**

Edit `lib/std/operators.cure` so lines 1-2 become (matching the `bool.cure` stacking of `@group` then `@prelude` then `mod`):

```
@group(:core)
@prelude
mod Std.Operators
```

The file's header comment (current lines 4-9) describes the OLD location-based
rule this change retires: *"the protection is by LOCATION — anything declared
in this stdlib module is 'built in' and off-limits to user fixity
declarations (see `Program.check_no_builtin_rebind`)."* Once Task 8 deletes
`check_no_builtin_rebind`, this sentence names a function that no longer
exists and describes semantics (`use`-independent, unconditional protection)
this design replaces with `@prelude`-driven conflict detection. Update it to:

```
# The fixity-declaration authority for Cure's core operators — the operators
# every module gets, unconditionally, via `@prelude`. A user module may
# declare NEW operators of its own; redeclaring one of THESE with a
# different group/body is a conflict (`Cure.Compiler.Parser.FixityResolver`,
# `:conflicting_operator_fixity` / `:conflicting_precedence_group`), not a
# location-based rejection — because `@prelude` places this module's
# declarations in every table via the same union every `use` triggers, a
# redeclaration always collides. An identical redeclaration is a no-op.
```

- [ ] **Step 3b: Reimplement `compute/0`**

In `lib/cure/compiler/parser/builtin_fixity.ex`, replace `compute/0` (:55) so it unions fixity over the compiler-bundled `@prelude` stdlib closure. Keep the `@fixity_table_key` memo in `table/0` (:31) unchanged. **Keep the `Process.put(:cure_building_fixity_table, true)` re-entrancy guard, but note its actual role changes here.** Today it guards a real recursion: `compute/0` calls full `Parser.parse/2`, whose line-190 `builtin_fixity = session_builtin_fixity_table()` would otherwise call `BuiltinFixity.table()` again mid-computation. The new `compute/0` below calls `Parser.harvest/4` (Task 2) directly, never `Parser.parse/2` — and `harvest/4` takes its seed table as an explicit `base` argument, never consulting `session_builtin_fixity_table/0` itself (confirm: `grep -n "session_builtin_fixity_table" lib/cure/compiler/parser.ex` shows its only callers are `Parser.parse/2`'s line ~190 and the Pratt loop's nil-fallback `fixity_table/1` accessor — neither is reached by a bare `harvest/4` call with a non-nil `base`). So this specific recursion no longer exists on the `compute/0` → `bundled_prelude_sources/0` → `Parser.harvest/4` path. Keep the guard anyway, as a cheap defensive belt against a *future* change that routes prelude-source scanning back through full `Parser.parse/2` (which would reintroduce the recursion) — but do not describe it as guarding something `harvest/4` currently does, since it doesn't.

```elixir
defp compute do
  prev = Process.put(:cure_building_fixity_table, true)

  try do
    providers = bundled_prelude_providers()

    Enum.reduce(providers, FixityTable.new(), fn {path, scan}, acc ->
      # sole-source per provider: fold groups then ops. Reuse the same
      # meta reads as FixityResolver.merge_node/2 via add_group/add_fixity_op
      # (last-write-wins is fine here — the bundled prelude is authoritative).
      acc
      |> merge_group_nodes(scan.fixity)
      |> merge_op_nodes(scan.fixity)
      |> then(fn t -> if scan == :sentinel, do: t, else: t end)
      |> then(fn t -> {t, path} |> elem(0) end)
    end)
  after
    if prev == nil,
      do: Process.delete(:cure_building_fixity_table),
      else: Process.put(:cure_building_fixity_table, prev)
  end
end
```

**Simplify the reduce** — the `then/2` noise above is a placeholder to force you to read `build/2`. Actually implement `compute/0` cleanly by REUSING the existing `build/2` (builtin_fixity.ex:100), which already folds groups-then-ops via `add_group`/`add_fixity_op`. The only change from today is *which sources* are folded:

```elixir
defp compute do
  prev = Process.put(:cure_building_fixity_table, true)

  try do
    Enum.reduce(bundled_prelude_sources(), FixityTable.new(), fn source_ast, acc ->
      build(source_ast, acc)
    end)
  after
    if prev == nil,
      do: Process.delete(:cure_building_fixity_table),
      else: Process.put(:cure_building_fixity_table, prev)
  end
end

# Compiler-bundled @prelude stdlib modules, as harvested ASTs (node lists).
# Located via the fixed @stdlib_source_dir wildcard — independent of the
# project source universe, exactly like the old single-file operators path.
defp bundled_prelude_sources do
  @stdlib_source_dir
  |> Path.join("*.cure")
  |> Path.wildcard()
  |> Enum.sort()
  |> Enum.flat_map(fn path ->
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, emit_events: false) do
      exprs = Cure.Compiler.Parser.harvest(tokens, path, FixityTable.new(), Cure.Edition.current())
      if Cure.Compiler.Parser.FixityScan.prelude?(exprs), do: [exprs], else: []
    else
      _ -> []
    end
  end)
end
```

Notes:
- **Delete the `then/2` placeholder version** — only the clean `compute/0` + `bundled_prelude_sources/0` above ships. (The placeholder is intentionally non-compiling so it can't be left in by accident.)
- `build/2` (:100) is reused unchanged; it already reads group/op meta the same way `FixityResolver.merge_node/2` does, keeping base and propagated interpretation aligned.
- Alias `FixityScan` at the top of `builtin_fixity.ex` (add to the existing `alias Cure.Compiler.Parser.FixityTable` line → `alias Cure.Compiler.Parser.{FixityTable, FixityScan}`), or fully-qualify as written.
- `operators_source_path/0` (:83) and `collect_fixity_nodes/1` may become unused after this change — remove them only if the compiler flags them unused; `build/2` still uses `collect_fixity_nodes/1`, so keep that one.
- **Caching stays in `table/0` unchanged.** Because `bundled_prelude_sources/0` only ever reads stdlib paths under `@stdlib_source_dir`, the closure never includes user source, so the existing unconditional persistent-term memo remains provenance-safe. (User `@prelude` providers reach a module via the resolver's `:prelude_providers` option in Tasks 6/10, NOT via `table/0`.) Add a one-line comment at the `@fixity_table_key` memo in `table/0` recording this invariant.

- [ ] **Step 4: Run test + the fixity/parser suites**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/builtin_fixity_prelude_test.exs test/cure/compiler/fixity_table_merge_test.exs test/cure/compiler/fixity_scan_test.exs test/cure/compiler/parser_test.exs`
Expected: PASS. If `declares?(table(), "+")` fails, `bundled_prelude_sources/0` isn't picking up `operators.cure` — confirm `FixityScan.prelude?` sees its `@prelude` and that the `*.cure` wildcard resolves under `@stdlib_source_dir`.

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/std/operators.cure lib/cure/compiler/parser/builtin_fixity.ex test/cure/compiler/builtin_fixity_prelude_test.exs
# operators.cure is a source of a generated bundle — see priv/std note; author here in lib/std.
git commit -m "feat(fixity): @prelude operators.cure; table/0 = bundled prelude closure"
```

---

## Task 8: Elaboration migration — repoint cycle check, delete rebind check, migrate tests

**Files:**
- Modify: `lib/cure/elab/program.ex` (`check_declarations/1` :110-118; `check_no_precedence_cycle/1` :130; delete `check_no_builtin_rebind/1` :148 + call at :115; delete `fixity_decl_nodes/1` :168 if unused)
- Modify: `lib/cure/compiler/parser.ex` (fix the stale `check_no_builtin_rebind` reference in `parse_fixity/1`'s comment, ~:5595-5598)
- Modify: `test/cure/compiler/operator_flip_test.exs` (migrate 3 assertions; add cross-module cycle test)

**Interfaces:**
- Consumes: `FixityResolver.assemble/5`, `FixityScan.collect_fixity/1`, `FixityScan.collect_use_targets/1`, `FixityTable.cyclic_groups/1`.
- Produces: precedence-cycle detection now operates on `fixity(M)` (base + own + use-closure), so a cycle closed through a `use`d module's group is caught. The built-in-rebind location rule is gone; conflicts are raised at parse time (Task 6).

- [ ] **Step 1: Write/adjust the failing tests**

In `test/cure/compiler/operator_flip_test.exs`:

(a) Replace the body of "rebinding a builtin syntactic operator is rejected" (:105-113):

```elixir
test "rebinding a builtin syntactic operator is rejected" do
  src = """
  mod M
    use Std.Operators
    infix `|>` : Additive
  end
  """

  assert_error_tag(src, :conflicting_operator_fixity)
end
```

(b) Replace "redeclaring the fixity of any stdlib operator is rejected by location" (:115-126) — update the comment and assertion:

```elixir
test "redeclaring the fixity of a stdlib operator is rejected as a conflict" do
  # `+`'s fixity is fixed by Std.Operators (now @prelude). Redeclaring its group
  # collides with the prelude entry present in every assembled table.
  src = """
  mod M
    use Std.Operators
    infix `+` : Multiplicative
  end
  """

  assert_error_tag(src, :conflicting_operator_fixity)
end
```

(c) Replace "redeclaring the Melquiades envelope operator is rejected" (:128-138):

```elixir
test "redeclaring the Melquiades envelope operator is rejected" do
  src = """
  mod M
    use Std.Operators
    infix `✉` : Additive
  end
  """

  assert_error_tag(src, :conflicting_operator_fixity)
end
```

(d) Add a new cross-module precedence-cycle test proving the repoint:

```elixir
test "a precedence cycle closed through a used module's group is rejected" do
  src = """
  mod M
    use Std.Operators
    precedencegroup Ga
      associativity: left
      higher_than: Gb
    precedencegroup Gb
      associativity: left
      higher_than: Ga
  end
  """

  assert {:error, {:precedence_cycle, groups}} = Cure.Elab.Program.elaborate(src)
  assert Enum.sort(groups) == [:Ga, :Gb]
end
```

(This same-module cycle already works today; the *cross-module* variant is exercised in `fixity_propagation_test`/`fixity_resolver_test`. Keeping a same-module cycle here guards the repoint didn't break local detection. The genuinely cross-module cycle — A declares `Ga higher_than Gb`, `B use A` declares `Gb higher_than Ga`, cycle seen only in `fixity(B)` — is added in Step 1e.)

(e) Add the true cross-module cycle test (requires a source root). Add to `operator_flip_test.exs`:

```elixir
test "a precedence cycle spanning a use edge is rejected in the importer" do
  dir = Path.join(System.tmp_dir!(), "of_#{System.unique_integer([:positive])}")
  File.mkdir_p!(dir)
  File.write!(Path.join(dir, "a.cure"), "mod A\n  precedencegroup Ga\n    associativity: left\n    higher_than: Gb\nend\n")
  prev = Process.get(:cure_source_roots, [])
  Process.put(:cure_source_roots, [dir])

  src = """
  mod B
    use A
    precedencegroup Gb
      associativity: left
      higher_than: Ga
  end
  """

  try do
    assert {:error, {:precedence_cycle, groups}} = Cure.Elab.Program.elaborate(src)
    assert :Ga in groups and :Gb in groups
  after
    Process.put(:cure_source_roots, prev)
    File.rm_rf!(dir)
  end
end
```

- [ ] **Step 2: Run to verify current failures**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/operator_flip_test.exs`
Expected: the migrated tests and the new cross-module cycle FAIL (cycle still uses builtin+own only; conflicts route may already satisfy (a)-(c) after Task 6 but the cross-module cycle (e) fails).

- [ ] **Step 3: Migrate `program.ex`**

1. Delete the `check_no_builtin_rebind(ast)` call at :115 from the `with` chain in `check_declarations/1`. The chain becomes:

```elixir
with :ok <- check_no_duplicate_defs(ast),
     :ok <- check_no_duplicate_types(ast),
     :ok <- check_no_duplicate_ctors(ast),
     :ok <- check_no_fn_ctor_collision(ast),
     :ok <- check_no_precedence_cycle(ast),
     :ok <- check_proof_shapes(ast) do
  check_no_sibling_collision(ast)
end
```

2. Delete `check_no_builtin_rebind/1` (:148 + its doc comment :140-147).

3. Delete `fixity_decl_nodes/1` (:168-183) — it was used only by the deleted check. (Grep to confirm no other caller: `grep -n fixity_decl_nodes lib/cure/elab/program.ex` → only the deleted references.)

3.5. **Fix the now-stale comment in `lib/cure/compiler/parser.ex`.** `parse_fixity/1`'s preceding comment (~:5595-5598) reads: *"Whether the operator is 'built in' (non-redeclarable) is not marked here — it is decided by LOCATION at elaboration: any operator declared in `Std.Operators` is protected. See `Cure.Elab.Program.check_no_builtin_rebind`."* This names a function this step just deleted and describes the retired location rule. Replace it with:

```elixir
  # `infix|prefix|postfix <op> : Group`. Whether the operator conflicts with
  # an existing declaration is not decided here — it is decided when the
  # module's declarations are folded into `fixity(M)`
  # (`Cure.Compiler.Parser.FixityResolver.assemble/5`): a same-lexeme
  # different-group (or same-group-name different-body) redeclaration is a
  # `:conflicting_operator_fixity` / `:conflicting_precedence_group` error;
  # an identical redeclaration is a no-op.
```

4. Repoint `check_no_precedence_cycle/1` (:130) at `fixity(M)`:

```elixir
defp check_no_precedence_cycle(ast) do
  base = Cure.Compiler.Parser.BuiltinFixity.table()
  own_fixity = Cure.Compiler.Parser.FixityScan.collect_fixity(ast)
  own_uses = Cure.Compiler.Parser.FixityScan.collect_use_targets(ast)

  case Cure.Compiler.Parser.FixityResolver.assemble(base, own_fixity, own_uses, []) do
    {:ok, table} ->
      case Cure.Compiler.Parser.FixityTable.cyclic_groups(table) do
        [] -> :ok
        groups -> {:error, {:precedence_cycle, groups}}
      end

    # A conflict is already reported at parse time (Task 6); by the time
    # elaboration runs, assembly succeeds. Treat a defensive conflict as
    # "no cycle to add" rather than double-reporting.
    {:error, _conflict} ->
      :ok
  end
end
```

`prelude_providers` is `[]` here: the stdlib prelude is already in `base`, and user `@prelude` group contributions are out of scope for cycle detection.

- [ ] **Step 4: Run the migrated tests + the elaboration suite**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/operator_flip_test.exs`
Expected: PASS (all, including both cycle tests and the 3 migrated conflict tests). Then run the broader elaboration suite to catch fallout: `mix test test/cure/elab/` — expect green.

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/elab/program.ex lib/cure/compiler/parser.ex test/cure/compiler/operator_flip_test.exs
git commit -m "feat(fixity): cycle-check on fixity(M); drop builtin-rebind rule"
```

---

## Task 9: Harden `DepGraph.scan_file/1` to statement-level recovery

**Files:**
- Modify: `lib/cure/compiler/dep_graph.ex` (`scan_file/1` :181-220, the `{:error, reason}` branch :200-202)
- Test: `test/cure/compiler/dep_graph_resilience_test.exs` (create)

**Interfaces:**
- Consumes: `FixityScan.harvest_source/3`, `BuiltinFixity.table/0`.
- Produces: when `parse_source` errors but the file still declares a module, `scan_file/1` now recovers `module`, `order_deps`, and `prelude_provider?` from the tolerant harvest, so the file stays in the graph's `modules` map and its `use` edges/`@prelude` flag survive. A file with no recoverable module name still drops (module `nil`) as before.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/dep_graph_resilience_test.exs`:

```elixir
defmodule Cure.Compiler.DepGraphResilienceTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.DepGraph

  setup do
    dir = Path.join(System.tmp_dir!(), "dg_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "a file using a not-yet-resolvable operator keeps its module + use edge", %{dir: dir} do
    a = Path.join(dir, "a.cure")
    b = Path.join(dir, "b.cure")
    File.write!(a, "mod A\n  precedencegroup G\n    associativity: left\n  infix `<?>` : G\nend\n")
    # B's body uses <?>, which a standalone table-naive parse of B cannot bind.
    File.write!(b, "mod B\n  use A\n  fn go() -> Int = 1 <?> 2\nend\n")

    {:ok, graph} = DepGraph.scan([b, a])

    assert Map.has_key?(graph.modules, "B"), "B must survive despite the <?> parse error"
    assert graph.modules["A"] == a
    b_node = graph.nodes[b]
    assert b_node.module == "B"
    assert Enum.any?(b_node.order_deps, &(&1.target == "A"))
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/dep_graph_resilience_test.exs`
Expected: FAIL — B is dropped from `modules` (module stays `nil` under today's all-or-nothing error branch).

- [ ] **Step 3: Harden the error branch of `scan_file/1`**

In `lib/cure/compiler/dep_graph.ex`, the current error branch (:200-202) is:

```elixir
case Cure.Compiler.parse_source(source, file: path) do
  {:error, reason} ->
    %{base | parse_error: reason}

  {:ok, ast} ->
    ... # finalize from ast (module/order_deps/closure_deps/prelude)
end
```

Change the `{:error, reason}` branch to recover declaration-level facts from the tolerant harvest, keeping `parse_error` set (so other consumers still see it) but populating `module`/`order_deps`/`prelude_provider?` so the file is not dropped:

```elixir
{:error, reason} ->
  scan =
    Cure.Compiler.Parser.FixityScan.harvest_source(
      source,
      path,
      Cure.Compiler.Parser.BuiltinFixity.table()
    )

  %{
    base
    | parse_error: reason,
      module: scan.module,
      line: base.line,
      order_deps: Enum.map(scan.uses, fn u -> %{target: u.target, line: u.line} end)
  }
  |> Map.put(:prelude_provider?, scan.prelude?)
```

Notes:
- **`closure_deps` stays `[]` for a recovered node — this is a known, accepted gap, not a bug to fix here.** `finalize_node` (dep_graph.ex:224-227) early-returns the node UNCHANGED whenever `parse_error` is non-nil — it never reaches the third clause that derives `closure_deps` from `order_deps` + the prelude set. Since this recovery branch deliberately keeps `parse_error: reason` set, every node recovered by it hits that early return, so `closure_deps` never gets computed and stays at the `base` map's default `[]`. Verified this does NOT break `order/1` (the CLI/`Cure.Project` compile-order function `cli.ex`/`project.ex` actually call): it reads `node.order_deps` directly and re-filters against `real_map`/`modules` itself (dep_graph.ex:91-99), never `closure_deps`. It DOES mean `closure_deps_map/1` (dep_graph.ex:157-161, docstring "Baking input for Preload") silently under-reports the closure of any module recovered this way — out of scope for this plan (Preload/`closure_deps_map` isn't touched by any task here), but worth the implementer knowing rather than assuming finalization "just works" for these nodes.
- The `{:ok, ast}` branch already sets `:prelude_provider?` via `Map.put(..., prelude_decorated?(ast))` (:210). Confirm the recovered branch's `scan.prelude?` matches `prelude_decorated?` semantics — both derive from the same recognition (Task 3 copied it), so they agree.
- If `scan.module` is `nil` (genuinely unrecoverable), the node still has `module: nil` and drops as before — no regression.

- [ ] **Step 4: Run the resilience test + the DepGraph suite**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/dep_graph_resilience_test.exs test/cure/compiler/dep_graph_test.exs`
Expected: PASS. Existing DepGraph tests must stay green (clean files take the unchanged `{:ok, ast}` path).

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler/dep_graph.ex test/cure/compiler/dep_graph_resilience_test.exs
git commit -m "fix(dep-graph): recover module/use/prelude on recoverable parse error"
```

---

## Task 10: Thread `prelude_provider?` set + `fixity(M)` through the driver and printer

**Files:**
- Modify: `lib/cure/compiler.ex` (`compile_string/2` :85, internal `parse/4` :249 — accept + forward `:prelude_providers`)
- Modify: `lib/cure/cli.ex` (:450-471 — capture prelude set from the graph, thread into `compile_one`)
- Modify: `lib/cure/project.ex` (:765-957 — same, through `compile_all_files`)
- Test: `test/cure/compiler/fixity_propagation_test.exs` (add driver-level test)

**Interfaces:**
- Consumes: `DepGraph.scan/2` result (the `:prelude_provider?` node fields, aggregated to a name set), `Parser.parse/2`'s `:prelude_providers` option (Task 6).
- Produces: a user module marked `@prelude`, discovered by the driver's `DepGraph` scan, contributes its operators to every sibling file compiled in the same run — even siblings with no `use` of it. A bare single-file `Parser.parse` (no driver) still falls back to the compiler-bundled prelude only.

- [ ] **Step 1: Write the failing test**

Add to `test/cure/compiler/fixity_propagation_test.exs`:

```elixir
test "a user @prelude module reaches a sibling via the compile driver", %{dir: dir} do
  # P is @prelude and declares <?>; M does NOT `use P`.
  File.write!(Path.join(dir, "p.cure"), """
  @prelude
  mod P
    precedencegroup G
      associativity: left
    infix `<?>` : G
    fn `<?>`(a: Int, b: Int) -> Int = a
  end
  """)

  File.write!(Path.join(dir, "m.cure"), "mod M\n  fn go() -> Int = 1 <?> 2\nend\n")

  # Simulate the driver: scan the project, extract the prelude-provider name
  # set, and parse M with it threaded in.
  {:ok, graph} = Cure.Compiler.DepGraph.scan([Path.join(dir, "p.cure"), Path.join(dir, "m.cure")])
  providers = Cure.Compiler.prelude_provider_names(graph)
  assert "P" in providers

  prev = Process.get(:cure_source_roots, [])
  Process.put(:cure_source_roots, [dir])

  try do
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(File.read!(Path.join(dir, "m.cure")), emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false, prelude_providers: providers)
  after
    Process.put(:cure_source_roots, prev)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_propagation_test.exs`
Expected: FAIL — `Cure.Compiler.prelude_provider_names/1` undefined.

- [ ] **Step 3a: Expose the prelude-provider name set from a graph**

In `lib/cure/compiler/dep_graph.ex`, add a public accessor (the field is currently only aggregated internally at :64-68):

```elixir
@doc "Module names of every scanned node marked `@prelude`."
@spec prelude_provider_names(t()) :: [String.t()]
def prelude_provider_names(%__MODULE__{nodes: nodes}) do
  for {_path, node} <- nodes,
      Map.get(node, :prelude_provider?, false),
      is_binary(node.module),
      do: node.module
end
```

And re-export it from `Cure.Compiler` (so tests/drivers have one entry point). In `lib/cure/compiler.ex` add:

```elixir
@spec prelude_provider_names(Cure.Compiler.DepGraph.t()) :: [String.t()]
defdelegate prelude_provider_names(graph), to: Cure.Compiler.DepGraph
```

(Reference it in the test as `Cure.Compiler.prelude_provider_names/1`.)

- [ ] **Step 3b: Thread `:prelude_providers` through `compile_string` → `parse/4`**

In `lib/cure/compiler.ex`, in `compile_string/2` (:85) read the option and pass it into the internal `parse`:

```elixir
prelude_providers = Keyword.get(opts, :prelude_providers, [])
# ... existing pipeline ...
# change the internal parse call (:250) to forward it:
```

Update `defp parse(tokens, file, emit?, edition)` (:249) to `defp parse(tokens, file, emit?, edition, prelude_providers)` and its call site (:250) to:

```elixir
Parser.parse(tokens,
  file: file,
  emit_events: emit?,
  edition: edition,
  prelude_providers: prelude_providers
)
```

Thread `prelude_providers` from `compile_string` into that `parse/5` call. (`parse_source/2` at :166 may keep `prelude_providers: []` — it is a single-file utility; pass `[]` explicitly.)

- [ ] **Step 3c: Populate the set in the CLI and project drivers**

In `lib/cure/cli.ex` (:450-465), after the scan, capture the provider set and thread it into each `compile_one`:

```elixir
case Cure.Compiler.DepGraph.scan(files) do
  {:ok, graph} ->
    {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)
    providers = Cure.Compiler.DepGraph.prelude_provider_names(graph)
    # ... existing cycle warnings ...
    compile_opts = Keyword.put(compile_opts, :prelude_providers, providers)
    Enum.each(ordered, &compile_one(&1, compile_opts, verbose?))
```

`compile_one/3` (:468) already forwards `opts` to `Cure.Compiler.compile_file(path, opts)` (:471), which now understands `:prelude_providers` via 3b.

In `lib/cure/project.ex` (:765-767), capture likewise and thread through `compile_all_files/6`:

```elixir
{:ok, graph} ->
  {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)
  providers = Cure.Compiler.DepGraph.prelude_provider_names(graph)
  # carry `providers` to compile_all_files (add a param or put into its opts)
```

In `compile_all_files/6` (:940), add `:prelude_providers` to the `opts` keyword built at :941-952:

```elixir
opts = Keyword.put(opts, :prelude_providers, providers)
```

(Add `providers` as a parameter to `compile_all_files` and pass it at the call site near :773; keep the arity change local — grep `compile_all_files(` to update all call sites.)

- [ ] **Step 3d: Printer fixity threading (defensive)**

`Printer.quoted_to_string/2` already accepts `:fixity` (printer.ex:63). No code change is required for correctness of parsing, but document the requirement: any driver that re-prints a module using a `use`-propagated operator must pass `fixity: fixity(M)` or the operator prints at `:unknown` precedence. Add a one-line note to the `:fixity` option docstring (printer.ex:54-58) pointing at `FixityResolver.assemble/5` as the source of a module-specific table. (No test — this is a doc-only clarification; the formatter/printer suites already cover the default-table path.)

- [ ] **Step 4: Run the driver test + compiler/CLI/project suites**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test test/cure/compiler/fixity_propagation_test.exs test/cure/compiler/compiler_test.exs test/cure/cli_test.exs test/cure/project_test.exs`
Expected: PASS. (Adjust test file names to the actual suite paths — grep `test/` for the CLI/project test files.)

- [ ] **Step 5: Commit**

```bash
cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity
git add lib/cure/compiler.ex lib/cure/compiler/dep_graph.ex lib/cure/cli.ex lib/cure/project.ex lib/cure/compiler/printer.ex test/cure/compiler/fixity_propagation_test.exs
git commit -m "feat(fixity): thread user @prelude providers through the compile driver"
```

---

## Task 11: Full-gate verification

**Files:** none (verification only).

- [ ] **Step 1: Run the complete suite once**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && mix test`
Expected: green. **One run at a time — do not launch concurrently with any other build.**

- [ ] **Step 2: Author-identity check on every new commit**

Run: `cd /Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/use-propagated-fixity && git log 73533a50..HEAD --format='%an <%ae>' | sort -u`
Expected: exactly `Made In Heaven <madeinheaven@madeinheaven.com>`. If any other identity or a co-sign trailer appears, amend before finishing.

- [ ] **Step 3: If any suite is red**, fix red-test-first (failing test reproducing the defect → minimal fix → green), then re-run the full gate once. Do not weaken or delete a behavioral test to make the gate pass.

---

## Self-Review

**1. Spec coverage** (each spec section → task):
- Unified model `fixity(M)` → Tasks 5, 6.
- Table-independent extraction / harvest reuse → Tasks 2, 3.
- Component 1 per-module scanner `own(X)` → Task 3. **Caching scope, partially deferred:** the design's "provenance-scoped caching" discussion (spec lines 124-141) has two parts — (a) `BuiltinFixity.table()` stays an unconditional stdlib-only memo, which Task 7 Step 3b's note addresses; (b) `own(X)`/`fixity(M)` (Component 2) being "memoized per module" for arbitrary `use_reach(M)` modules, which this plan does NOT implement — `SourceResolver.module_path` (Task 4) and `FixityResolver.gather` (Task 5) re-read and re-harvest from disk on every BFS step, with no memoization at all. This is intentionally left uncached rather than unsafely cached: since correctness is what the spec's caching discussion protects (a stale unconditional cache silently missing a user edit), an uncached implementation can never go stale and satisfies that invariant trivially, just without the memoization the spec describes as the eventual per-module cache shape. Flagged here as a known, deliberate scope reduction (performance-only, not correctness) rather than a silent gap — a follow-up may add provenance-scoped memoization to `SourceResolver`/`FixityResolver` per spec Components 1-2 if `use_reach` BFS cost becomes material.
- Component 2 `use`-closure resolver + on-demand name resolution (not DepGraph) → Tasks 4, 5; the `DepGraph.scan_file` precondition → Task 9.
- Component 3 parser hook (3 phases; conflict is a hard whole-module parse error before body parse) → Task 6.
- Component 4 `@prelude` on operators module → Task 7.
- Component 5 conflict detection (operator + precedence-group, per-slot) → Tasks 1, 5; error tags `:conflicting_operator_fixity` / `:conflicting_precedence_group` → Task 1 payloads, Task 6/8 surfacing.
- Overloading vs fixity → conflict keys on declaration nodes only (Tasks 1, 5); no function-def path touched.
- Decisions 1-3 (transitivity, cycles-by-union, one-fixity-per-slot) → Task 5 BFS union + Task 1 per-slot merge.
- Edge cases: single-file fallback → Task 6 test; operator-present/group-absent (`incomparable?`) → existing path, unchanged; prelude bootstrap generalized re-entrancy → Task 7.
- Migration: whole-stdlib-scan revert → never coded (nothing to revert); `declares?/2` retained (used by Task 7 test); `@prelude` added → Task 7; `check_no_precedence_cycle` repoint → Task 8; `check_no_builtin_rebind` deleted (not repointed) → Task 8; `BuiltinFixity.table/0` reimplemented → Task 7; cli/project `prelude_provider?` threading → Task 10; Printer note → Task 10.
- Testing section: scanner (T3), propagation/transitivity (T5/T6), conflict + transitive conflict + group-name conflict (T5), DepGraph resilience (T9), cross-module cycle (T8), prelude-provider use-closure (covered by T5 gather over reach + T10 driver), prelude-still-protected (T8), overload-not-conflict (declaration-only keying, asserted structurally in T5/existing operator_flip "user-declared operator dispatches"), idempotent redeclare (T5), single-file fallback (T6), user @prelude via driver (T10), group-absent degrade (existing `incomparable?`).

**Coverage gaps found & resolved:**
- Spec "Prelude provider's own use-closure propagates" test: the resolver's `gather/4` enqueues each reached module's `.uses` (Task 5), so a `@prelude` provider `P` that `use`s `H` propagates `H`'s operators. Task 10's driver test uses a `@prelude` `P` that declares directly; a `P use H` variant is worth adding during Task 10 but the mechanism is already exercised by Task 5's transitivity test. **Added note:** implementer should add a `P use H` case to Task 10's test if trivial.
- Spec "overload is not a conflict": no dedicated task-owned test. **Resolved:** the existing operator_flip test "a user-declared operator dispatches to its function" plus Task 5's keying-on-declaration-nodes already prove a second `fn <op>` adds no fixity node; add an explicit "two `fn <?>` of different types + one `infix`" acceptance test to Task 5's file during implementation.

**2. Placeholder scan:** The Task 7 `compute/0` intentionally shows a non-compiling `then/2` placeholder FOLLOWED by the clean shipping version, with an explicit "delete the placeholder" instruction — this is a deliberate guard to force reading `build/2`, not an unfilled TODO. All other steps carry complete code. No "TBD"/"handle edge cases"/"similar to Task N" remain.

**3. Type consistency:** `assemble/5` signature identical in Tasks 5, 6, 8. `FixityScan.collect_fixity/1`, `collect_use_targets/1`, `harvest_source/3`, `prelude?/1`, `module_name/1` used with the same arities across Tasks 3, 6, 7, 8, 9. `merge_op/4`/`merge_group/3` payloads (`{:conflicting_operator_fixity, {lexeme, g_a, g_b}}` / `{:conflicting_precedence_group, {name, body_a, body_b}}`) consistent across Tasks 1, 5, 6, 8. `prelude_provider_names/1` defined and used within Task 10 (exposed in Step 3a, consumed in Step 3c) — Task 9 only ensures the underlying `:prelude_provider?` *field* it reads survives a recoverable parse error; it does not define the accessor itself. `uses` shape `%{target, line}` consistent (FixityScan T3 → resolver T5 → dep_graph T9).
