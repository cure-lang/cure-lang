# Automatic Dependency-Ordered Compilation (DepGraph) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace manual/alphabetical module ordering in every Cure build entry point with automatic dependency-graph sorting (`Cure.Compiler.DepGraph`), plus closure-aware stdlib preload and a warning where codegen silently falls back today.

**Architecture:** A pure Elixir module `Cure.Compiler.DepGraph` scans `.cure` files with the headless `Cure.Compiler.parse_source/2`, extracts declared module names, `use`-based order-edges, and (`use` + qualified-call + auto-prelude) closure-edges, and provides deterministic SCC-condensation ordering — cycles compile as a deterministically-ordered group and surface as W086 warnings (spec §3.1 as amended 2026-07-08); duplicate module names remain a hard error. Build entry points (`cure.compile_stage1`, `cure.compile_stdlib`, `Cure.CLI.cmd_compile`, `Cure.Project.compile_project`) feed files through it; multi-file builds load each emitted beam immediately after compiling it. `Cure.Stdlib.Preload` bakes order-only and closure dep maps at Elixir compile time and expands `kind:` selections to their closure.

**Tech Stack:** Elixir (~> 1.14 per mix.exs), ExUnit, `:beam_lib` for beam-import-table assertions. No new dependencies.

**Spec:** `docs/superpowers/specs/tooling/2026-07-08-auto-import-order-design.md` (hardened). Read it before starting; §2 "verified ground truth" explains WHY each change is shaped the way it is.

## Global Constraints

- Compile Cure with OTP 26–28 (AtomVM constraint; do not use OTP-29-only APIs).
- **Never run two full build/test passes concurrently** — one `mix test` / `mix cure.*` build at a time, always sequential.
- No kernel/TCB changes, no elaborator changes, no new surface syntax, no manifest system (spec §3, §6).
- `Cure.Compiler.parse_source/2` is the ONLY front-end entry DepGraph may use.
- Preload's compile-time baking must keep `@external_resource` invalidation for every scanned source.
- Deterministic ordering everywhere: same inputs → identical order (alphabetical tie-break).
- TDD (spec §5): red test first, watch it fail for the stated reason, minimal green, refactor. Tests are immutable once correct — a red test is fixed by changing implementation, never by weakening the test.
- Git commits: author is the user only — NO co-author trailers of any kind.
- Run all commands from the worktree root: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/auto-import-order`.
- `mix test <file>` triggers this repo's compile alias chain (stdlib + stage1 + escript) on first run — that is normal; let it finish. Subsequent runs are incremental.

## Verified AST shapes (probe evidence, 2026-07-08 — trust these)

`Cure.Compiler.parse_source/2` returns `{:ok, ast}` where ast is the container node (or a list of top-level nodes; handle both — see `Cure.Elab.Program.find_module_name/1` which recurses over both shapes):

```elixir
{:container, [container_type: :module, name: "X", language: :cure, line: 1, col: 1],
 [
   {:import, [source: "Std.List", import_type: :use, language: :cure, line: 2, col: 3], []},
   {:import, [items: ["fst"], source: "Std.Pair", import_type: :use, language: :cure, line: 3, col: 3], []},
   {:container, [container_type: :enum, name: "Bool", line: 4, col: 3], [...variants...]},
   {:function_def, [...],
    [{:function_call, [name: "Std.Map.get", line: 5, col: 36], [args...]}]}
 ]}
```

- Top-level module-like containers carry `container_type:` one of `:module | :proof | :fsm | :actor | :supervisor | :app` (confirmed: `parser.ex:4199` emits `container_type: :app` verbatim) with `name:` and `line:` in meta. Nested `container_type: :enum | :struct | :protocol | :trait` are declarations, not modules.
- A `use` is `{:import, meta, []}` with `meta[:source]` = dotted module string, `meta[:line]`.
- A qualified call is `{:function_call, meta, args}` where `meta[:name]` contains `"."`; module part = all segments but the last (mirrors `compile_qualified_call`, `lib/cure/compiler/codegen.ex:1222-1229`).

---

### Task 1: `Cure.Compiler.DepGraph` — scan + order (core)

**Files:**
- Create: `lib/cure/compiler/dep_graph.ex`
- Test: `test/cure/compiler/dep_graph_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.parse_source/2` (`{:ok, ast} | {:error, {:lex_error | :parse_error, _}}`).
- Produces (later tasks rely on these exact names):
  - `DepGraph.scan([Path.t()], keyword()) :: {:ok, %DepGraph{}} | {:error, {:duplicate_module, String.t(), [Path.t()]}}` — opts: `known_modules: [String.t()]` (default `[]`).
  - `%Cure.Compiler.DepGraph{nodes: %{Path.t() => node}, modules: %{String.t() => Path.t()}}` where `node = %{path: Path.t(), module: String.t() | nil, line: pos_integer() | nil, blank?: boolean(), parse_error: term() | nil, order_deps: [%{target: String.t(), line: pos_integer()}], closure_deps: [String.t()]}`
  - `DepGraph.order(%DepGraph{}) :: {:ok, [Path.t()], [cycle]}` where `cycle :: [%{module: String.t(), path: Path.t(), line: pos_integer()}]` is the CLOSED walk of one multi-member SCC (first hop repeated last, `A -> B -> A`). `order/1` NEVER fails on cycles (spec §3.1 as amended 2026-07-08, per the operator's briefing: SCCs compile as a group, not a crash); `cycles` is `[]` on a DAG, one entry per multi-member SCC otherwise.
  - `DepGraph.order_deps_map(%DepGraph{}) :: %{String.t() => [String.t()]}` (in-set targets only, values sorted)

**Semantics to implement (from spec §3.1):**
- Blank file (`String.trim(source) == ""`) → node with `blank?: true`, no module, no edges. `order/1` returns ordered non-blank paths **followed by** blank paths sorted alphabetically (callers like stage1 still print their "skip" lines).
- Parse failure → node with `parse_error: reason`, no edges; participates in ordering as an isolated node (it will fail its own compile later through the existing per-file channel).
- Unreadable file (File.read error) → treat like parse failure with `parse_error: {:file_error, posix}`.
- Order-edges: only `use` targets that are declared by another file **in the set** (`modules` index). Self-edges (`use` of own module) are dropped.
- `order/1` is Kahn's algorithm over in-set order-edges: at each step take the alphabetically-smallest (by path) ready node. When NO node is ready (a cycle blocks progress), break the deadlock deterministically instead of erroring: among the remaining nodes, find the SCC that has no dependencies on nodes OUTSIDE itself within the remaining subgraph (a source SCC of the condensation; if several, the one containing the alphabetically-smallest path), emit its members in alphabetical path order, record its closed cycle walk (each hop's `module`, `path`, and the `line` of the `use` creating the edge to the next hop; first hop repeated as last), delete its members from the working graph, and continue Kahn. Result: `{:ok, ordered_paths ++ blank_paths, cycles}`.
- Duplicate non-nil module name across two files → `{:error, {:duplicate_module, name, [path_a, path_b]}}` from `scan/2` (paths sorted).

- [ ] **Step 1: Write the failing tests**

Create `test/cure/compiler/dep_graph_test.exs`:

```elixir
defmodule Cure.Compiler.DepGraphTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.DepGraph

  @moduletag :tmp_dir

  defp write!(dir, name, contents) do
    path = Path.join(dir, name)
    File.write!(path, contents)
    path
  end

  describe "scan/2 + order/1" do
    test "orders use-dependencies before their dependents", %{tmp_dir: dir} do
      a = write!(dir, "zz_lib.cure", "mod LibA\n  fn ping() -> Int = 41\n")
      b = write!(dir, "aa_user.cure", "mod UserB\n  use LibA\n  fn start() -> Int = ping()\n")

      {:ok, graph} = DepGraph.scan([b, a])
      {:ok, order, []} = DepGraph.order(graph)

      assert order == [a, b]
    end

    test "deterministic: shuffled input, identical output", %{tmp_dir: dir} do
      paths =
        for n <- ["m1", "m2", "m3", "m4"] do
          write!(dir, n <> ".cure", "mod #{String.upcase(n)}\n  fn f() -> Int = 1\n")
        end

      {:ok, g1} = DepGraph.scan(paths)
      {:ok, g2} = DepGraph.scan(Enum.reverse(paths))
      assert DepGraph.order(g1) == DepGraph.order(g2)
      assert {:ok, Enum.sort(paths), []} == DepGraph.order(g1)
    end

    test "cycle: ordering succeeds as an SCC group and reports the closed walk", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod CycA\n  use CycB\n  fn f() -> Int = 1\n")
      b = write!(dir, "b.cure", "mod CycB\n  use CycA\n  fn g() -> Int = 2\n")
      c = write!(dir, "c.cure", "mod Down\n  use CycA\n  fn h() -> Int = 3\n")

      {:ok, graph} = DepGraph.scan([a, b, c])
      # SCC policy (spec §3.1 as amended): no crash — members compile as a
      # group in alphabetical path order, dependents still AFTER the SCC,
      # and the cycle is reported as one closed walk.
      assert {:ok, order, [hops]} = DepGraph.order(graph)

      assert order == [a, b, c]

      modules = Enum.map(hops, & &1.module)
      assert "CycA" in modules and "CycB" in modules
      refute "Down" in modules
      assert Enum.all?(hops, &(is_binary(&1.path) and is_integer(&1.line)))
      # The hop list must be a CLOSED walk, not just "both modules appear
      # somewhere" -- assert it actually loops back to its own start, per
      # the spec's `A (a.cure:3) -> B (b.cure:2) -> A` format.
      assert length(hops) == 3
      assert List.first(hops).module == List.last(hops).module
    end

    test "duplicate module name across files is an error", %{tmp_dir: dir} do
      a = write!(dir, "one.cure", "mod Dup\n  fn f() -> Int = 1\n")
      b = write!(dir, "two.cure", "mod Dup\n  fn g() -> Int = 2\n")

      assert {:error, {:duplicate_module, "Dup", paths}} = DepGraph.scan([a, b])
      assert Enum.sort(paths) == Enum.sort([a, b])
    end

    test "out-of-set use targets impose no ordering", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod OnlyOne\n  use Std.List\n  use NotInSet\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([a])
      assert {:ok, [^a], []} = DepGraph.order(graph)
      assert graph.nodes[a].order_deps == [] or
               Enum.all?(graph.nodes[a].order_deps, &(&1.target in ["Std.List", "NotInSet"]))
    end

    test "blank placeholders sort last; parse failures are isolated nodes", %{tmp_dir: dir} do
      blank = write!(dir, "a_blank.cure", "   \n")
      bad = write!(dir, "b_bad.cure", "mod ((((\n")
      good = write!(dir, "c_good.cure", "mod Good\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([blank, bad, good])
      assert graph.nodes[blank].blank?
      assert graph.nodes[bad].parse_error != nil

      {:ok, order, []} = DepGraph.order(graph)
      assert List.last(order) == blank
      assert bad in order and good in order
    end

    test "self-use is ignored", %{tmp_dir: dir} do
      a = write!(dir, "selfy.cure", "mod Selfy\n  use Selfy\n  fn f() -> Int = 1\n")
      {:ok, graph} = DepGraph.scan([a])
      assert {:ok, [^a], []} = DepGraph.order(graph)
    end

    test "stage1 parity: real lib/compiler tree — every cross-SCC use edge is respected" do
      root = Path.expand("../../..", __DIR__)

      files =
        Path.wildcard(Path.join(root, "lib/compiler/**/*.cure"))
        |> Enum.reject(fn p -> String.trim(File.read!(p)) == "" end)

      {:ok, graph} = DepGraph.scan(files)
      {:ok, order, cycles} = DepGraph.order(graph)
      index = order |> Enum.with_index() |> Map.new()

      # The real tree contains a genuine use cycle (Environment <-> Exception,
      # commit 5ef6d80 — spec §2 fact 6 as amended): it must be REPORTED, and
      # edges inside one SCC are exempt from the ordering property.
      scc_of =
        for {cycle, i} <- Enum.with_index(cycles),
            hop <- cycle,
            into: %{},
            do: {hop.path, i}

      assert Enum.any?(cycles, fn cycle ->
               mods = Enum.map(cycle, & &1.module)

               "Compiler.Kernel.Core.Environment" in mods and
                 "Compiler.Kernel.Core.Exception" in mods
             end),
             "expected the known Environment<->Exception cycle to be reported, got: #{inspect(cycles)}"

      for {path, node} <- graph.nodes,
          %{target: target} <- node.order_deps,
          dep_path = graph.modules[target],
          dep_path != nil,
          # intra-SCC edges are exempt (no valid topological constraint exists)
          scc_of[path] == nil or scc_of[path] != scc_of[dep_path] do
        assert index[dep_path] < index[path],
               "#{target} (#{dep_path}) must precede #{node.module} (#{path})"
      end
    end
  end

  describe "order_deps_map/1" do
    test "maps module names to sorted in-set dep names", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod MA\n  fn f() -> Int = 1\n")
      b = write!(dir, "b.cure", "mod MB\n  use MA\n  use Std.List\n  fn g() -> Int = 2\n")

      {:ok, graph} = DepGraph.scan([a, b])
      assert DepGraph.order_deps_map(graph) == %{"MA" => [], "MB" => ["MA"]}
    end
  end
end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/compiler/dep_graph_test.exs 2>&1 | tail -20`
Expected: FAIL — `module Cure.Compiler.DepGraph is not loaded` (UndefinedFunctionError / CompileError).

- [ ] **Step 3: Implement `lib/cure/compiler/dep_graph.ex`**

```elixir
defmodule Cure.Compiler.DepGraph do
  @moduledoc """
  Dependency graph over a set of `.cure` source files (a *compile set*),
  built with the headless front end (`Cure.Compiler.parse_source/2`) —
  no app boot, no type checking, no codegen.

  Two edge kinds, deliberately distinct (see the 2026-07-08
  auto-import-order design spec, §3.1):

    * **order-edges** — `use` declarations targeting modules declared
      inside the compile set. These gate compile order: classic codegen
      resolves `use`-imported unqualified calls by probing loaded beams.
    * **closure-edges** — the superset (`use` + qualified-call targets +
      auto-prelude). These describe what must be *loadable at runtime*
      and drive preload closure, never compile order: qualified calls
      lower syntactically and are order-free.

  Ordering is deterministic: Kahn's algorithm, alphabetical (path)
  tie-break. Cycles among `use` declarations are NOT an error (spec §3.1
  as amended 2026-07-08): a strongly-connected component compiles as a
  group in alphabetical path order — Cure's compile-set model matches
  Rust's crate-internal modules, where cycles are legal — and each
  multi-member SCC is reported as a closed cycle walk so callers can
  emit the W086 warning. Duplicate module names remain a hard error.
  """

  defstruct nodes: %{}, modules: %{}

  @type node_info :: %{
          path: Path.t(),
          module: String.t() | nil,
          line: pos_integer() | nil,
          blank?: boolean(),
          parse_error: term() | nil,
          order_deps: [%{target: String.t(), line: pos_integer()}],
          closure_deps: [String.t()]
        }

  @type t :: %__MODULE__{
          nodes: %{Path.t() => node_info()},
          modules: %{String.t() => Path.t()}
        }

  @module_container_types [:module, :proof, :fsm, :actor, :supervisor, :app]
  @auto_prelude ["Std.Bool", "Std.Nat"]
  @auto_prelude_types %{"Std.Bool" => "Bool", "Std.Nat" => "Nat"}

  @spec scan([Path.t()], keyword()) ::
          {:ok, t()} | {:error, {:duplicate_module, String.t(), [Path.t()]}}
  def scan(paths, opts \\ []) do
    known = MapSet.new(Keyword.get(opts, :known_modules, []))
    nodes = paths |> Enum.sort() |> Map.new(fn path -> {path, scan_file(path)} end)

    case duplicate_module(nodes) do
      {name, dup_paths} ->
        {:error, {:duplicate_module, name, Enum.sort(dup_paths)}}

      nil ->
        modules =
          for {path, %{module: m}} <- nodes, is_binary(m), into: %{}, do: {m, path}

        universe = MapSet.union(known, MapSet.new(Map.keys(modules)))

        nodes =
          Map.new(nodes, fn {path, node} ->
            {path, finalize_node(node, modules, universe)}
          end)

        {:ok, %__MODULE__{nodes: nodes, modules: modules}}
    end
  end

  @type cycle_hop :: %{module: String.t(), path: Path.t(), line: pos_integer()}

  @spec order(t()) :: {:ok, [Path.t()], [[cycle_hop()]]}
  def order(%__MODULE__{nodes: nodes, modules: modules}) do
    {blank, real} = Enum.split_with(nodes, fn {_p, n} -> n.blank? end)
    blank_paths = blank |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    # Computed once, not per-dependency-per-node: `real` doesn't change
    # while building `edges`, so re-deriving this map inside the inner
    # filter (once per candidate dep) is pure waste, not a correctness
    # concern (the value is identical every time).
    real_map = Map.new(real)

    edges =
      Map.new(real, fn {path, node} ->
        deps =
          node.order_deps
          |> Enum.map(&modules[&1.target])
          |> Enum.filter(&(&1 != nil and &1 != path and Map.has_key?(real_map, &1)))
          |> Enum.uniq()

        {path, deps}
      end)

    {ordered, stuck_groups} = kahn(edges)
    cycles = Enum.map(stuck_groups, &cycle_info(&1, real_map, modules))
    {:ok, ordered ++ blank_paths, cycles}
  end

  @doc "In-set `use` deps by module name (values sorted). Baking input for Preload."
  @spec order_deps_map(t()) :: %{String.t() => [String.t()]}
  def order_deps_map(%__MODULE__{nodes: nodes, modules: modules}) do
    for {_path, %{module: m} = node} <- nodes, is_binary(m), into: %{} do
      deps =
        node.order_deps
        |> Enum.map(& &1.target)
        |> Enum.filter(&(Map.has_key?(modules, &1) and &1 != m))
        |> Enum.uniq()
        |> Enum.sort()

      {m, deps}
    end
  end

  # -- scanning ---------------------------------------------------------------

  defp scan_file(path) do
    base = %{
      path: path,
      module: nil,
      line: nil,
      blank?: false,
      parse_error: nil,
      order_deps: [],
      closure_deps: []
    }

    case File.read(path) do
      {:error, posix} ->
        %{base | parse_error: {:file_error, posix}}

      {:ok, source} ->
        if String.trim(source) == "" do
          %{base | blank?: true}
        else
          case Cure.Compiler.parse_source(source, file: path) do
            {:error, reason} ->
              %{base | parse_error: reason}

            {:ok, ast} ->
              {module, line} = find_module(ast)
              uses = collect_uses(ast)
              qualified = collect_qualified_targets(ast)

              %{
                base
                | module: module,
                  line: line,
                  order_deps: uses,
                  closure_deps: Enum.map(uses, & &1.target) ++ qualified
              }
          end
        end
    end
  end

  defp finalize_node(%{blank?: true} = node, _modules, _universe), do: node
  defp finalize_node(%{parse_error: e} = node, _modules, _universe) when e != nil, do: node

  defp finalize_node(node, _modules, universe) do
    closure =
      node.closure_deps
      |> Enum.filter(&MapSet.member?(universe, &1))
      |> Kernel.++(auto_prelude_deps(node, universe))
      |> Enum.reject(&(&1 == node.module))
      |> Enum.uniq()
      |> Enum.sort()

    order_deps =
      node.order_deps
      |> Enum.reject(&(&1.target == node.module))
      |> Enum.uniq_by(& &1.target)

    %{node | closure_deps: closure, order_deps: order_deps}
  end

  defp auto_prelude_deps(node, universe) do
    declared = declared_type_names_of(node)

    Enum.filter(@auto_prelude, fn prelude ->
      MapSet.member?(universe, prelude) and prelude != node.module and
        not MapSet.member?(declared, Map.fetch!(@auto_prelude_types, prelude))
    end)
  end

  # Declared enum/struct type names are stashed on the node during scan via
  # the process-free path below; recomputed here from closure scan output.
  defp declared_type_names_of(node), do: Map.get(node, :declared_types, MapSet.new())

  defp find_module({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) in @module_container_types do
      {Keyword.get(meta, :name), Keyword.get(meta, :line)}
    else
      {nil, nil}
    end
  end

  defp find_module(list) when is_list(list) do
    Enum.find_value(list, {nil, nil}, fn item ->
      case find_module(item) do
        {nil, nil} -> nil
        found -> found
      end
    end)
  end

  defp find_module(_other), do: {nil, nil}

  defp collect_uses(ast), do: walk(ast, [], &use_collector/2) |> Enum.reverse()

  defp use_collector({:import, meta, _}, acc) when is_list(meta) do
    case Keyword.get(meta, :source) do
      source when is_binary(source) ->
        [%{target: source, line: Keyword.get(meta, :line, 1)} | acc]

      _ ->
        acc
    end
  end

  defp use_collector(_node, acc), do: acc

  defp collect_qualified_targets(ast) do
    walk(ast, [], fn
      {:function_call, meta, _args}, acc when is_list(meta) ->
        name = Keyword.get(meta, :name, "")

        case String.split(name, ".") do
          parts when length(parts) > 1 -> [Enum.join(Enum.drop(parts, -1), ".") | acc]
          _ -> acc
        end

      _node, acc ->
        acc
    end)
    |> Enum.uniq()
  end

  defp walk({_tag, _meta, children} = node, acc, fun) do
    acc = fun.(node, acc)
    walk(children, acc, fun)
  end

  defp walk(list, acc, fun) when is_list(list),
    do: Enum.reduce(list, acc, &walk(&1, &2, fun))

  defp walk(_other, acc, _fun), do: acc

  # -- ordering ---------------------------------------------------------------

  # Deliberately simple, not optimal: pops ONE ready node per round and
  # rebuilds the whole map each time (O(V) per removal, O(V^2) overall)
  # rather than batching the ready set or maintaining reverse-adjacency
  # for O(V+E). Compile sets here are tens to low hundreds of files
  # (stdlib ~39, stage1 kernel ~15) -- this is not a hot path, and the
  # simplicity keeps the alphabetical tie-break obviously correct.
  #
  # Returns {ordered_paths, stuck_groups}: when no node is ready (cycle
  # deadlock), the source SCC of the remaining subgraph is emitted as a
  # group (alphabetical within it) and its internal edge map is collected
  # so order/1 can report the closed cycle walk. Never errors.
  defp kahn(edges), do: do_kahn(edges, [], [])

  defp do_kahn(edges, acc, sccs) when map_size(edges) == 0,
    do: {Enum.reverse(acc), Enum.reverse(sccs)}

  defp do_kahn(edges, acc, sccs) do
    ready =
      edges
      |> Enum.filter(fn {_path, deps} -> deps == [] end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.sort()

    case ready do
      [] ->
        # Cycle deadlock: emit the source SCC of the condensation as a
        # group. A source SCC at a deadlock is always multi-member (a
        # ready singleton would have been picked above).
        {members, scc_edges} = source_scc(edges)

        edges =
          edges
          |> Map.drop(members)
          |> Map.new(fn {p, deps} -> {p, deps -- members} end)

        do_kahn(edges, Enum.reverse(members) ++ acc, [scc_edges | sccs])

      [next | _] ->
        edges =
          edges
          |> Map.delete(next)
          |> Map.new(fn {p, deps} -> {p, List.delete(deps, next)} end)

        do_kahn(edges, [next | acc])
    end
  end

  # The SCC of the remaining subgraph with no dependencies on OTHER
  # remaining SCCs; among several sources, the one containing the
  # alphabetically-smallest path. Returns {sorted_members, scc_edge_map}.
  defp source_scc(edges) do
    sccs = tarjan(edges)
    scc_of = for {members, i} <- Enum.with_index(sccs), m <- members, into: %{}, do: {m, i}

    members =
      sccs
      |> Enum.filter(fn scc_members ->
        Enum.all?(scc_members, fn m ->
          Enum.all?(edges[m], fn d -> scc_of[d] == scc_of[m] end)
        end)
      end)
      |> Enum.min_by(fn scc_members -> Enum.min(scc_members) end)
      |> Enum.sort()

    member_set = MapSet.new(members)

    scc_edges =
      Map.new(members, fn m ->
        {m, Enum.filter(edges[m], &MapSet.member?(member_set, &1))}
      end)

    {members, scc_edges}
  end

  # Standard Tarjan SCC over the (small) stuck subgraph; returns [[path]].
  # Determinism: neighbors and roots visited in sorted order.
  defp tarjan(edges) do
    nodes = edges |> Map.keys() |> Enum.sort()

    {_state, sccs} =
      Enum.reduce(nodes, {%{index: %{}, low: %{}, stack: [], on: MapSet.new(), n: 0}, []}, fn v,
                                                                                             {st,
                                                                                              acc} ->
        if Map.has_key?(st.index, v), do: {st, acc}, else: strongconnect(v, edges, st, acc)
      end)

    Enum.reverse(sccs)
  end

  defp strongconnect(v, edges, st, sccs) do
    st = %{
      st
      | index: Map.put(st.index, v, st.n),
        low: Map.put(st.low, v, st.n),
        stack: [v | st.stack],
        on: MapSet.put(st.on, v),
        n: st.n + 1
    }

    {st, sccs} =
      Enum.reduce(Enum.sort(edges[v] || []), {st, sccs}, fn w, {st, sccs} ->
        cond do
          not Map.has_key?(st.index, w) ->
            {st, sccs} = strongconnect(w, edges, st, sccs)
            {%{st | low: Map.update!(st.low, v, &min(&1, st.low[w]))}, sccs}

          MapSet.member?(st.on, w) ->
            {%{st | low: Map.update!(st.low, v, &min(&1, st.index[w]))}, sccs}

          true ->
            {st, sccs}
        end
      end)

    if st.low[v] == st.index[v] do
      {members, rest} = Enum.split_while(st.stack, &(&1 != v))
      members = members ++ [v]
      rest = tl(rest)

      st = %{st | stack: rest, on: Enum.reduce(members, st.on, &MapSet.delete(&2, &1))}
      {st, [Enum.sort(members) | sccs]}
    else
      {st, sccs}
    end
  end

  defp cycle_info(scc_edges, nodes, modules) do
    path_to_module = for {m, p} <- modules, into: %{}, do: {p, m}
    start = scc_edges |> Map.keys() |> Enum.sort() |> hd()
    hops = trace_cycle(start, scc_edges, [])

    Enum.map(hops, fn path ->
      node = nodes[path]
      module = path_to_module[path] || "?"

      line =
        case Enum.find(node.order_deps, fn d -> modules[d.target] in hops end) do
          %{line: l} -> l
          _ -> node.line || 1
        end

      %{module: module, path: path, line: line}
    end)
  end

  # Do NOT `Enum.uniq/1` the final result: the whole point is to return a
  # CLOSED walk (first hop == last hop, e.g. `[A, B, A]`), matching the
  # spec's `A -> B -> A` format and the Task 3 formatter fixture. `uniq`
  # would strip that closing repeat and silently turn a cycle report into
  # an open chain that no longer shows it loops.
  defp trace_cycle(path, edges, seen) do
    if path in seen do
      Enum.reverse([path | Enum.take_while(seen, &(&1 != path))] ++ [path])
    else
      case edges[path] do
        [next | _] -> trace_cycle(next, edges, [path | seen])
        _ -> Enum.reverse([path | seen])
      end
    end
  end
end
```

Note on `declared_type_names_of/1`: for Task 1 the auto-prelude exclusion set is empty (`Map.get(node, :declared_types, MapSet.new())` — no `:declared_types` key is set yet). Task 2 adds the collection. This is deliberate staging, not an oversight.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/dep_graph_test.exs 2>&1 | tail -10`
Expected: PASS (all tests, 0 failures). The stage1-parity test EXPECTS the known Environment↔Exception cycle (commit `5ef6d80`, spec §2 fact 6 as amended) to be reported in `order/1`'s cycles element; if a DIFFERENT cycle or ordering violation appears, the fix is in DepGraph — investigate before touching the test.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/dep_graph.ex test/cure/compiler/dep_graph_test.exs
git commit -m "feat(compiler): DepGraph — dependency scan + deterministic topo order"
```

---

### Task 2: DepGraph closure edges, `closure/2`, `toposort/2`, auto-prelude exclusions

**Files:**
- Modify: `lib/cure/compiler/dep_graph.ex`
- Test: `test/cure/compiler/dep_graph_test.exs` (append)

**Interfaces:**
- Produces:
  - `DepGraph.closure(%{k => [k]}, [k]) :: [k]` — roots ∪ transitive deps over the map, sorted, missing keys tolerated (contribute nothing). Generic over key type (strings at scan level, atoms for Preload's baked maps).
  - `DepGraph.toposort(%{k => [k]}, [k]) :: [k]` — generic Kahn over the given keys, edges restricted to the given keys, alphabetical (`Enum.sort/1`) tie-break; SCC-tolerant like `order/1` (cycle members emitted as an alphabetical group), so it always returns a full ordering and never errors.
  - `DepGraph.closure_deps_map(%DepGraph{}) :: %{String.t() => [String.t()]}` — per-module closure deps (in-universe filtered, sorted).

- [ ] **Step 1: Write the failing tests** (append inside the outer `describe`-less module, new describes):

```elixir
  describe "closure edges" do
    test "qualified-call targets become closure deps when in the known universe", %{tmp_dir: dir} do
      lib = write!(dir, "libm.cure", "mod LibM\n  fn get(x: Int) -> Int = x\n")

      user =
        write!(dir, "userq.cure", "mod UserQ\n  fn f(x: Int) -> Int = LibM.get(x)\n")

      {:ok, graph} = DepGraph.scan([lib, user])

      assert "LibM" in graph.nodes[user].closure_deps
      # qualified call is NOT an order edge (spec fact 2)
      assert graph.nodes[user].order_deps == []
    end

    test "out-of-universe qualified targets are dropped", %{tmp_dir: dir} do
      user = write!(dir, "u.cure", "mod U2\n  fn f(x: Int) -> Int = Nowhere.get(x)\n")
      {:ok, graph} = DepGraph.scan([user])
      refute "Nowhere" in graph.nodes[user].closure_deps
    end

    test "known_modules extends the universe (stdlib case)", %{tmp_dir: dir} do
      user = write!(dir, "u.cure", "mod U3\n  fn f(x: Int) -> Int = Std.Map.get(x)\n")
      {:ok, graph} = DepGraph.scan([user], known_modules: ["Std.Map", "Std.Bool", "Std.Nat"])
      assert "Std.Map" in graph.nodes[user].closure_deps
    end

    test "auto-prelude Bool/Nat are closure deps unless self or shadowed", %{tmp_dir: dir} do
      plain = write!(dir, "p.cure", "mod Plain\n  fn f() -> Int = 1\n")
      shadow = write!(dir, "s.cure", "mod Shadow\n  type Bool = TT | FF\n  fn f() -> Int = 1\n")

      {:ok, graph} =
        DepGraph.scan([plain, shadow], known_modules: ["Std.Bool", "Std.Nat"])

      assert "Std.Bool" in graph.nodes[plain].closure_deps
      assert "Std.Nat" in graph.nodes[plain].closure_deps
      refute "Std.Bool" in graph.nodes[shadow].closure_deps
      assert "Std.Nat" in graph.nodes[shadow].closure_deps
    end
  end

  describe "closure/2 and toposort/2" do
    test "closure walks transitively and tolerates missing keys" do
      map = %{"A" => ["B"], "B" => ["C"], "C" => [], "X" => ["Y"]}
      assert DepGraph.closure(map, ["A"]) == ["A", "B", "C"]
      assert DepGraph.closure(map, ["X"]) == ["X", "Y"]
      assert DepGraph.closure(%{}, ["R"]) == ["R"]
    end

    test "toposort orders deps first, deterministic, SCC-tolerant on cycles" do
      map = %{"A" => ["B"], "B" => [], "C" => []}
      assert ["B", "A", "C"] = DepGraph.toposort(map, ["A", "B", "C"])
      assert ["B", "C"] = DepGraph.toposort(map, ["C", "B"])

      # cycle members come out as an alphabetical group, dependents after
      cyc = %{"A" => ["B"], "B" => ["A"], "C" => ["A"]}
      assert ["A", "B", "C"] = DepGraph.toposort(cyc, ["C", "B", "A"])
    end
  end
```

- [ ] **Step 2: Run to verify the new tests fail — for the right subset of reasons**

Run: `mix test test/cure/compiler/dep_graph_test.exs 2>&1 | tail -15`

Expected: FAIL, but not uniformly across every test just added. Task 1's `finalize_node/3` already computes `closure_deps` from qualified-call targets and already filters by `universe` (in-set modules ∪ `known_modules`) — so 3 of the 4 new "closure edges" tests ("qualified-call targets become closure deps", "out-of-universe qualified targets are dropped", "known_modules extends the universe") exercise behavior Task 1 already implements and are expected to PASS immediately; they are regression coverage for Task 1, not new red tests for Task 2. The genuinely red tests at this point are: "auto-prelude Bool/Nat are closure deps unless self or shadowed" (fails — `declared_types` collection doesn't exist yet, so the shadow exclusion never fires) and every test under "closure/2 and toposort/2" (fails — `UndefinedFunctionError`, those functions don't exist yet). Confirm the failures match this split before proceeding; if the 3 "already implemented" tests are somehow also failing, that's a Task 1 regression to fix first, not a Task 2 concern.

- [ ] **Step 3: Implement**

In `scan_file/1`, collect declared type names alongside uses (enum/struct containers nested in the body):

```elixir
              declared_types =
                walk(ast, MapSet.new(), fn
                  {:container, m, _}, acc when is_list(m) ->
                    if Keyword.get(m, :container_type) in [:enum, :struct],
                      do: MapSet.put(acc, Keyword.get(m, :name)),
                      else: acc

                  _n, acc ->
                    acc
                end)

              base
              |> Map.put(:declared_types, declared_types)
              |> Map.merge(%{
                module: module,
                line: line,
                order_deps: uses,
                closure_deps: Enum.map(uses, & &1.target) ++ qualified
              })
```

(`declared_type_names_of/1` from Task 1 now finds the key; no other change to `auto_prelude_deps/2`.)

Add the public functions:

```elixir
  @doc "Roots plus transitive dependencies over `dep_map`, sorted. Missing keys contribute nothing."
  @spec closure(%{k => [k]}, [k]) :: [k] when k: term()
  def closure(dep_map, roots) do
    do_closure(dep_map, roots, MapSet.new()) |> MapSet.to_list() |> Enum.sort()
  end

  defp do_closure(_map, [], seen), do: seen

  defp do_closure(map, [root | rest], seen) do
    if MapSet.member?(seen, root) do
      do_closure(map, rest, seen)
    else
      do_closure(map, Map.get(map, root, []) ++ rest, MapSet.put(seen, root))
    end
  end

  @doc """
  Generic deterministic Kahn sort of `keys` using `dep_map` edges restricted
  to `keys`. SCC-tolerant like `order/1`: cycle members are emitted as an
  alphabetical group, so the result is always a complete ordering.
  """
  @spec toposort(%{k => [k]}, [k]) :: [k] when k: term()
  def toposort(dep_map, keys) do
    keyset = MapSet.new(keys)

    edges =
      Map.new(keys, fn k ->
        {k, dep_map |> Map.get(k, []) |> Enum.filter(&(MapSet.member?(keyset, &1) and &1 != k))}
      end)

    {ordered, _sccs} = kahn(edges)
    ordered
  end

  @doc "Per-module closure deps (in-universe filtered, sorted). Baking input for Preload."
  @spec closure_deps_map(t()) :: %{String.t() => [String.t()]}
  def closure_deps_map(%__MODULE__{nodes: nodes}) do
    for {_path, %{module: m} = node} <- nodes, is_binary(m), into: %{} do
      {m, node.closure_deps}
    end
  end
```

- [ ] **Step 4: Run the whole DepGraph test file**

Run: `mix test test/cure/compiler/dep_graph_test.exs 2>&1 | tail -8`
Expected: PASS, 0 failures.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/dep_graph.ex test/cure/compiler/dep_graph_test.exs
git commit -m "feat(compiler): DepGraph closure edges, closure/2, toposort/2"
```

---

### Task 3: Error-registry entries for cycle / duplicate-module / unresolved-import

**Files:**
- Modify: `lib/cure/compiler/errors.ex`
- Test: `test/cure/compiler/dep_graph_errors_format_test.exs` (create)

**Interfaces:**
- Consumes: error tuples produced by DepGraph (`{:import_cycle, hops}`, `{:duplicate_module, name, paths}`) and, in Task 7, codegen's `{:unresolved_import, name, arity, imports, line}` warning tuple.
- Produces: `Cure.Compiler.Errors.format_error/2` clauses so every build entry point gets uniform diagnostics.

- [ ] **Step 1: Verify the actual next free codes.** The E/W/H registry shares ONE numeric sequence (spec §3.1 note: `W081/W082/H083/H084` sit between `E080` and `E085`; `W091` follows `E090`). Run:

```bash
grep -rhoE "\b[EWH]0[0-9][0-9]\b" lib/cure/compiler/errors.ex lib | sort -u | tail -15
```

Expected (as of spec writing): highest used is `W091`; `086`–`089` free. Use: **W086 = import cycle (warning — spec §3.1 as amended: cycles compile as an SCC group and warn, never error)**, **E087 = duplicate module (hard error)**, **W088 = unresolved import fallback (warning)**. If any of these numbers is taken by the time you run this, take the next free numbers in sequence and use them consistently across Tasks 3–7 (and say so in the commit message).

- [ ] **Step 2: Write the failing test**

```elixir
defmodule Cure.Compiler.DepGraphErrorsFormatTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors

  test "import cycle formats as a WARNING with code, module chain and file:line hops" do
    hops = [
      %{module: "CycA", path: "a.cure", line: 3},
      %{module: "CycB", path: "b.cure", line: 2},
      %{module: "CycA", path: "a.cure", line: 3}
    ]

    out = Errors.format_error({:import_cycle, hops}, "a.cure")

    assert out =~ "W086"
    assert out =~ "warning"
    assert out =~ "CycA"
    assert out =~ "CycB"
    assert out =~ "a.cure:3"
    assert out =~ "->"
  end

  test "duplicate module formats with code and both files" do
    out = Errors.format_error({:duplicate_module, "Dup", ["one.cure", "two.cure"]}, "one.cure")
    assert out =~ "E087"
    assert out =~ "Dup"
    assert out =~ "one.cure"
    assert out =~ "two.cure"
  end

  test "unresolved import fallback formats as a warning with code" do
    out =
      Errors.format_error(
        {:unresolved_import, "ping", 0, [:"Cure.LibA"], 7},
        "user.cure"
      )

    assert out =~ "W088"
    assert out =~ "ping/0"
    assert out =~ "Cure.LibA"
    assert out =~ "warning"
  end
end
```

- [ ] **Step 3: Run to verify failure**

Run: `mix test test/cure/compiler/dep_graph_errors_format_test.exs 2>&1 | tail -10`
Expected: FAIL — either `FunctionClauseError`/fallthrough formatting without the codes, depending on `format_error`'s catch-all.

- [ ] **Step 4: Implement.** Add `format_error/2` clauses in `lib/cure/compiler/errors.ex`, next to the existing clauses (see `{:refinement_violation, ...}` at `errors.ex:56-58` for the `format_diagnostic` idiom):

```elixir
  def format_error({:import_cycle, hops}, file) do
    chain =
      hops
      |> Enum.map(fn %{module: m, path: p, line: l} -> "#{m} (#{p}:#{l})" end)
      |> Enum.join(" -> ")

    format_diagnostic(
      "warning",
      "import cycle (W086)",
      file,
      hops |> List.first() |> Map.get(:line, 1),
      "modules form a `use` cycle: #{chain}. " <>
        "They compile together as one group in deterministic order. " <>
        "Type-level mutual recursion across modules is fine; but if these " <>
        "modules CALL each other's imported functions unqualified, resolution " <>
        "inside the group is order-dependent (see W088). Consider qualifying " <>
        "such calls, merging the modules, or dropping a redundant `use`."
    )
  end

  def format_error({:duplicate_module, name, paths}, file) do
    format_diagnostic(
      "error",
      "duplicate module (E087)",
      file,
      1,
      "module '#{name}' is declared by more than one file in this compile set: " <>
        Enum.join(paths, ", ")
    )
  end

  def format_error({:unresolved_import, name, arity, imports, line}, file) do
    probed = imports |> Enum.map(&Atom.to_string/1) |> Enum.join(", ")

    format_diagnostic(
      "warning",
      "unresolved import (W088)",
      file,
      line,
      "call to #{name}/#{arity} matches no export of the imported modules " <>
        "(probed: #{probed}); emitting a local call. If #{name} lives in an " <>
        "imported module, make sure that module is compiled and loaded before " <>
        "this file, or qualify the call."
    )
  end
```

Also register explanations in the long-form code table (the `"E030" => """..."""` map in the same file): add `"W086"`, `"E087"`, `"W088"` entries with a 3-6 line explanation + fix guidance each, in the same prose style as the neighbors (W086's should state the SCC-group compile behavior and when a cycle is harmless vs. when W088 makes it actionable).

- [ ] **Step 5: Run the test — PASS. Then commit**

```bash
mix test test/cure/compiler/dep_graph_errors_format_test.exs 2>&1 | tail -5
git add lib/cure/compiler/errors.ex test/cure/compiler/dep_graph_errors_format_test.exs
git commit -m "feat(errors): W086 import cycle, E087 duplicate module, W088 unresolved import"
```

---

### Task 4: `mix cure.compile_stage1` — delete the hardcoded table, order via DepGraph

**Files:**
- Modify: `lib/mix/tasks/cure.compile_stage1.ex` (delete `stage1_group/1` `:106-118` and `stage1_sort_key/1` `:100-104`)

**Interfaces:**
- Consumes: `DepGraph.scan/2`, `DepGraph.order/1`, `Errors.format_error/2`.
- Produces: no API change — same task, same flags, same output shape (`stage1: N compiled, M placeholders, 0 errors`).

The stage1-parity property test (Task 1, Step 1, last test in the first `describe`) is the red/green gate for correctness of the derived order on the real tree; it is already green. This task swaps the mechanism and verifies the build end-to-end.

- [ ] **Step 1: Capture the BEFORE state (module set + count)**

```bash
mix cure.compile_stage1 2>&1 | tail -3
ls _build/cure/stage1/ebin/*.beam | sort > /tmp/stage1_before.txt; wc -l /tmp/stage1_before.txt
```

Expected: `stage1: 11 compiled, 15 placeholders, 0 errors` (counts may drift as the tree grows — record whatever they are).

- [ ] **Step 2: Replace the ordering.** In `lib/mix/tasks/cure.compile_stage1.ex`, replace

```elixir
    files =
      @source_dir
      |> Path.join("**/*.cure")
      |> Path.wildcard()
      |> Enum.sort_by(&stage1_sort_key/1)
      |> maybe_reject_tests(include_tests?)
```

with

```elixir
    candidates =
      @source_dir
      |> Path.join("**/*.cure")
      |> Path.wildcard()
      |> maybe_reject_tests(include_tests?)

    files =
      case Cure.Compiler.DepGraph.scan(candidates) do
        {:ok, graph} ->
          {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)

          Enum.each(cycles, fn walk ->
            Mix.shell().info(Cure.Compiler.Errors.format_error({:import_cycle, walk}, @source_dir))
          end)

          ordered

        {:error, reason} ->
          Mix.shell().error(Cure.Compiler.Errors.format_error(reason, @source_dir))
          exit({:shutdown, 1})
      end
```

Note: `order/1` cannot fail (SCC policy); only `scan/2` can (`duplicate_module`). The known Environment↔Exception kernel cycle will print one W086 warning per stage1 build — that is intended, honest output, not a defect.

and delete `stage1_sort_key/1` and all `stage1_group/1` clauses entirely. Keep `maybe_reject_tests/2`, `blank_source?/1`, and everything else unchanged (DepGraph puts blank files last; the loop still prints `skip` for them).

- [ ] **Step 3: Rebuild and compare AFTER vs BEFORE**

```bash
mix cure.compile_stage1 2>&1 | tail -3
ls _build/cure/stage1/ebin/*.beam | sort > /tmp/stage1_after.txt
diff /tmp/stage1_before.txt /tmp/stage1_after.txt && echo IDENTICAL_MODULE_SET
```

Expected: same `N compiled, M placeholders, 0 errors` counts as Step 1, and `IDENTICAL_MODULE_SET`.

- [ ] **Step 4: Run the DepGraph suite once more (guard against regressions)**

Run: `mix test test/cure/compiler/dep_graph_test.exs 2>&1 | tail -5`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/mix/tasks/cure.compile_stage1.ex
git commit -m "feat(build): stage1 compile order derived from DepGraph, hardcoded table deleted"
```

---

### Task 5: `mix cure.compile_stdlib` — DepGraph order + code path before the loop

**Files:**
- Modify: `lib/mix/tasks/cure.compile_stdlib.ex`

**Interfaces:** consumes `DepGraph.scan/2`/`order/1`/`Errors.format_error/2`; no API change.

- [ ] **Step 1: Replace alphabetical order.** In `run/1`, replace

```elixir
    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure")) |> Enum.sort()
```

with

```elixir
    cure_files =
      case Cure.Compiler.DepGraph.scan(Path.wildcard(Path.join(stdlib_dir, "*.cure"))) do
        {:ok, graph} ->
          {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)

          Enum.each(cycles, fn walk ->
            Mix.shell().info(Cure.Compiler.Errors.format_error({:import_cycle, walk}, stdlib_dir))
          end)

          ordered

        {:error, reason} ->
          Mix.shell().error(Cure.Compiler.Errors.format_error(reason, stdlib_dir))
          exit({:shutdown, 1})
      end
```

(The stdlib graph is currently a DAG, so no W086 prints today; the branch exists for when a cycle appears.)

- [ ] **Step 2: Register the output dir on the code path BEFORE compiling.** Move this block (currently after the compile loop, `compile_stdlib.ex:71-77`):

```elixir
        # Add to code path
        File.mkdir_p!(output_dir)
        abs_dir = Path.expand(output_dir)

        unless abs_dir in :code.get_path() do
          :code.add_patha(String.to_charlist(abs_dir))
        end
```

to immediately BEFORE `results = Enum.map(cure_files, ...)` (inside the `true ->` branch, after the `Mix.shell().info("Compiling Cure standard library ...")` line). Delete the original post-loop copy.

- [ ] **Step 3: Full stdlib build, verify clean**

```bash
mix cure.compile_stdlib 2>&1 | tail -4
```

Expected: `39 compiled, 0 errors` (count = number of `lib/std/*.cure` files; take the count the BEFORE build prints — it must not shrink) and `Output: _build/cure/ebin`.

- [ ] **Step 4: Commit**

```bash
git add lib/mix/tasks/cure.compile_stdlib.ex
git commit -m "feat(build): stdlib compile in DepGraph order, code path registered up front"
```

---

### Task 6: Ordered + loaded multi-file builds (`Cure.Project` + `Cure.CLI.cmd_compile`)

**Files:**
- Modify: `lib/cure/compiler.ex` (add `load_emitted/2`)
- Modify: `lib/cure/project.ex` (`compile_project/2` ordering, `compile_all_files/5` load-after-compile)
- Modify: `lib/cure/cli.ex` (`cmd_compile/2`: union file set, order, load after compile)
- Test: `test/cure/project/multi_file_link_test.exs` (create)

**Interfaces:**
- Consumes: `DepGraph.scan/2`, `DepGraph.order/1`.
- Produces: `Cure.Compiler.load_emitted(module(), Path.t()) :: :ok | {:error, term()}` — loads `<output_dir>/<module>.beam` via `:code.load_binary/3` (the `Preload.load_if_present/2` pattern: no global code-path pollution). Later tasks/tests may use it.

- [ ] **Step 1: Write the failing linkage test (red today — this is the bug the spec's §5.3 names)**

```elixir
defmodule Cure.Project.MultiFileLinkTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  # aa_user.cure sorts alphabetically BEFORE zz_lib.cure, so today's
  # Enum.sort() order compiles the dependent first, and since compiled
  # beams are never loaded between files, codegen's resolve_import finds
  # nothing and silently emits a LOCAL call (codegen.ex:1208-1213).
  # After DepGraph ordering + load-after-compile, the beam import table
  # must carry the remote call.
  test "user->user use + unqualified call produces a remote call regardless of filename order",
       %{tmp_dir: dir} do
    src = Path.join(dir, "src")
    out = Path.join(dir, "ebin")
    File.mkdir_p!(src)

    File.write!(Path.join(src, "aa_user.cure"), """
    mod LinkUser
      use LinkLib
      fn start() -> Int = ping()
    """)

    File.write!(Path.join(src, "zz_lib.cure"), """
    mod LinkLib
      fn ping() -> Int = 41
    """)

    File.write!(Path.join(dir, "Cure.toml"), """
    [project]
    name = "linktest"
    version = "0.1.0"
    source_paths = ["src"]
    """)

    {:ok, project} = Cure.Project.load(dir)

    assert {:ok, %{modules: modules}} =
             Cure.Project.compile_project(project, output_dir: out, check_types: false)

    assert :"Cure.LinkUser" in modules and :"Cure.LinkLib" in modules

    beam = Path.join(out, "Cure.LinkUser.beam")
    {:ok, {_, [{:imports, imports}]}} = :beam_lib.chunks(String.to_charlist(beam), [:imports])

    assert {:"Cure.LinkLib", :ping, 0} in imports,
           "expected remote call Cure.LinkLib.ping/0 in beam import table, got: #{inspect(imports)}"
  end
end
```

Verified (`lib/cure/project.ex:711-715, 749-767`): `source_paths` is parsed exclusively from the `[project]` table (`parsed.project`, via `apply_kv({:table, "project"}, ...)` special-casing the key through `parse_scalar/1` for its array form) — there is no `[compiler] source_paths`. The fixture above reflects this. `Cure.Project.load/1` takes a single directory arg (default `"."`) and returns `{:ok, %Cure.Project{}} | {:error, term()}`, matching the call above. If a future project.ex refactor moves this key, the fixture's TOML shape is the part to adjust — the test's assertion (remote call in the import table) is the immutable part.

- [ ] **Step 2: Run to verify it fails for the right reason**

Run: `mix test test/cure/project/multi_file_link_test.exs 2>&1 | tail -15`
Expected: FAIL on the final assertion — `{:"Cure.LinkLib", :ping, 0}` NOT in imports (the beam compiled with a local call). If it fails earlier (project loading), fix the fixture per the note above until the failure is the import-table assertion — that exact red is required before proceeding.

- [ ] **Step 3: Add `Cure.Compiler.load_emitted/2`** in `lib/cure/compiler.ex` (public section, near `compile_file/2`):

```elixir
  @doc """
  Load a just-emitted `<output_dir>/<module>.beam` into the VM via
  `:code.load_binary/3` — no code-path mutation. Used by multi-file
  builds so later files' codegen can resolve imports of earlier ones.
  """
  @spec load_emitted(module(), Path.t()) :: :ok | {:error, term()}
  def load_emitted(module, output_dir) when is_atom(module) and is_binary(output_dir) do
    path = Path.join(output_dir, "#{module}.beam")

    with {:ok, binary} <- File.read(path),
         {:module, ^module} <- :code.load_binary(module, String.to_charlist(path), binary) do
      :ok
    else
      {:error, reason} -> {:error, reason}
    end
  end
```

- [ ] **Step 4: Order + load in `Cure.Project`.** In `compile_project/2` (`project.ex:522`), replace

```elixir
    cure_files =
      extra_paths
      |> Enum.flat_map(fn dir ->
        if File.dir?(dir), do: Path.wildcard(Path.join(dir, "**/*.cure")), else: []
      end)
      |> Enum.sort()
```

with

```elixir
    discovered =
      extra_paths
      |> Enum.flat_map(fn dir ->
        if File.dir?(dir), do: Path.wildcard(Path.join(dir, "**/*.cure")), else: []
      end)

    cure_files_result =
      case Cure.Compiler.DepGraph.scan(discovered) do
        {:ok, graph} ->
          {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)

          Enum.each(cycles, fn walk ->
            Logger.warning(Cure.Compiler.Errors.format_error({:import_cycle, walk}, project.root))
          end)

          {:ok, ordered}

        {:error, _} = err ->
          err
      end
```

(`Cure.Project` already `require Logger`? Verify — if not, add `require Logger` at the top of the module; `Logger.warning/1` is the right channel for a library function, matching how the CLI layer prints and tests capture logs.)

and thread it through the `with`:

```elixir
    with {:ok, cure_files} <- cure_files_result,
         {:ok, app_info} <- detect_app(cure_files, project),
         ...rest unchanged...
```

In `compile_all_files/5` (`project.ex:650`), load each beam right after its successful compile:

```elixir
      Enum.reduce_while(files, {:ok, []}, fn file, {:ok, acc} ->
        case Cure.Compiler.compile_file(file, opts) do
          {:ok, module, _warnings} ->
            # Best-effort: callback-mode/actor/sup/app containers load
            # themselves during codegen and may have no beam on disk.
            _ = Cure.Compiler.load_emitted(module, output_dir)
            {:cont, {:ok, [module | acc]}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)
```

- [ ] **Step 5: Order + load in `Cure.CLI.cmd_compile`.** Replace the per-path `Enum.each` (`cli.ex:488-497`) with a union-then-order pass (spec §3.2 item 3: the compile set is the union across ALL path arguments):

```elixir
    files =
      Enum.flat_map(paths, fn path ->
        if File.dir?(path) do
          path |> Path.join("**/*.cure") |> Path.wildcard()
        else
          [path]
        end
      end)
      |> Enum.uniq()

    ordered =
      case Cure.Compiler.DepGraph.scan(files) do
        {:ok, graph} ->
          {:ok, ordered, cycles} = Cure.Compiler.DepGraph.order(graph)

          Enum.each(cycles, fn walk ->
            warn(Cure.Compiler.Errors.format_error({:import_cycle, walk}, hd(paths)))
          end)

          ordered

        {:error, reason} ->
          diagnostic(Cure.Compiler.Errors.format_error(reason, hd(paths)))
          exit({:shutdown, 1})
      end

    Enum.each(ordered, &compile_one(&1, compile_opts, verbose?))
```

and in `compile_one/3` (`cli.ex:500-517`), after the `{:ok, module, warnings}` branch's existing prints, add:

```elixir
        _ = Cure.Compiler.load_emitted(module, Keyword.fetch!(opts, :output_dir))
```

- [ ] **Step 6: Run the linkage test — PASS**

Run: `mix test test/cure/project/multi_file_link_test.exs 2>&1 | tail -8`
Expected: PASS. The import table now contains `{:"Cure.LinkLib", :ping, 0}`.

- [ ] **Step 7: Guard: DepGraph + errors suites still green**

Run: `mix test test/cure/compiler/dep_graph_test.exs test/cure/compiler/dep_graph_errors_format_test.exs 2>&1 | tail -5`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/compiler.ex lib/cure/project.ex lib/cure/cli.ex test/cure/project/multi_file_link_test.exs
git commit -m "feat(build): ordered multi-file compiles with load-after-compile (Project + CLI)"
```

---

### Task 7: Codegen warnings plumbing + W088 unresolved-import warning

**Files:**
- Modify: `lib/cure/compiler/codegen.ex` (struct `:warnings`, function_call cond restructure, `compile_module_container` return, `compile_module` return)
- Modify: `lib/cure/compiler.ex` (`codegen/5`, `write_beam_forms/4` → `/5` merge, `compile_and_load/2` binding)
- Test: `test/cure/compiler/unresolved_import_warning_test.exs` (create)

**Interfaces:**
- Produces: `Cure.Compiler.Codegen.compile_module/2` now returns `{:ok, forms, warnings :: [term()]}` for module containers (special containers return `{:ok, {:callback_mode | :actor | :supervisor | :app, mod}, []}`); `Cure.Compiler.compile_file/2` merges codegen warnings ahead of BeamWriter warnings in its `{:ok, module, warnings}` result. Warning term: `{:unresolved_import, name :: String.t(), arity :: non_neg_integer(), imports :: [module()], line :: pos_integer()}` (exactly what Task 3's W088 formatter consumes).

- [ ] **Step 1: Find every `compile_module` caller** (they all need the 3-tuple):

```bash
grep -rn "Codegen.compile_module\|Codegen\.compile_module(" lib test | grep -v "_build"
```

This grep surfaces two different kinds of hits, with different treatment:

- **The implementation caller**: `lib/cure/compiler.ex` `codegen/5` (`compiler.ex:268-272`) — update as Step 5 shows.
- **Pre-existing test callers** that pattern-match `Codegen.compile_module/2`'s CURRENT bare-tuple contract directly (not `Cure.Compiler.compile_file/2` — that public contract is already 3-tuple and is untouched by this task): `test/cure/app/app_test.exs`, `test/cure/fsm/fsm_test.exs`, `test/cure/sup/sup_test.exs`, `test/cure/actor/actor_test.exs`, `test/cure/compiler/codegen_test.exs`, `test/cure/compiler/melquiades_parser_test.exs`, `test/cure/compiler/with_abs_codegen_test.exs`, `test/cure/compiler/shadow_codegen_test.exs`, `test/cure/compiler/bin_segment_test.exs`. These assert shapes like `{:ok, forms} = Codegen.compile_module(...)` or `{:ok, {:app, mod}} = Codegen.compile_module(...)`. Once Step 4 makes `compile_module/2` uniformly return 3-tuples, every one of these must have its pattern updated (e.g. `{:ok, forms, _warnings} = ...`, `{:ok, {:app, mod}, _warnings} = ...`).

  **This is legitimate API-contract migration, not "weakening a red test"**: these are pre-existing tests asserting on an internal function's return arity, not red tests written during this plan's own TDD process, and the behavior they actually check (which forms/module get produced) is unchanged — only the wrapper arity grows by one element to carry warnings. Update them in the same commit as the implementation, and re-run the full suite (Step 6) to catch any caller this grep missed.

- [ ] **Step 2: Write the failing test**

```elixir
defmodule Cure.Compiler.UnresolvedImportWarningTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "imported-but-unresolvable unqualified call compiles with a W088 warning",
       %{tmp_dir: dir} do
    # `use Ghost` imports a module that exports no `phantom/0`; the call
    # falls back to a local call (unchanged behavior) but must WARN now.
    ghost = Path.join(dir, "ghost.cure")
    File.write!(ghost, "mod Ghost\n  fn real() -> Int = 1\n")

    user = Path.join(dir, "user.cure")

    File.write!(user, """
    mod GhostUser
      use Ghost
      fn start() -> Int = phantom()
    """)

    out = Path.join(dir, "ebin")

    assert {:ok, _mod, _w} =
             Cure.Compiler.compile_file(ghost, output_dir: out, emit_events: false)

    :ok = Cure.Compiler.load_emitted(:"Cure.Ghost", out)

    assert {:ok, :"Cure.GhostUser", warnings} =
             Cure.Compiler.compile_file(user,
               output_dir: out,
               emit_events: false,
               check_types: false
             )

    assert Enum.any?(warnings, fn
             {:unresolved_import, "phantom", 0, mods, _line} -> :"Cure.Ghost" in mods
             _ -> false
           end),
           "expected an :unresolved_import warning, got: #{inspect(warnings)}"
  end
end
```

- [ ] **Step 3: Run to verify it fails for the right reason**

Run: `mix test test/cure/compiler/unresolved_import_warning_test.exs 2>&1 | tail -10`

Expected: FAIL — `{:ok, :"Cure.GhostUser", warnings}` does not match. The fixture as written does NOT reach the `{:ok, ...}` path at all today: `phantom` is neither a local function of `GhostUser` nor an export of `Ghost`, so codegen's fallback emits a local call `{:atom, line, :phantom}` to a function nothing defines, and Erlang's `erl_lint` always rejects a local call to an undefined function — there is no fixture shape that is simultaneously (a) genuinely unresolved (exercises the fallback) and (b) lint-clean, because lint-clean requires the name to be defined *somewhere* in the module, which would make it `is_local` and skip the fallback entirely. So `compile_file(user, ...)` returns `{:error, {:beam_lint_error, errors}}` today (compiler.ex:117-134), not `{:ok, ...}` — this is the honest, permanent shape of this case, not a fixture bug to iterate away.

This means the test above is wrong about *where* the warning surfaces, and must be corrected before it can ever go green — per the test-immutability rule's escape hatch (a test proven wrong before it was ever green may be fixed, with the reasoning stated up front, which is what the paragraph above is). The fix: thread codegen warnings onto the lint-error path too, since that's the path this case actually takes. Extend the existing 2-tuple error reason to a 3-tuple *only* when codegen produced warnings — `{:beam_lint_error, errors}` stays as today's shape when there are none, so no other caller's pattern match is disturbed. Replace the test's final assertions with:

```elixir
    assert {:error, {:beam_lint_error, _lint, warnings}} =
             Cure.Compiler.compile_file(user,
               output_dir: out,
               emit_events: false,
               check_types: false
             )

    assert Enum.any?(warnings, fn
             {:unresolved_import, "phantom", 0, mods, _line} -> :"Cure.Ghost" in mods
             _ -> false
           end)
```

Re-run: still FAIL (now on the pattern match itself — `compile_file` returns the bare 2-tuple `{:error, {:beam_lint_error, errors}}` today, which doesn't match the 3-tuple pattern at all). This is the one fixture and the one pair of assertions to implement Steps 4-5 against.

(The green-path merge — codegen warnings prepended to BeamWriter warnings in `{:ok, module, warnings}` — is implemented in Step 5 alongside this; it fires whenever the fallback target exists locally under the same name and the module lints clean, e.g. Task 6's linkage fixture.)

- [ ] **Step 4: Implement in codegen.** In `lib/cure/compiler/codegen.ex`:

(a) Add to the defstruct (`codegen.ex:29-45`): `warnings: [],`

(b) Restructure the function_call cond (`codegen.ex:~1160-1218`) so every arm yields `{form, state}` and the import-fallback arm records the warning. The current shape ends with the cond producing `form` and a trailing `{form, state}`; change to `{form, state} = cond do ... end` with each arm returning a tuple. The final (`true ->`) arm becomes:

```elixir
          true ->
            fn_atom = mangle_fn_name(name)
            arity = length(arg_forms)
            local_fns = Map.get(state, :local_fns, [])

            is_local =
              Enum.any?(state.exports ++ local_fns, fn {n, a} -> n == fn_atom and a == arity end)

            if is_local or state.imports == [] do
              {{:call, line, {:atom, line, fn_atom}, arg_forms}, state}
            else
              case resolve_import(fn_atom, arity, state.imports) do
                {:ok, mod_atom} ->
                  {{:call, line, {:remote, line, {:atom, line, mod_atom}, {:atom, line, fn_atom}},
                    arg_forms}, state}

                :not_found ->
                  case resolve_protocol_call(name, arity, line) do
                    {:ok, form} ->
                      {form, state}

                    :not_found ->
                      state = %{
                        state
                        | warnings: [
                            {:unresolved_import, name, arity, state.imports, line}
                            | state.warnings
                          ]
                      }

                      {{:call, line, {:atom, line, fn_atom}, arg_forms}, state}
                  end
              end
            end
```

All other arms wrap their existing form expression as `{<form-expr>, state}` unchanged.

(c) In `compile_module_container/4`, include the collected warnings in the return: where it currently returns `{:ok, forms}` (after the events emit), return `{:ok, forms, Enum.reverse(state.warnings)}`. The `validate_stdlib_imports` error branch is unchanged.

(d) The `:fsm`/`:actor`/`:supervisor`/`:app` branches of `dispatch_container/6` (codegen.ex:134-201) return whatever `Cure.FSM.Compiler.compile/2`, `Cure.Actor.Compiler.compile/2`, `Cure.Sup.Compiler.compile/2`, and `Cure.App.Compiler.compile/2` return, UNCHANGED — those are four separate modules, each with its own documented `{:ok, {:actor, module()}}`-shaped `@spec` and their own test coverage; do not touch them or their bare-tuple contract. `:fsm` in particular can ALSO return a plain forms list (`{:ok, list()}`, simple-mode FSM) — the same shape `compile_module_container` used to return before this task's edit — so a shape-only check ("is this a 3-tuple already?") is the correct place to normalize, not a per-container-type rewrite. Do the wrapping once, at `compile_module/2`'s own two call sites into `dispatch_container` (both the `{:container, ...}` clause and the `{:block, ...}` clause), with a small private helper:

```elixir
  defp normalize_compile_result({:ok, _forms, _warnings} = ok), do: ok
  defp normalize_compile_result({:ok, other}), do: {:ok, other, []}
  defp normalize_compile_result({:error, _} = err), do: err
```

and wrap both `dispatch_container(...)` calls in `compile_module/2` with `normalize_compile_result(...)`. This makes `compile_module/2` uniformly return a 3-tuple (module containers already 3-tuple straight from `compile_module_container`; every other shape gets `[]` appended) without any of the four container compilers ever knowing warnings exist. Update `compile_module/2`'s `@spec` (codegen.ex:85-91) to reflect the 3-tuple return in every branch.

- [ ] **Step 5: Thread through `lib/cure/compiler.ex`.**

(a) `codegen/5` (`compiler.ex:258-274`): classic branch becomes

```elixir
      case Codegen.compile_module(ast, opts) do
        {:ok, forms, cg_warnings} -> {:ok, forms, cg_warnings}
        {:error, reason} -> {:error, {:codegen_error, reason}}
      end
```

and the `if Cure.Elab.Program.dependent?(ast) do ... end` branch of `codegen/5` wraps `dependent_codegen/1`'s result the same way, since the kernel-lowering path never produces codegen warnings:

```elixir
    if Cure.Elab.Program.dependent?(ast) do
      case dependent_codegen(ast) do
        {:ok, forms} -> {:ok, forms, []}
        {:error, _} = err -> err
      end
    else
      ...
    end
```

(b) `codegen/5` now always returns a 3-tuple on success, so every `with`-chain that binds its result must widen its pattern — but the THREE consumers do not all do the same thing with the extra element:

- **`compile_string/2`** (and `compile_file/2`, which delegates to it): bind `{:ok, forms, cg_warnings} <- codegen(...)` and pass `cg_warnings` into `write_beam_forms/5` for the `forms when is_list(forms)` case (the `{:callback_mode, mod}`/`{:actor, mod}`/`{:supervisor, mod}`/`{:app, mod}` cases already return `{:ok, mod, []}` today and need no change).
- **`compile_and_load/2`** does NOT call `write_beam_forms` at all — its `forms when is_list(forms)` case calls `BeamWriter.compile_and_load(forms)` directly, and its documented public contract is `{:ok, module()}` with no warnings element. Bind `{:ok, forms, _cg_warnings} <- codegen(ast, file, emit?, nil, declared_phases)` and simply discard the third element — codegen warnings are not surfaced through this entry point (it exists for REPL/testing, and its return shape is intentionally unchanged):

```elixir
    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms, _cg_warnings} <- codegen(ast, file, emit?, nil, declared_phases) do
      case forms do
        {:callback_mode, mod_atom} -> {:ok, mod_atom}
        {:actor, mod_atom} -> {:ok, mod_atom}
        {:supervisor, mod_atom} -> {:ok, mod_atom}
        {:app, mod_atom} -> {:ok, mod_atom}
        forms when is_list(forms) -> BeamWriter.compile_and_load(forms)
      end
    end
```

For `compile_string/2`, thread `cg_warnings` into `write_beam_forms/5`:

```elixir
  defp write_beam_forms(forms, output_dir, emit?, file, cg_warnings) do
    case BeamWriter.compile_forms(forms) do
      {:ok, module, binary, warnings} ->
        case BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
          :ok -> {:ok, module, cg_warnings ++ warnings}
          {:error, _} = err -> err
        end

      {:error, errors, _warnings} when cg_warnings != [] ->
        {:error, {:beam_lint_error, errors, cg_warnings}}

      {:error, errors, _warnings} ->
        {:error, {:beam_lint_error, errors}}
    end
  end
```

The special-container `{:ok, mod_atom, []}` returns in `compile_string/2` (`compiler.ex:98-110`) stay as-is (append nothing). `compile_and_load/2` is handled separately, per (b) above — it binds the 3-tuple and discards the warnings element rather than calling `write_beam_forms`.

(c) Add to `lib/cure/compiler/errors.ex` a 3-element lint clause delegating per-warning to the W088 formatter:

```elixir
  def format_error({:beam_lint_error, errors, warnings}, file) do
    warned = Enum.map_join(warnings, "\n", &format_error(&1, file))
    warned <> "\n" <> format_error({:beam_lint_error, errors}, file)
  end
```

(place it near the existing `{:beam_lint_error, errors}` clause, i.e. well above the file's catch-all `format_error(error, file)` clause at the bottom — that catch-all, not the 2-tuple clause, is the only thing that could otherwise swallow the 3-tuple match, since a 2-tuple and 3-tuple pattern never overlap regardless of order).

- [ ] **Step 6: Run the warning test + neighbors**

```bash
mix test test/cure/compiler/unresolved_import_warning_test.exs 2>&1 | tail -8
mix test test/cure/compiler/codegen_test.exs test/cure/compiler/dep_graph_test.exs test/cure/project/multi_file_link_test.exs 2>&1 | tail -8
```

Expected: PASS, given the Step 1 test-file updates (the 9 files listed there) are already applied. `test/cure/compiler/codegen_test.exs` and `test/cure/project/multi_file_link_test.exs` in particular exercise both the direct `Codegen.compile_module/2` 3-tuple and the public `Cure.Compiler.compile_file/2` contract (unchanged shape) — running them together is the cross-check that both were updated consistently. If any caller besides the 9 files Step 1 enumerated turns up here, update it the same way.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/compiler/codegen.ex lib/cure/compiler.ex lib/cure/compiler/errors.ex test/cure/compiler/unresolved_import_warning_test.exs
git commit -m "feat(codegen): warn (W088) instead of silently local-falling-back on unresolved imports"
```

---

### Task 8: Preload — baked dep maps, closure-aware selection, ordered source-JIT, docs

**Files:**
- Modify: `lib/cure/stdlib/preload.ex`
- Modify: `docs/STDLIB.md`
- Test: `test/cure/stdlib/preload_closure_test.exs` (create)

**Interfaces:**
- Consumes: `DepGraph.scan/2` (no `known_modules:` needed — the scanned set IS the full stdlib), `order_deps_map/1`, `closure_deps_map/1`, `closure/2`, `toposort/2`.
- Produces:
  - `Preload.module_order_deps() :: %{module() => [module()]}` (baked, `:"Cure.Std.X"` keys)
  - `Preload.module_closure_deps() :: %{module() => [module()]}` (baked)
  - `Preload.closure_modules(kind) :: [module()]` — `stdlib_modules(kind)` expanded over the closure map, sorted. `stdlib_modules/1` itself is UNCHANGED (selection-only; REPL config semantics preserved).

- [ ] **Step 1: Write the failing tests**

```elixir
defmodule Cure.Stdlib.PreloadClosureTest do
  use ExUnit.Case, async: true

  alias Cure.Stdlib.Preload

  test "baked order deps carry Vector -> Nat/Bounded (the only stdlib use edges)" do
    deps = Preload.module_order_deps()

    assert :"Cure.Std.Nat" in Map.fetch!(deps, :"Cure.Std.Vector")
    assert :"Cure.Std.Bounded" in Map.fetch!(deps, :"Cure.Std.Vector")
    assert :"Cure.Std.Nat" in Map.fetch!(deps, :"Cure.Std.Bounded")
  end

  test "baked closure deps carry qualified-call targets (Access -> List/Map/Pair)" do
    deps = Preload.module_closure_deps()
    access = Map.fetch!(deps, :"Cure.Std.Access")

    for m <- [:"Cure.Std.List", :"Cure.Std.Map", :"Cure.Std.Pair"] do
      assert m in access, "expected #{m} in Access closure, got #{inspect(access)}"
    end
  end

  test "closure_modules expands a selection across groups" do
    # Vector is :collections; its use-deps Nat and Bounded are :core.
    expanded = Preload.closure_modules(:collections)

    assert :"Cure.Std.Vector" in expanded
    assert :"Cure.Std.Nat" in expanded
    assert :"Cure.Std.Bounded" in expanded
    # selection itself unchanged:
    refute :"Cure.Std.Nat" in Preload.stdlib_modules(:collections)
  end

  test "closure degrades to plain selection when maps are empty" do
    assert Cure.Compiler.DepGraph.closure(%{}, [:"Cure.Std.List"]) == [:"Cure.Std.List"]
  end

  test "kind API and groups are untouched" do
    assert Preload.known_groups() == [
             :core, :collections, :text, :numeric, :system,
             :concurrency, :option, :test, :network
           ]

    assert Preload.stdlib_modules(:none) == []
  end
end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/preload_closure_test.exs 2>&1 | tail -10`
Expected: FAIL — `module_order_deps/0` undefined.

- [ ] **Step 3: Implement baking in `lib/cure/stdlib/preload.ex`.** After the existing `@std_module_groups` attribute (`preload.ex:109-123`), add (compile-time; the existing `@external_resource` loop already covers every source — do NOT duplicate it):

```elixir
  # Dependency maps baked at compile time via DepGraph (design spec
  # 2026-07-08-auto-import-order §3.3): order-only (`use` edges) and full
  # closure (`use` + qualified-call + auto-prelude). Keys/values are
  # runtime module atoms (:"Cure.Std.X"). Empty when lib/std was absent
  # at compile time (packaged releases) — consumers degrade to plain
  # selection in that case.
  {order_map, closure_map} =
    (fn ->
       # No `known_modules:` needed here: the compile set IS the full
       # stdlib (`@stdlib_sources` already lists every `lib/std/*.cure`
       # file), so `DepGraph.scan/2`'s own AST-derived `modules` map
       # already covers every stdlib module name -- there is nothing
       # out-of-set left for `known_modules` to add. (Contrast a scan
       # over a strict subset, or user files needing to recognize
       # `Std.*` qualified calls as legitimate closure deps -- that's
       # the scenario `known_modules` exists for; it isn't this one.)
       case Cure.Compiler.DepGraph.scan(@stdlib_sources) do
         {:ok, graph} ->
           to_atoms = fn map ->
             Map.new(map, fn {k, vs} ->
               {String.to_atom("Cure." <> k), Enum.map(vs, &String.to_atom("Cure." <> &1))}
             end)
           end

           {to_atoms.(Cure.Compiler.DepGraph.order_deps_map(graph)),
            to_atoms.(Cure.Compiler.DepGraph.closure_deps_map(graph))}

         {:error, _} ->
           {%{}, %{}}
       end
     end).()

  @std_order_deps order_map
  @std_closure_deps closure_map
```

and the public accessors + closure expansion:

```elixir
  @doc "Baked `use`-only dependency map (module atoms). Empty in beams-only deployments."
  @spec module_order_deps() :: %{module() => [module()]}
  def module_order_deps, do: @std_order_deps

  @doc "Baked full closure dependency map (use + qualified calls + auto-prelude)."
  @spec module_closure_deps() :: %{module() => [module()]}
  def module_closure_deps, do: @std_closure_deps

  @doc """
  `stdlib_modules(kind)` expanded to its dependency closure over the baked
  closure map. Selection semantics are unchanged — closure only adds the
  modules the selection needs at runtime. Degrades to the plain selection
  when the baked maps are empty (beams-only deployments).
  """
  @spec closure_modules(kind()) :: [module()]
  def closure_modules(kind) do
    Cure.Compiler.DepGraph.closure(@std_closure_deps, stdlib_modules(kind))
  end
```

- [ ] **Step 4: Route loading + JIT through closure and dependency order.**

(a) In `preload/1` (`preload.ex:261-274`): `load_stdlib(candidate_dirs, kind)` and `compile_missing_from_sources(kind)` operate per-module; change both call chains to use the expanded, ordered list. Replace the internals:

```elixir
  defp load_stdlib([], _kind), do: :ok

  defp load_stdlib(candidate_dirs, kind) do
    Enum.each(ordered_closure_modules(kind), fn module ->
      load_from_candidates(module, candidate_dirs)
    end)
  end
```

and in `compile_missing_from_sources/1` replace `Enum.each(stdlib_modules(kind), ...)` with `Enum.each(ordered_closure_modules(kind), ...)`, adding the shared helper:

```elixir
  # Closure-expanded selection in dependency (use-edge) order. toposort/2
  # is SCC-tolerant, so this always yields a complete deterministic list
  # even if a cycle ever appears in the baked map.
  defp ordered_closure_modules(kind) do
    Cure.Compiler.DepGraph.toposort(@std_order_deps, closure_modules(kind))
  end
```

(b) UNCHANGED, verify by reading after the edit: `stdlib_modules/1`, `known_groups/0`, `module_groups/0`, `validate_kind!/1`, `discover_from_beams/1`, `load_if_present/2`, the `@known_groups` list, and the `__group__` regexes.

- [ ] **Step 5: Docs.** In `docs/STDLIB.md`, in the groups section (~line 42-84), add one paragraph:

```markdown
Groups are **selection tags only** — they say *which* modules a `kind:`
pulls in, never in what order. Compile order and load closure are automatic:
the build derives them from the dependency graph (`Cure.Compiler.DepGraph`
— `use` edges order compilation; `use` + qualified-call edges define the
runtime closure), and `preload(kind:)` expands a selection to everything it
needs at runtime, so e.g. selecting `:collections` also loads the `:core`
modules its members call. See
`docs/superpowers/specs/tooling/2026-07-08-auto-import-order-design.md`.
```

- [ ] **Step 6: Run tests**

```bash
mix test test/cure/stdlib/preload_closure_test.exs 2>&1 | tail -8
mix test test/cure/stdlib 2>&1 | tail -8
```

Expected: PASS (the second run covers existing Preload behavior tests — selection semantics must be untouched).

- [ ] **Step 7: Commit**

```bash
git add lib/cure/stdlib/preload.ex docs/STDLIB.md test/cure/stdlib/preload_closure_test.exs
git commit -m "feat(stdlib): closure-aware preload + dependency-ordered source JIT (baked DepGraph maps)"
```

---

### Task 9: Full verification pass

**Files:** none (verification only; fix regressions where they surface).

- [ ] **Step 1: Full suite, ONE run:**

```bash
mix test 2>&1 | tail -15
```

Expected: 0 failures. Triage any failure to its owning task's code (implementation fixes only; tests from Tasks 1–8 are immutable).

- [ ] **Step 2: Build tasks clean (sequential, never parallel):**

```bash
mix cure.compile_stdlib 2>&1 | tail -3
mix cure.compile_stage1 2>&1 | tail -3
mix cure.check.examples 2>&1 | tail -5
```

Expected: stdlib `0 errors`; stage1 `0 errors` with the Task 4 counts; check.examples exits 0 (same pass/fail set as on the base commit — compare against a `git stash`-free baseline only if it fails).

- [ ] **Step 3: Commit anything the verification pass required, with a message naming the regression it fixed.**

---

## Self-review notes (executed at plan-writing time)

- **Spec coverage:** §3.1 → Tasks 1–2; §3.2 items 1/2/3/4 → Tasks 4/5/6/7; §3.3 → Task 8; §4 table → Tasks 3/6/7/8; §5.1–5.6 → Tasks 1, 1(parity), 6, 7, 8, 9 respectively; §3.4 needs no code (documented in Task 8 Step 5).
- **Known judgment call, resolved:** Task 7's fixture (erl_lint interaction) is settled — the warning rides the lint-error path via `{:beam_lint_error, errors, warnings}`, the green path via prepended warnings; the test asserts the error-path shape because that is the only reachable behavior for a genuinely-unresolved unqualified call. This was independently re-derived and confirmed during a `recursive-skeptical-review` pass (2026-07-08), which also found and fixed: a real cycle-reconstruction bug (`trace_cycle`'s trailing `Enum.uniq/1` silently opened the closed cycle walk the spec's `A -> B -> A` format requires), a factually wrong TOML table in Task 6's fixture (`source_paths` lives under `[project]`, verified against `project.ex:711-767`), an underspecified normalization point for Task 7's special-container 3-tuple wrapping (now pinned to `compile_module/2`'s two `dispatch_container` call sites, not the four container-compiler modules), an inaccurate blanket claim about `compile_and_load/2` threading warnings through `write_beam_forms` (it doesn't call that function at all), and an undercounted test blast-radius (9 pre-existing test files pattern-match `Codegen.compile_module/2`'s bare-tuple shape and must be migrated to the 3-tuple contract). See the task bodies for the fixes in place; this note is not asking a future reviewer to re-derive them.
- **Type consistency:** warning tuple `{:unresolved_import, name, arity, imports, line}` identical in Tasks 3 and 7; `load_emitted/2` defined in Task 6 and consumed in Task 7's test; `closure/2`/`toposort/2` shapes match between Tasks 2 and 8.
- **Determinism:** every map iteration that feeds output goes through `Enum.sort`/sorted paths (scan sorts inputs; kahn sorts ready set; Tarjan visits nodes/neighbors sorted; SCC members emitted sorted; baked maps sort values).
- **AMENDMENT 2026-07-08 (mid-execution, operator-briefing-driven):** the cycle policy changed from hard-error (E086) to SCC-condensation-with-warning (W086) after Task 1's first execution attempt discovered a genuine `use` cycle (`Compiler.Kernel.Core.Environment ↔ Exception`, commit `5ef6d80`, landed after the spec's ground-truth experiments). The operator's pre-run briefing explicitly required "a defined behavior (compile an SCC together / arbitrary intra-SCC order), not a crash" for cycles. Spec §2 fact 6 and §3.1 were amended in the same commit as this plan revision; `order/1` is now `{:ok, paths, cycles}` and never fails, `toposort/2` returns a plain list, and Tasks 1/2/3/4/5/6/8 were updated consistently. If any residual text in this plan still implies cycles are fatal, the amended spec §3.1 governs.
