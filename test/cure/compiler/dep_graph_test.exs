defmodule Cure.Compiler.DepGraphTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.DepGraph

  @moduletag :tmp_dir

  defp write!(dir, name, contents) do
    path = Path.join(dir, name)
    File.write!(path, contents)
    path
  end

  describe "scan/2 + order_deps_map/1 + components/3" do
    test "indexes a declaration-only source under the implicit Main module", %{tmp_dir: dir} do
      path = write!(dir, "main.cure", "fn answer() -> Int = 42\n")

      assert {:ok, graph} = DepGraph.scan([path])
      assert graph.modules["Main"] == path
      assert graph.module_index.entries["Main"].provided_modules == ["Main"]
      assert DepGraph.order_deps_map(graph) == %{"Main" => []}
    end

    test "orders use-dependencies before their dependents", %{tmp_dir: dir} do
      a = write!(dir, "zz_lib.cure", "mod LibA\n  fn ping() -> Int = 41\n")
      b = write!(dir, "aa_user.cure", "mod UserB\n  use LibA\n  fn start() -> Int = ping()\n")

      {:ok, graph} = DepGraph.scan([b, a])
      deps = DepGraph.order_deps_map(graph)

      assert DepGraph.toposort(deps, Map.keys(deps)) == ["LibA", "UserB"]
      assert graph.module_index.entries["LibA"].source_path == a
      assert graph.module_index.entries["UserB"].source_path == b
    end

    test "bulk compilation uses the graph when filenames oppose dependency order", %{tmp_dir: dir} do
      output = Path.join(dir, "ebin")
      provider = write!(dir, "zz_provider.cure", "mod Bulk.Provider\n  fn value() -> Int = 41\n")

      consumer =
        write!(
          dir,
          "aa_consumer.cure",
          "mod Bulk.Consumer\n  use Bulk.Provider\n  fn run() -> Int = value() + 1\n"
        )

      assert {:ok, result} =
               Cure.Compiler.compile_files([consumer, provider],
                 output_dir: output,
                 emit_events: false
               )

      assert Enum.map(result.compiled, &elem(&1, 0)) == [provider, consumer]
      assert apply(:"Cure.Bulk.Consumer", :run, []) == 42
    after
      :code.purge(:"Cure.Bulk.Consumer")
      :code.delete(:"Cure.Bulk.Consumer")
      :code.purge(:"Cure.Bulk.Provider")
      :code.delete(:"Cure.Bulk.Provider")
    end

    test "bulk drivers reject a legacy external graph plan", %{tmp_dir: dir} do
      output = Path.join(dir, "planned_ebin")
      provider = write!(dir, "zz_planned.cure", "mod Planned.Provider\n  fn value() -> Int = 8\n")

      consumer =
        write!(
          dir,
          "aa_planned.cure",
          "mod Planned.Consumer\n  use Planned.Provider\n  fn run() -> Int = value()\n"
        )

      assert {:error, {:invalid_compile_files_options, [:plan]}} =
               Cure.Compiler.compile_files([consumer, provider],
                 plan: %{retired: true},
                 output_dir: output,
                 emit_events: false
               )
    after
      :code.purge(:"Cure.Planned.Consumer")
      :code.delete(:"Cure.Planned.Consumer")
      :code.purge(:"Cure.Planned.Provider")
      :code.delete(:"Cure.Planned.Provider")
    end

    test "deterministic: shuffled input, identical output", %{tmp_dir: dir} do
      paths =
        for n <- ["m1", "m2", "m3", "m4"] do
          write!(dir, n <> ".cure", "mod #{String.upcase(n)}\n  fn f() -> Int = 1\n")
        end

      {:ok, g1} = DepGraph.scan(paths)
      {:ok, g2} = DepGraph.scan(Enum.reverse(paths))
      deps1 = DepGraph.order_deps_map(g1)
      deps2 = DepGraph.order_deps_map(g2)

      assert deps1 == deps2
      assert DepGraph.toposort(deps1, Map.keys(deps1)) == DepGraph.toposort(deps2, Map.keys(deps2))
      assert DepGraph.toposort(deps1, Map.keys(deps1)) == ["M1", "M2", "M3", "M4"]
    end

    test "cycle: order_deps_map + components groups the SCC together, dependents after", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod CycA\n  use CycB\n  fn f() -> Int = 1\n")
      b = write!(dir, "b.cure", "mod CycB\n  use CycA\n  fn g() -> Int = 2\n")
      c = write!(dir, "c.cure", "mod Down\n  use CycA\n  fn h() -> Int = 3\n")

      {:ok, graph} = DepGraph.scan([a, b, c])
      deps = DepGraph.order_deps_map(graph)

      # SCC policy (spec §3.1 as amended): no crash — members are grouped
      # together (alphabetical within the group), dependents still AFTER
      # the SCC. The closed-walk cycle diagnostic with file/line hops is a
      # separate contract owned by `Cure.Compiler.Artifacts.Sweep` — see
      # `canonical_artifact_sweep_test.exs`.
      assert DepGraph.components(deps, Map.keys(deps)) == [["CycA", "CycB"], ["Down"]]
    end

    test "duplicate module name across files is an error", %{tmp_dir: dir} do
      a = write!(dir, "one.cure", "mod Dup\n  fn f() -> Int = 1\n")
      b = write!(dir, "two.cure", "mod Dup\n  fn g() -> Int = 2\n")

      assert {:error, {:duplicate_module, "Dup", paths}} = DepGraph.scan([a, b])
      assert Enum.sort(paths) == Enum.sort([a, b])
    end

    test "real graph failures exercise every dependency-graph diagnostic producer", %{tmp_dir: dir} do
      duplicate_a = write!(dir, "duplicate_a.cure", "mod Repeated\n  fn left() -> Int = 1\n")
      duplicate_b = write!(dir, "duplicate_b.cure", "mod Repeated\n  fn right() -> Int = 2\n")

      assert {:error, duplicate_reason} = DepGraph.scan([duplicate_a, duplicate_b])

      {duplicate_diagnostic, _registry} =
        Cure.Compiler.Errors.to_diagnostic(duplicate_reason, duplicate_a, File.read!(duplicate_a))

      assert duplicate_diagnostic.code == "E087"

      # The closed-walk `:import_cycle` payload is produced by the live
      # canonical pipeline (`Cure.Compiler.Artifacts.Sweep`), not by this
      # module, so exercise it through the real `sweep/1` entry point (its
      # own dedicated subdirectory keeps it isolated from the duplicate-module
      # fixture above).
      cycle_root = Path.join(dir, "cycle_src")
      File.mkdir_p!(cycle_root)
      cycle_a = write!(cycle_root, "cycle_a.cure", "mod CycleA\n  use CycleB\n  fn left() -> Int = 1\n")
      _cycle_b = write!(cycle_root, "cycle_b.cure", "mod CycleB\n  use CycleA\n  fn right() -> Int = 2\n")

      assert {:ok, result} =
               Cure.Compiler.Artifacts.sweep(
                 module_pipeline: :canonical,
                 package: "cycle_fixture",
                 kind: :project,
                 source_roots: [cycle_root],
                 output_dir: Path.join(dir, "cycle_ebin"),
                 repair: true
               )

      assert [hops] = result.cycles

      {cycle_diagnostic, _registry} =
        Cure.Compiler.Errors.to_diagnostic({:import_cycle, hops}, cycle_a, File.read!(cycle_a))

      assert cycle_diagnostic.code == "W086"

      assert :ok =
               Cure.Diagnostic.Registry.validate_exercised_producer_fixtures([:duplicate_module, :import_cycle],
                 only_producers: [:dependency_graph]
               )
    end

    test "out-of-set use targets impose no ordering", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod OnlyOne\n  use Std.List\n  use NotInSet\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([a])
      assert DepGraph.order_deps_map(graph) == %{"OnlyOne" => []}

      assert graph.nodes[a].order_deps == [] or
               Enum.all?(graph.nodes[a].order_deps, &(&1.target in ["Std.List", "NotInSet"]))
    end

    test "strict bulk scans reject an unavailable dependency before body elaboration", %{tmp_dir: dir} do
      source =
        write!(
          dir,
          "missing.cure",
          "mod MissingConsumer\n  fn value() -> Int = Definitely.Missing.value()\n"
        )

      assert {:error, {:module_dependency_missing, edge}} =
               DepGraph.scan([source], validate_dependencies: true)

      assert edge.kind == :qualified_reference
      assert edge.source_module == "MissingConsumer"
      assert edge.target == "Definitely.Missing"
      assert edge.line == 2
    end

    test "strict scans recognize generated modules provided by the same source", %{tmp_dir: dir} do
      source =
        write!(
          dir,
          "generated_provider.cure",
          """
          mod GeneratedProvider
            lift module Cure.Generated.Worker
              fn value() -> Int = 1
            fn run() -> Int = Cure.Generated.Worker.value()
          """
        )

      assert {:ok, graph} = DepGraph.scan([source], validate_dependencies: true)
      assert "Cure.Generated.Worker" in graph.module_index.entries["GeneratedProvider"].provided_modules

      assert {:ok, owner_entry} =
               Cure.Compiler.ModuleIndex.fetch(graph.module_index, "Cure.Generated.Worker")

      assert owner_entry.module_name == "GeneratedProvider"
      assert owner_entry.source_path == source
      assert graph.modules["Cure.Generated.Worker"] == source
    end

    test "blank placeholders and parse failures are isolated nodes", %{tmp_dir: dir} do
      blank = write!(dir, "a_blank.cure", "   \n")
      bad = write!(dir, "b_bad.cure", "mod ((((\n")
      good = write!(dir, "c_good.cure", "mod Good\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([blank, bad, good])
      assert graph.nodes[blank].blank?
      assert graph.nodes[bad].parse_error != nil

      # Nodes without a resolved module name (blank) are excluded from the
      # module-name-keyed maps entirely; a recoverable parse error still
      # contributes whatever module name the tolerant fixity harvest found
      # (here, none -- `mod ((((` recovers no real name).
      assert DepGraph.order_deps_map(graph) == %{"(" => [], "Good" => []}
    end

    test "self-use is ignored", %{tmp_dir: dir} do
      a = write!(dir, "selfy.cure", "mod Selfy\n  use Selfy\n  fn f() -> Int = 1\n")
      {:ok, graph} = DepGraph.scan([a])
      assert DepGraph.order_deps_map(graph) == %{"Selfy" => []}
    end

    test "generic lifted modules are discovered without OTP container kinds", %{tmp_dir: dir} do
      worker = write!(dir, "worker.cure", "lift module Cure.Worker\n  behaviour custom\n")
      root = write!(dir, "root.cure", "mod Cure.Root\n  use Cure.Worker\n")

      {:ok, graph} = DepGraph.scan([root, worker])
      assert graph.modules["Cure.Worker"] == worker
      assert graph.modules["Cure.Root"] == root
    end

    # This test originally asserted the ordering property against the real
    # stage1 Lean-bootstrap tree (lib/compiler/**), whose Environment <->
    # Exception `use` cycle motivated the SCC policy. That tree was removed
    # (operator directive, reverts of 5ef6d80..8f249d9), so the same
    # property now runs against a fixture replicating its shape: a kernel
    # mesh with a genuine 2-cycle and downstream dependents.
    test "mesh with a cycle: every cross-SCC use edge is respected, intra-SCC exempt",
         %{tmp_dir: dir} do
      files = [
        write!(dir, "name.cure", "mod MName\n  fn f() -> Int = 1\n"),
        write!(dir, "expr.cure", "mod MExpr\n  use MName\n  fn f() -> Int = 1\n"),
        write!(dir, "env.cure", "mod MEnv\n  use MName\n  use MExpr\n  use MExc\n  fn f() -> Int = 1\n"),
        write!(dir, "exc.cure", "mod MExc\n  use MName\n  use MEnv\n  fn f() -> Int = 1\n"),
        write!(dir, "tc.cure", "mod MTc\n  use MEnv\n  use MExc\n  use MExpr\n  fn f() -> Int = 1\n")
      ]

      {:ok, graph} = DepGraph.scan(files)
      deps = DepGraph.order_deps_map(graph)
      order = DepGraph.toposort(deps, Map.keys(deps))
      components = DepGraph.components(deps, Map.keys(deps))
      index = order |> Enum.with_index() |> Map.new()

      scc_of =
        for {members, i} <- Enum.with_index(components), m <- members, into: %{}, do: {m, i}

      assert Enum.any?(components, fn members -> "MEnv" in members and "MExc" in members end),
             "expected the MEnv<->MExc cycle to be reported, got: #{inspect(components)}"

      for {source_module, targets} <- deps,
          target <- targets,
          # intra-SCC edges are exempt (no valid topological constraint exists)
          scc_of[source_module] == nil or scc_of[source_module] != scc_of[target] do
        assert index[target] < index[source_module],
               "#{target} must precede #{source_module}"
      end
    end
  end

  describe "components/3" do
    test "returns deterministic dependency-first singleton components" do
      deps = %{
        "App" => ["Service", "Config"],
        "Service" => ["Config"],
        "Config" => [],
        "Unused" => []
      }

      expected = [["Config"], ["Unused"], ["Service"], ["App"]]

      assert DepGraph.components(deps, ["Unused", "Service", "App", "Config"]) == expected
      assert DepGraph.components(deps, ["Config", "App", "Unused", "Service"]) == expected
    end

    test "keeps a cycle together before its dependents" do
      deps = %{
        "A" => ["B"],
        "B" => ["A"],
        "Consumer" => ["B"]
      }

      assert DepGraph.components(deps, ["Consumer", "B", "A"]) == [
               ["A", "B"],
               ["Consumer"]
             ]
    end

    test "prefers ready priority components without violating dependencies" do
      deps = %{
        "Prelude" => [],
        "Independent" => [],
        "Consumer" => ["Prelude"]
      }

      assert DepGraph.components(deps, Map.keys(deps), ["Prelude"]) == [
               ["Prelude"],
               ["Independent"],
               ["Consumer"]
             ]
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

  describe "priority-aware toposort/3" do
    test "sorts an ambient prelude provider before an implicit consumer", %{tmp_dir: dir} do
      provider = write!(dir, "z_provider.cure", "@prelude\nmod LiteralProvider\n  fn make() -> Int = 1\n")
      consumer = write!(dir, "a_consumer.cure", "mod Consumer\n  fn value() -> Int = 2\n")

      {:ok, graph} = DepGraph.scan([consumer, provider])
      deps = DepGraph.order_deps_map(graph)

      assert deps["Consumer"] == []
      assert DepGraph.toposort(deps, Map.keys(deps), ["LiteralProvider"]) == ["LiteralProvider", "Consumer"]
    end

    test "does not add a prelude back-edge into its bootstrap dependencies", %{tmp_dir: dir} do
      dependency = write!(dir, "z_dependency.cure", "mod Dependency\n  fn base() -> Int = 1\n")

      provider =
        write!(
          dir,
          "a_provider.cure",
          "@prelude\nmod Provider\n  use Dependency\n  fn make() -> Int = base()\n"
        )

      consumer = write!(dir, "b_consumer.cure", "mod Consumer\n  fn value() -> Int = 2\n")

      {:ok, graph} = DepGraph.scan([consumer, provider, dependency])
      deps = DepGraph.order_deps_map(graph)

      assert deps["Provider"] == ["Dependency"]
      refute "Provider" in deps["Dependency"]

      assert DepGraph.toposort(deps, Map.keys(deps), ["Provider"]) == [
               "Dependency",
               "Provider",
               "Consumer"
             ]
    end
  end

  describe "closure edges" do
    test "qualified-call targets become closure deps when in the known universe", %{tmp_dir: dir} do
      lib = write!(dir, "libm.cure", "mod LibM\n  fn get(x: Int) -> Int = x\n")

      user =
        write!(dir, "userq.cure", "mod UserQ\n\n  fn f(x: Int) -> Int = LibM.get(x)\n")

      {:ok, graph} = DepGraph.scan([lib, user])

      assert "LibM" in graph.nodes[user].closure_deps
      # qualified call is NOT an order edge (spec fact 2)
      assert graph.nodes[user].order_deps == []

      assert [%{kind: :qualified_reference, target: "LibM", line: 3}] =
               graph.module_index.entries["UserQ"].direct_edges
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

    test "marked prelude providers are closure dependencies", %{tmp_dir: dir} do
      plain = write!(dir, "p.cure", "mod Plain\n  fn f() -> Int = 1\n")
      shadow = write!(dir, "s.cure", "mod Shadow\n  type Bool = TT | FF\n  fn f() -> Int = 1\n")
      bool = write!(dir, "bool.cure", "@prelude\nmod Std.Bool\n  type Bool = False | True\nend\n")
      nat = write!(dir, "nat.cure", "@prelude\nmod Std.Nat\n  type Nat = Z | S(Nat)\nend\n")

      {:ok, graph} = DepGraph.scan([plain, shadow, bool, nat])

      assert "Std.Bool" in graph.nodes[plain].closure_deps
      assert "Std.Nat" in graph.nodes[plain].closure_deps
      assert "Std.Bool" in graph.nodes[shadow].closure_deps
      assert "Std.Nat" in graph.nodes[shadow].closure_deps
      refute "Std.Bool" in graph.nodes[bool].closure_deps
      refute "Std.Nat" in graph.nodes[nat].closure_deps
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
end
