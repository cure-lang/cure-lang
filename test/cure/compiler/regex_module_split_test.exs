defmodule Cure.Compiler.RegexModuleSplitTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleManifest
  alias Cure.Compiler.ModuleIndex
  alias Cure.Elab.Program
  alias Cure.Compiler.ModulePipeline
  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Name

  @moduletag :tmp_dir

  test "the public façade re-exports Core and Runtime through classic elaboration" do
    source = """
    mod RegexFacadeSurface
      use Std.Regex

      fn build() -> Pattern(CharC) = PatternPredicate(fn(_) -> true)
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "regex_facade_surface.cure")
  end

  test "the embedded package export surface is read from its Cure.toml manifest" do
    assert {:ok, exports} = Cure.Stdlib.Packages.package_exports("lib/std_deps/regex")
    assert exports == %{"cure_regex" => ["Std.Regex"]}
  end

  test "package export authority follows the selected package manifest", %{tmp_dir: dir} do
    File.write!(
      Path.join(dir, "Cure.toml"),
      """
      [project]
      name = "fixture_regex"

      [exports]
      modules = ["Fixture.Public", "Fixture.Public"]
      """
    )

    assert {:ok, exports} = Cure.Stdlib.Packages.package_exports(dir)
    assert exports == %{"fixture_regex" => ["Fixture.Public"]}
  end

  test "the Regex layers have one-way manifest ownership" do
    paths =
      Path.wildcard("lib/std_deps/regex/regex*.cure")
      |> Enum.map(&Path.expand/1)

    assert {:ok, stdlib_index} =
             ModuleIndex.build(Path.wildcard("lib/std/**/*.cure"), validate_dependencies: false)

    assert {:ok, manifest} =
             ModuleManifest.build(paths,
               package: "cure_regex",
               known_modules: ["Std.Builtin" | ModuleIndex.module_names(stdlib_index)]
             )

    assert manifest.package == "cure_regex"

    dependencies = fn module_name ->
      manifest
      |> ModuleManifest.dependencies(module_name)
      |> Enum.map(&elem(&1.target, 1))
      |> MapSet.new()
    end

    assert "Std.Regex.Core" in dependencies.("Std.Regex.Runtime")
    assert "Std.Regex.Runtime" in dependencies.("Std.Regex.Proof")
    assert "Std.Regex.Proof" in dependencies.("Std.Regex")
    assert "Std.Regex.Core" in dependencies.("Std.Regex.Language")
    assert "Std.Regex.Runtime" in dependencies.("Std.Regex.Language")
    assert "Std.Regex.Proof" in dependencies.("Std.Regex.Language")

    refute "Std.Regex.Proof" in dependencies.("Std.Regex.Core")
    refute "Std.Regex" in dependencies.("Std.Regex.Core")
    refute "Std.Regex" in dependencies.("Std.Regex.Proof")
  end

  test "Regex manifest identities are independent of source ordering" do
    paths =
      Path.wildcard("lib/std_deps/regex/regex*.cure")
      |> Enum.map(&Path.expand/1)
      |> Enum.sort()

    assert {:ok, stdlib_index} =
             ModuleIndex.build(Path.wildcard("lib/std/**/*.cure"), validate_dependencies: false)

    known_modules = ["Std.Builtin" | ModuleIndex.module_names(stdlib_index)]

    build_entries = fn ordered ->
      assert {:ok, manifest} =
               ModuleManifest.build(ordered,
                 package: "cure_regex",
                 known_modules: known_modules
               )

      manifest.entries
    end

    baseline = build_entries.(paths)

    [Enum.reverse(paths), Enum.drop(paths, 3) ++ Enum.take(paths, 3)]
    |> Enum.each(fn ordered ->
      assert build_entries.(ordered) == baseline
    end)
  end

  test "the complete embedded Regex package has an acyclic use graph" do
    paths =
      Path.wildcard("lib/std_deps/regex/regex*.cure")
      |> Enum.map(&Path.expand/1)

    assert {:ok, graph} = Cure.Compiler.DepGraph.scan(paths, validate_dependencies: false)

    components =
      graph
      |> Cure.Compiler.DepGraph.order_deps_map()
      |> Cure.Compiler.DepGraph.components(Map.keys(graph.modules))

    assert Enum.all?(components, &(length(&1) == 1)),
           "embedded Regex package must be a DAG, got SCCs: #{inspect(components)}"
  end

  test "the complete Regex dependency closure is acyclic, including qualified calls" do
    paths =
      Path.wildcard("lib/std_deps/regex/regex*.cure")
      |> Enum.map(&Path.expand/1)

    assert {:ok, graph} = Cure.Compiler.DepGraph.scan(paths, validate_dependencies: false)

    components =
      graph
      |> Cure.Compiler.DepGraph.closure_deps_map()
      |> Cure.Compiler.DepGraph.components(Map.keys(graph.modules))

    assert Enum.all?(components, &(length(&1) == 1)),
           "embedded Regex closure must be a DAG, got SCCs: #{inspect(components)}"
  end

  test "Regex follows the acyclic Char-Literal-String text boundary" do
    runtime = File.read!(Path.expand("lib/std_deps/regex/regex_runtime.cure"))

    # Unicode case mappings belong to the Char floor and return List(Char).
    # Regex must not route them through the nominal String wrapper, which would
    # recreate the old Char -> String edge that the text-layer migration removed.
    assert runtime =~ "Std.Char.lowercased_characters("
    refute runtime =~ "Std.Char.lowercased("
    refute runtime =~ "Std.String.characters(Std.Char.lowercased("

    paths =
      (["lib/std/char.cure", "lib/std/literal.cure", "lib/std/string.cure"] ++
         Path.wildcard("lib/std_deps/regex/regex*.cure"))
      |> Enum.map(&Path.expand/1)

    assert {:ok, graph} = Cure.Compiler.DepGraph.scan(paths, validate_dependencies: false)

    direct_targets = fn module_name, kind ->
      graph.module_index.entries[module_name].direct_edges
      |> Enum.filter(&(&1.kind == kind))
      |> Enum.map(& &1.target)
      |> MapSet.new()
    end

    char_imports = direct_targets.("Std.Char", :use_import)
    literal_imports = direct_targets.("Std.Literal", :use_import)
    string_imports = direct_targets.("Std.String", :use_import)

    refute MapSet.member?(char_imports, "Std.String")
    refute MapSet.member?(char_imports, "Std.Literal")
    assert MapSet.member?(literal_imports, "Std.Char")
    assert MapSet.member?(string_imports, "Std.Char")
    assert MapSet.member?(string_imports, "Std.Literal")
  end

  test "canonical visibility follows transitive public reexports", %{tmp_dir: dir} do
    base = Path.join(dir, "base.cure")
    middle = Path.join(dir, "middle.cure")
    facade = Path.join(dir, "facade.cure")

    File.write!(base, "mod Surface.Base\n  fn value() -> Int = 41\n")

    File.write!(
      middle,
      "mod Surface.Middle\n  public use Surface.Base\n"
    )

    File.write!(
      facade,
      "mod Surface.Facade\n  public use Surface.Middle\n  fn result() -> Int = value() + 1\n"
    )

    assert {:ok, _result} =
             ModulePipeline.check([facade, middle, base],
               module_pipeline: :canonical,
               package: "surface",
               source_roots: [dir]
             )
  end

  test "canonical qualified compatibility roots preserve public reexports", %{tmp_dir: dir} do
    base = Path.join(dir, "base.cure")
    facade = Path.join(dir, "facade.cure")
    consumer = Path.join(dir, "consumer.cure")

    File.write!(base, "mod Surface.Base\n  fn value() -> Int = 41\n")
    File.write!(facade, "mod Surface.Facade\n  public use Surface.Base\n")

    File.write!(
      consumer,
      "mod Surface.Consumer\n  use Surface.Facade\n  fn result() -> Int = Surface.Facade.value()\n"
    )

    assert {:ok, _result} =
             ModulePipeline.check([consumer, facade, base],
               module_pipeline: :canonical,
               package: "surface",
               source_roots: [dir]
             )
  end

  test "the compatibility inventory resolves to one canonical owner" do
    source = """
    mod RegexFacadeInventory
      use Std.Regex
      fn keep({shape: ShapeCode}, value: Pattern(shape)) -> Pattern(shape) = value
    end
    """

    assert {:ok, env} = Program.elaborate(source, file: "regex_facade_inventory.cure")

    # This is the reviewed public inventory for the façade. The test deliberately
    # checks canonical environment entries rather than merely parsing names from
    # the source file, so copying a second nominal family cannot pass unnoticed.
    public_families = [
      {:Pattern, "Std.Regex.Core"},
      {:ShapeCode, "Std.Regex.Core"},
      {:EvidenceInstruction, "Std.Regex.Core.Evidence"},
      {:NewlinePolicy, "Std.Regex.Core.Newline"},
      {:InitialPosition, "Std.Regex.Core.Initial"},
      {:Evidence, "Std.Regex.Core"},
      {:Encodes, "Std.Regex.Core"},
      {:EncodesMany, "Std.Regex.Core"},
      {:EncodingExtraction, "Std.Regex.Core"},
      {:ManyEncodingExtraction, "Std.Regex.Core"},
      {:ThreadState, "Std.Regex.Core"},
      {:MachineState, "Std.Regex.Core"},
      {:PatternMachine, "Std.Regex.Core"}
    ]

    Enum.each(public_families, fn {name, owner} ->
      facade_key = String.to_atom("Std.Regex##{name}")
      core_key = String.to_atom("#{owner}##{name}")
      assert Inductive.get_family(env, facade_key) == nil
      family = Inductive.get_family(env, core_key)
      assert family.name == core_key
    end)

    public_functions = ~w(parse_pattern_full parse_program_full parse_full parse_prefix search scan split replace)

    Enum.each(public_functions, fn name ->
      key = String.to_atom("Std.Regex##{name}")
      assert %{name: ^key} = Env.get_def(env, key)
      assert Name.owner(key) == "Std.Regex"
    end)

    # Constructors are also part of the inventory and must resolve through the
    # Core owner without leaving a façade-owned duplicate.
    assert Inductive.get_ctor(env, :"Std.Regex#PatternEmpty") == nil
    assert Inductive.get_ctor(env, :"Std.Regex.Core#PatternEmpty").name == :"Std.Regex.Core#PatternEmpty"
    assert Inductive.get_ctor(env, :"Std.Regex#PatternPredicate") == nil
    assert Inductive.get_ctor(env, :"Std.Regex.Core#PatternPredicate").name == :"Std.Regex.Core#PatternPredicate"

    # The inventory above is intentionally readable. This second assertion is
    # exhaustive for all public Core/Runtime families visible through the
    # façade: every base name has one canonical owner and never a façade-owned
    # nominal duplicate.
    canonical_families =
      env.families
      |> Map.keys()
      |> Enum.filter(&(Name.owner(&1) in ["Std.Regex.Core", "Std.Regex.Core.Evidence", "Std.Regex.Core.Newline", "Std.Regex.Core.Initial", "Std.Regex.Runtime"]))

    Enum.each(canonical_families, fn key ->
      refute Inductive.get_family(env, String.to_atom("Std.Regex##{Name.base(key)}"))
      assert Name.owner(key) in ["Std.Regex.Core", "Std.Regex.Core.Evidence", "Std.Regex.Core.Newline", "Std.Regex.Core.Initial", "Std.Regex.Runtime"]
    end)
  end

  test "qualified façade type families resolve through canonical public reexports" do
    source = """
    mod RegexQualifiedFacadeInventory
      use Std.Regex
      fn keep({shape: Std.Regex.ShapeCode}, value: Std.Regex.Pattern(shape)) -> Std.Regex.Pattern(shape) = value
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "regex_qualified_facade_inventory.cure")
  end
end
