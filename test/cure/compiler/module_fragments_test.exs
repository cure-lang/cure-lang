defmodule Cure.Compiler.ModuleFragmentsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.ModuleIndex
  alias Cure.Compiler.ModuleManifest
  alias Cure.Compiler.ModulePipeline.Expansion
  alias Cure.Compiler.DepGraph

  @moduletag :tmp_dir

  test "marked same-module fragments aggregate into one manifest entry", %{tmp_dir: dir} do
    first = write!(dir, "fragment_a.cure", "# cure:fragment\nmod Fragmented\n  fn first() -> Int = 1\n")
    second = write!(dir, "fragment_b.cure", "# cure:fragment\nmod Fragmented\n  fn second() -> Int = 2\n")

    assert {:ok, manifest} = ModuleManifest.build([second, first])
    assert {:ok, entry} = ModuleManifest.fetch(manifest, "Fragmented")
    assert entry.source_paths == Enum.sort([first, second])
    assert manifest.paths[first] == {"root", "Fragmented"}
    assert manifest.paths[second] == {"root", "Fragmented"}
  end

  test "unmarked duplicate module providers remain an error", %{tmp_dir: dir} do
    first = write!(dir, "duplicate_a.cure", "mod Duplicate\n  fn first() -> Int = 1\n")
    second = write!(dir, "duplicate_b.cure", "mod Duplicate\n  fn second() -> Int = 2\n")

    assert {:error, {:duplicate_module_identity, %{identity: {"root", "Duplicate"}, providers: providers}}} =
             ModuleManifest.build([first, second])

    assert providers == Enum.sort([first, second])
  end

  test "marked fragments are one canonical module-index node", %{tmp_dir: dir} do
    first = write!(dir, "index_fragment_a.cure", "# cure:fragment\nmod Indexed\n  fn first() -> Int = 1\n")
    second = write!(dir, "index_fragment_b.cure", "# cure:fragment\nmod Indexed\n  fn second() -> Int = 2\n")

    assert {:ok, index} = ModuleIndex.build([first, second])
    assert {:ok, entry} = ModuleIndex.fetch(index, "Indexed")
    assert entry.source_paths == Enum.sort([first, second])
    assert index.paths[first] == "Indexed"
    assert index.paths[second] == "Indexed"
  end

  test "unmarked duplicate module index providers remain an error", %{tmp_dir: dir} do
    first = write!(dir, "index_duplicate_a.cure", "mod IndexedDuplicate\n")
    second = write!(dir, "index_duplicate_b.cure", "mod IndexedDuplicate\n")

    assert {:error, {:duplicate_module, "IndexedDuplicate", paths}} =
             ModuleIndex.build([first, second])

    assert paths == Enum.sort([first, second])
  end

  test "expansion elaborates marked fragments as one module body", %{tmp_dir: dir} do
    first = write!(dir, "expansion_fragment_a.cure", "# cure:fragment\nmod Expanded\n  fn first() -> Int = 1\n")
    second = write!(dir, "expansion_fragment_b.cure", "# cure:fragment\nmod Expanded\n  fn second() -> Int = 2\n")

    assert {:ok, manifest} = ModuleManifest.build([first, second])
    assert {:ok, expansion} = Expansion.run(manifest, prelude_modules: [])

    skeleton = expansion.skeletons[{"root", "Expanded"}]

    assert MapSet.new(Map.keys(skeleton.declarations)) ==
             MapSet.new([{:value, "first"}, {:value, "second"}])
  end

  test "expansion finds a module after leading decorators in a fragment", %{tmp_dir: dir} do
    first =
      write!(
        dir,
        "decorated_fragment_a.cure",
        "# cure:fragment\n@group(:core)\nmod Decorated\n  fn first() -> Int = 1\n"
      )

    second =
      write!(
        dir,
        "decorated_fragment_b.cure",
        "# cure:fragment\n@group(:core)\nmod Decorated\n  fn second() -> Int = 2\n"
      )

    assert {:ok, manifest} = ModuleManifest.build([first, second])
    assert {:ok, expansion} = Expansion.run(manifest, prelude_modules: [])

    skeleton = expansion.skeletons[{"root", "Decorated"}]

    assert Cure.Elab.Program.module_atom(expansion.asts[{"root", "Decorated"}]) ==
             :"Cure.Decorated"

    assert MapSet.new(Map.keys(skeleton.declarations)) ==
             MapSet.new([{:value, "first"}, {:value, "second"}])
  end

  test "dependency graph treats marked fragments as one canonical node", %{tmp_dir: dir} do
    first = write!(dir, "graph_fragment_a.cure", "# cure:fragment\nmod GraphFragmented\n  fn first() -> Int = 1\n")
    second = write!(dir, "graph_fragment_b.cure", "# cure:fragment\nmod GraphFragmented\n  fn second() -> Int = 2\n")

    assert {:ok, graph} = DepGraph.scan([second, first])
    assert graph.modules["GraphFragmented"] == Enum.min([first, second])
    assert graph.module_index.entries["GraphFragmented"].source_paths == Enum.sort([first, second])
    assert DepGraph.order_deps_map(graph) == %{"GraphFragmented" => []}
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
