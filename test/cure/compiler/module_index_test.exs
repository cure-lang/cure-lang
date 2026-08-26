defmodule Cure.Compiler.ModuleIndexTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.ModuleIndex

  @moduletag :tmp_dir

  test "declared identities and dependencies are independent of filenames and input order", %{tmp_dir: dir} do
    provider = write!(dir, "zz_provider.cure", "mod Canon.Provider\n  fn value() -> Int = 1\n")

    consumer =
      write!(
        dir,
        "aa_consumer.cure",
        "mod Canon.Consumer\n  fn value() -> Int = Canon.Provider.value()\n"
      )

    assert {:ok, left} = ModuleIndex.build([consumer, provider])
    assert {:ok, right} = ModuleIndex.build([provider, consumer])
    assert left.entries == right.entries
    assert ModuleIndex.dependency_order(left) == ["Canon.Provider", "Canon.Consumer"]

    assert [%{kind: :qualified_reference, target: "Canon.Provider"}] =
             ModuleIndex.edges(left, "Canon.Consumer")
  end

  test "missing dependencies fail before body elaboration with their source edge", %{tmp_dir: dir} do
    consumer =
      write!(dir, "consumer.cure", "mod Canon.Consumer\n  fn value() -> Int = Canon.Missing.value()\n")

    assert {:error, {:module_dependency_missing, edge}} = ModuleIndex.build([consumer])
    assert edge.source_module == "Canon.Consumer"
    assert edge.target == "Canon.Missing"
    assert edge.kind == :qualified_reference
    assert edge.source_path == consumer
  end

  test "duplicate canonical identities report both paths", %{tmp_dir: dir} do
    first = write!(dir, "first.cure", "mod Canon.Duplicate\n")
    second = write!(dir, "second.cure", "mod Canon.Duplicate\n")

    assert {:error, {:duplicate_module, "Canon.Duplicate", paths}} =
             ModuleIndex.build([second, first])

    assert paths == Enum.sort([first, second])
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
