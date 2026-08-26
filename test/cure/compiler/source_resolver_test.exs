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

  @tag :tmp_dir
  test "uses the compile universe's canonical index without rescanning source roots", %{tmp_dir: dir} do
    file = Path.join(dir, "filename_deliberately_disagrees.cure")
    File.write!(file, "mod Canon.Indexed\n  fn go() -> Int = 1\nend\n")
    assert {:ok, index} = Cure.Compiler.ModuleIndex.build([file])

    previous_roots = Process.get(:cure_source_roots)
    previous_index = Process.get(:cure_module_index)
    Process.put(:cure_source_roots, [])
    Process.put(:cure_module_index, index)

    try do
      assert {:ok, ^file} = SourceResolver.module_path("Canon.Indexed")
    after
      restore(:cure_source_roots, previous_roots)
      restore(:cure_module_index, previous_index)
    end
  end

  defp restore(key, nil), do: Process.delete(key)
  defp restore(key, value), do: Process.put(key, value)
end
