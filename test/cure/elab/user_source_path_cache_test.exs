defmodule Cure.Elab.UserSourcePathCacheTest do
  @moduledoc """
  `Program.user_source_path/1` resolves a `use` import of a project module by
  declared name. It used to glob, lex and parse every `.cure` file under the
  source roots on every lookup. It now answers from a process `ModuleIndex`
  when one is present, and otherwise parses each file once per content version
  per process. These tests pin the observable contract of that change: an index
  is consulted first, an edit between lookups is never stale, and two files
  declaring one name are still reported as a duplicate identity.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, ModuleIndex, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_user_source_cache_#{System.pid()}_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)

    previous_roots = Process.get(:cure_source_roots)
    previous_index = Process.get(:cure_module_index)
    Process.put(:cure_source_roots, [tmp])
    Process.delete(:cure_module_index)
    Program.clear_user_source_cache()

    on_exit(fn ->
      if previous_roots,
        do: Process.put(:cure_source_roots, previous_roots),
        else: Process.delete(:cure_source_roots)

      if previous_index,
        do: Process.put(:cure_module_index, previous_index),
        else: Process.delete(:cure_module_index)

      Program.clear_user_source_cache()
      File.rm_rf!(tmp)
    end)

    %{tmp: tmp}
  end

  test "an edit between two lookups is seen; the cache is never stale", %{tmp: tmp} do
    path = Path.join(tmp, "lib.cure")
    File.write!(path, "mod Alpha\n  fn one() -> Int = 1\nend\n")
    assert {:ok, _} = elaborate("mod P\n  use Alpha\n  fn f() -> Int = one()\nend\n")

    # Same size, different identity: a size- or mtime-keyed cache would miss this.
    File.write!(path, "mod Gamma\n  fn one() -> Int = 1\nend\n")
    assert {:error, _} = elaborate("mod P\n  use Alpha\n  fn f() -> Int = one()\nend\n")
    assert {:ok, _} = elaborate("mod P\n  use Gamma\n  fn f() -> Int = one()\nend\n")
  end

  test "two files declaring one module name are still a duplicate identity", %{tmp: tmp} do
    File.write!(Path.join(tmp, "a.cure"), "mod Dup\n  fn one() -> Int = 1\nend\n")
    File.write!(Path.join(tmp, "b.cure"), "mod Dup\n  fn one() -> Int = 2\nend\n")

    assert {:error, {:duplicate_module_identity, "Dup", paths}} =
             elaborate("mod P\n  use Dup\n  fn f() -> Int = one()\nend\n")

    assert paths == Enum.sort([Path.join(tmp, "a.cure"), Path.join(tmp, "b.cure")])
  end

  test "a process ModuleIndex answers before any source-root scan", %{tmp: tmp} do
    # The real module lives outside the configured roots; only the index knows it.
    outside = Path.join(tmp, "outside")
    File.mkdir_p!(outside)
    path = Path.join(outside, "indexed.cure")
    File.write!(path, "mod Indexed\n  fn one() -> Int = 1\nend\n")
    Process.put(:cure_source_roots, [Path.join(tmp, "empty")])
    File.mkdir_p!(Path.join(tmp, "empty"))

    assert {:error, _} = elaborate("mod P\n  use Indexed\n  fn f() -> Int = one()\nend\n")

    {:ok, index} = ModuleIndex.build([path], validate_dependencies: false)
    Process.put(:cure_module_index, index)
    assert {:ok, _} = elaborate("mod P\n  use Indexed\n  fn f() -> Int = one()\nend\n")
  end

  test "the per-file cache is dropped when the outermost compilation ends", %{tmp: tmp} do
    path = Path.join(tmp, "lib.cure")
    File.write!(path, "mod Alpha\n  fn one() -> Int = 1\nend\n")
    Process.delete(:cure_source_roots)

    assert {:ok, _, _} =
             Cure.Compiler.compile_file(path,
               output_dir: Path.join(tmp, "out"),
               source_roots: [tmp],
               emit_events: false
             )

    refute Enum.any?(Process.get_keys(), &match?({:cure_user_module_cache, _}, &1))
  end
end
