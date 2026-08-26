defmodule Cure.Elab.ImportedModuleDupTest do
  @moduledoc """
  `program.ex` has two doors into `elaborate_declarations/3`. The top-level entry, `check_ast/2`,
  ran the duplicate guards first. Every imported-module path — `module_slice_env/1` for a direct
  `use`, `import_source_env/2` for a transitive nested import — called `elaborate_declarations/3`
  straight from the parsed AST and ran none of them.

  `Env.add_def/5` and `Inductive.declare/3` both register by plain `Map.put`, so whichever door
  skipped the check silently kept only the LAST same-named declaration and dropped the rest with
  no error. A duplicate inside a `Std.*` source was therefore accepted where the identical
  duplicate pasted into the top-level module was rejected (`dup_def_test.exs`). Both doors now
  run the same `check_declarations/1`.

  Fixture modules live in a process-local source root. Canonical stdlib modules
  continue to come from the verified stdlib provider.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_imported_dup_#{System.unique_integer([:positive])}")

    File.mkdir_p!(tmp)

    File.write!(Path.join(tmp, "dupfn.cure"), """
    mod Std.DupFn
      fn foo() -> Int = 1
      fn foo() -> Int = 2
    end
    """)

    File.write!(Path.join(tmp, "duptype.cure"), """
    mod Std.DupType
      type Widget = MkA
      type Widget = MkB
    end
    """)

    File.write!(Path.join(tmp, "okfn.cure"), """
    mod Std.OkFn
      fn only_once() -> Int = 1
    end
    """)

    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [tmp])

    on_exit(fn ->
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)

      File.rm_rf!(tmp)
    end)

    :ok
  end

  test "a duplicate fn name inside an imported module is rejected, not kept last-wins" do
    src = "mod P\n  use Std.DupFn\n  fn f() -> Int = foo()\nend\n"
    assert {:error, {:overlapping_overload, %{name: :foo, arity: 0}}} = elaborate(src)
  end

  test "a duplicate type name inside an imported module is rejected, not kept last-wins" do
    src = "mod Q\n  use Std.DupType\n  fn g() -> Widget = MkB\nend\n"
    assert {:error, {:duplicate_type, %{name: :Widget, spans: [first, second]}}} = elaborate(src)
    assert first.start_line == 2
    assert second.start_line == 3
  end

  test "an imported module with no duplicates still elaborates" do
    # Guard against a guard that rejects every import.
    src = "mod R\n  use Std.OkFn\n  fn h() -> Int = only_once()\nend\n"
    assert {:ok, _} = elaborate(src)
  end
end
