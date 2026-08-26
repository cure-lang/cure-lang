defmodule Cure.Compiler.Parser.FixityResolverTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.Parser.{FixityResolver, FixityTable}

  setup do
    dir = Path.join(System.tmp_dir!(), "fr_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])

    on_exit(fn ->
      Process.put(:cure_source_roots, prev)
      File.rm_rf!(dir)
    end)

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

    assert {:error,
            {:conflicting_operator_fixity,
             %{operator: "<?>", existing_group: :Ga, new_group: :Gb, spans: [first, second]}}} =
             assemble(["A", "B"])

    assert first.path == Path.join(dir, "a.cure")
    assert second.path == Path.join(dir, "b.cure")
  end

  test "two used modules declaring the same group name with different bodies conflict", %{dir: dir} do
    write(dir, "a.cure", "mod A\n  precedencegroup G\n    associativity: left\nend\n")
    write(dir, "b.cure", "mod B\n  precedencegroup G\n    associativity: right\nend\n")

    assert {:error,
            {:conflicting_precedence_group,
             %{name: :G, existing: %{assoc: :left}, new: %{assoc: :right}, spans: [first, second]}}} =
             assemble(["A", "B"])

    assert first.path == Path.join(dir, "a.cure")
    assert second.path == Path.join(dir, "b.cure")
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
