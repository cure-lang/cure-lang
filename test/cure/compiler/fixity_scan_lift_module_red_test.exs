defmodule Cure.Compiler.Parser.FixityScanLiftModuleRedTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Parser.{FixityResolver, FixityScan, FixityTable}
  alias Cure.Compiler.SourceResolver

  setup do
    dir = Path.join(System.tmp_dir!(), "fslm_#{System.unique_integer([:positive])}")
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

  @lifted_op_source """
  lift module Cure.Generated.LiftedOp
    precedencegroup G
      associativity: left
    infix `<+>` : G
  """

  test "FixityScan.harvest_source recovers the module name of a bare lift module block", %{
    dir: dir
  } do
    path = Path.join(dir, "lifted_op.cure")
    write(dir, "lifted_op.cure", @lifted_op_source)

    scan = FixityScan.harvest_source(@lifted_op_source, path, FixityTable.new())

    # The lift-module block IS the whole source's top-level construct, so
    # module_name/1 must recover its declared name the same way
    # DepGraph.find_module/1 does for the :lift_module tag. Currently it only
    # matches :container, so this comes back nil.
    assert scan.module == "Cure.Generated.LiftedOp"
  end

  test "SourceResolver finds a lift module's file by its declared name", %{dir: dir} do
    write(dir, "lifted_op.cure", @lifted_op_source)

    assert {:ok, _path} = SourceResolver.module_path("Cure.Generated.LiftedOp")
  end

  test "a fixity declared inside a lift module block is reachable via `use`", %{dir: dir} do
    write(dir, "lifted_op.cure", @lifted_op_source)

    {:ok, table} = FixityResolver.assemble(FixityTable.new(), [], ["Cure.Generated.LiftedOp"], [])

    assert FixityTable.group_of(table, "<+>") == :G
  end
end
