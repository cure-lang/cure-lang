defmodule Cure.Compiler.DepGraphResilienceTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.DepGraph

  setup do
    dir = Path.join(System.tmp_dir!(), "dg_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "a file using a not-yet-resolvable operator keeps its module + use edge", %{dir: dir} do
    a = Path.join(dir, "a.cure")
    b = Path.join(dir, "b.cure")
    File.write!(a, "mod A\n  precedencegroup G\n    associativity: left\n  infix `<?>` : G\nend\n")
    # B's body uses <?>, which a standalone table-naive parse of B cannot bind.
    File.write!(b, "mod B\n  use A\n  fn go() -> Int = 1 <?> 2\nend\n")

    {:ok, graph} = DepGraph.scan([b, a])

    assert Map.has_key?(graph.modules, "B"), "B must survive despite the <?> parse error"
    assert graph.modules["A"] == a
    b_node = graph.nodes[b]
    assert b_node.module == "B"
    assert Enum.any?(b_node.order_deps, &(&1.target == "A"))
  end
end
