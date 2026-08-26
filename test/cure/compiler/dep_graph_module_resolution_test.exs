defmodule Cure.Compiler.DepGraphModuleResolutionTest do
  @moduledoc """
  `DepGraph.scan` must resolve a module NAME for every stdlib source, so none is
  silently dropped from the baked closure/order maps that drive `Preload`. A
  file whose top-level AST is a `{:block, _, items}` wrapper (module container +
  a trailing sibling) must still have its module found — `find_module` has to
  descend into a block just as it descends into a raw list.

  Regression: access/string/gen/match/core parse to such a block and were
  dropped (module=nil), taking Access out of the closure map and Std.String out
  of signature resolution.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.DepGraph

  @std_dir Path.join([File.cwd!(), "lib", "std"])

  test "every stdlib module resolves a name in the closure map (no silent drops)" do
    sources = Path.wildcard(Path.join(@std_dir, "*.cure"))
    {:ok, graph} = DepGraph.scan(sources)
    resolved = graph |> DepGraph.closure_deps_map() |> Map.keys() |> MapSet.new()

    declared =
      for path <- sources,
          [_, name] <- [Regex.run(~r/^\s*mod\s+([A-Za-z_][\w\.]*)/m, File.read!(path))],
          do: name

    dropped = Enum.reject(declared, &MapSet.member?(resolved, &1))

    assert dropped == [],
           "these stdlib modules were silently dropped by DepGraph.scan: " <>
             Enum.join(dropped, ", ")
  end
end
