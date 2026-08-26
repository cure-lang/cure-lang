defmodule Cure.Stdlib.PreloadClosureTest do
  use ExUnit.Case, async: true

  alias Cure.Stdlib.Preload

  test "baked order deps carry Vector -> Nat/Bounded (the only stdlib use edges)" do
    deps = Preload.module_order_deps()

    assert :"Cure.Std.Nat" in Map.fetch!(deps, :"Cure.Std.Vector")
    assert :"Cure.Std.Bounded" in Map.fetch!(deps, :"Cure.Std.Vector")
    assert :"Cure.Std.Nat" in Map.fetch!(deps, :"Cure.Std.Bounded")
  end

  test "baked closure deps carry qualified-call targets (Vector -> Nat/Bounded)" do
    deps = Preload.module_closure_deps()
    vector = Map.fetch!(deps, :"Cure.Std.Vector")

    for m <- [:"Cure.Std.Nat", :"Cure.Std.Bounded"] do
      assert m in vector, "expected #{m} in Vector closure, got #{inspect(vector)}"
    end
  end

  test "closure_modules expands a selection across groups" do
    # Vector is :collections; its use-deps Nat and Bounded are :core.
    expanded = Preload.closure_modules(:collections)

    assert :"Cure.Std.Vector" in expanded
    assert :"Cure.Std.Nat" in expanded
    assert :"Cure.Std.Bounded" in expanded
    # selection itself unchanged:
    refute :"Cure.Std.Nat" in Preload.stdlib_modules(:collections)
  end

  test "closure degrades to plain selection when maps are empty" do
    assert Cure.Compiler.DepGraph.closure(%{}, [:"Cure.Std.List"]) == [:"Cure.Std.List"]
  end

  test "kind API and groups are untouched" do
    assert Preload.known_groups() == [
             :core,
             :collections,
             :text,
             :numeric,
             :system,
             :concurrency,
             :option,
             :test,
             :network
           ]

    assert Preload.stdlib_modules(:none) == []
  end
end
