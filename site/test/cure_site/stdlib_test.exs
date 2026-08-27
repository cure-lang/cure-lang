defmodule CureSite.StdlibTest do
  use ExUnit.Case, async: true

  alias CureSite.Stdlib

  test "modules/0 returns all standard library modules" do
    modules = Stdlib.modules()
    assert is_list(modules)
    assert length(modules) == 68

    names = Enum.map(modules, & &1.module)
    assert "Std.Core" in names
    assert "Std.Actor" in names
    assert "Std.List" in names
    assert "Std.Math" in names
    assert "Std.Proof" in names
  end

  test "groups/0 categorizes all standard library modules with no leftover 'Other' group" do
    groups = Stdlib.groups()
    assert is_list(groups)

    group_names = Enum.map(groups, &elem(&1, 0))
    refute "Other" in group_names, "Expected no modules to fall into the fallback 'Other' bucket, but found leftover modules"

    expected_groups = [
      "Core & Type System",
      "Primitive Types",
      "Numeric & Math",
      "Collections & Iteration",
      "Protocols & Abstractions",
      "Control & Error Handling",
      "Concurrency & OTP",
      "System & I/O",
      "Syntax & Metaprogramming",
      "Proofs & Formal Verification",
      "Testing & Quality"
    ]

    assert group_names == expected_groups

    total_grouped_modules =
      groups
      |> Enum.flat_map(fn {_name, mods} -> mods end)
      |> Enum.map(& &1.module)

    assert length(total_grouped_modules) == 68
    assert Enum.uniq(total_grouped_modules) == total_grouped_modules
  end

  test "module/1 fetches expected module docs" do
    core = Stdlib.module("Std.Core")
    assert core != nil
    assert core.module == "Std.Core"

    non_existent = Stdlib.module("Std.DoesNotExist")
    assert non_existent == nil
  end
end
