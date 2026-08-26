defmodule Cure.Compiler.GroupAttributeTest do
  @moduledoc """
  The `-group([:g])` BEAM attribute is emitted whether `@group` is attached
  above `mod` (container meta) or, transitionally, as an in-body standalone
  node. Guards `Cure.Compiler.inject_group_attribute/2` (spec
  2026-07-10-group-decorator-placement).
  """
  use ExUnit.Case, async: false

  # Compile+load a Cure source string and read the module's `:group` attribute.
  defp group_attr(src) do
    {:ok, mod} = Cure.Compiler.compile_and_load(src)
    mod.module_info(:attributes) |> Keyword.get(:group)
  end

  test "above-mod @group still emits the -group BEAM attribute" do
    attr =
      group_attr("@group(:sensors)\nmod GroupAttrAboveProbe\n  fn f(x: Int) -> Int = x\nend\n")

    assert attr == [:sensors]
  end
end
