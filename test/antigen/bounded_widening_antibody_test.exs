defmodule Antigen.BoundedWideningAntibodyTest do
  use ExUnit.Case, async: true

  @moduletag :antibody

  test "the two checked injections cannot overlap or escape their combined bound" do
    source = """
    mod BoundedWideningAntibody
      use Std.Bounded
      fn left(value: Bounded(4)) -> Bounded(plus(4, 3)) = inject_left(value)
      fn right(value: Bounded(3)) -> Bounded(plus(4, 3)) = inject_right(4, value)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    left = Enum.map(0..3, &apply(module, :left, [&1]))
    right = Enum.map(0..2, &apply(module, :right, [&1]))

    assert Enum.all?(left ++ right, &(&1 >= 0 and &1 < 7))
    assert MapSet.disjoint?(MapSet.new(left), MapSet.new(right))
  end
end
