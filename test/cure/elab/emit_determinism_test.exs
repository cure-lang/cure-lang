defmodule Cure.Elab.EmitDeterminismTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "synthetic BEAM binders do not depend on prior VM allocations" do
    source = """
    mod EmitDeterminism
      type Pair = Pair(Int, Int)
      fn first(pair: Pair) -> Int = match pair
        Pair(left, _right) -> left
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    first =
      Emit.module_forms(
        env,
        :"Cure.EmitDeterminism",
        [:"EmitDeterminism#first"]
      )

    for _ <- 1..100, do: System.unique_integer([:positive, :monotonic])

    second =
      Emit.module_forms(
        env,
        :"Cure.EmitDeterminism",
        [:"EmitDeterminism#first"]
      )

    assert second == first
  end
end
