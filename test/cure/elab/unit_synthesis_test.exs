defmodule Cure.Elab.UnitSynthesisTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "unit synthesizes a semantic type when nested in inferred arguments" do
    source = """
    mod UnitSynthesis
      fn units() -> List(Unit) = [(), ()]
      fn paired() -> Tuple(Char, List(Unit)) = %['x', [(), ()]]
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
