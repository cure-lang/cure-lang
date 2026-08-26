defmodule Cure.Stdlib.DecideAtBoundaryTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  @moduletag :stdlib

  @src """
  mod DecideAtBoundary
    use Std.Bool
    use Std.Decision
    use Std.Proof.IntMath

    # An external Int is DECIDED, not asserted; the Yes branch carries evidence.
    fn classify(external_value: Int) -> Bool =
      match decide_is_true(external_value > 0)
        Yes(evidence) -> True()
        No(_) -> False()
  end
  """

  test "the decide-at-boundary pattern type-checks in both branches" do
    assert {:ok, _env} = Program.elaborate(@src)
  end
end
