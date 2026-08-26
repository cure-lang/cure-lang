defmodule Cure.Core.UniverseTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Universe

  test "max picks the larger level" do
    assert Universe.max(0, 1) == 1
    assert Universe.max(2, 1) == 2
    assert Universe.max(1, 1) == 1
  end

  test "le? is the cumulative ordering" do
    assert Universe.le?(0, 1)
    refute Universe.le?(1, 0)
    assert Universe.le?(2, 2)
  end

  test "ceiling is 2" do
    assert Universe.ceiling() == 2
  end

  test "succ yields the universe's own type, erroring past the ceiling" do
    assert Universe.succ(0) == {:ok, 1}
    assert Universe.succ(1) == {:ok, 2}
    assert Universe.succ(2) == {:error, :universe_ceiling}
  end
end
