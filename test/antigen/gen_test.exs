defmodule Antigen.GenTest do
  use ExUnit.Case, async: true
  alias Antigen.Gen

  test "constructors reify to inspectable tagged tuples" do
    assert Gen.return(3) == {:return, 3}
    assert Gen.member_of([1, 2]) == {:member_of, [1, 2]}

    assert {:frequency, [{2, {:return, :a}}, {1, {:return, :b}}]} =
             Gen.frequency([{2, Gen.return(:a)}, {1, Gen.return(:b)}])

    assert {:bind, {:return, 1}, _f} = Gen.bind(Gen.return(1), fn x -> Gen.return(x + 1) end)
  end

  test "int/2 is derived from member_of over the range" do
    assert Gen.int(0, 2) == {:member_of, [0, 1, 2]}
  end

  test "support is finite for member_of/one_of/return and over-approx through bind" do
    assert Gen.support(Gen.member_of([1, 2, 3])) == {:finite, MapSet.new([1, 2, 3])}
    assert Gen.support(Gen.one_of([Gen.return(:a), Gen.return(:b)])) == {:finite, MapSet.new([:a, :b])}
    assert Gen.support(Gen.bind(Gen.return(1), fn _ -> Gen.return(2) end)) == :over_approx
  end

  test "tag records size hygiene" do
    assert Gen.tag(Gen.member_of([1]), :unsized) == {:tagged, :unsized, {:member_of, [1]}}
  end
end
