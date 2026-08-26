defmodule Cure.Stdlib.NonEmptyTest do
  use ExUnit.Case, async: false

  # `Cure.Std.NonEmpty` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all`; Elixir's compile-time checker doesn't see it.
  @compile {:no_warn_undefined, :"Cure.Std.NonEmpty"}

  @ne :"Cure.Std.NonEmpty"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  test "singleton has the element as head and an empty tail" do
    ne = @ne.singleton(7)
    assert @ne.head(ne) == 7
    assert @ne.tail(ne) == []
    assert @ne.to_list(ne) == [7]
  end

  test "from_list on a non-empty list splits head and tail" do
    assert {:some, ne} = @ne.from_list([1, 2, 3])
    assert @ne.head(ne) == 1
    assert @ne.tail(ne) == [2, 3]
    assert @ne.to_list(ne) == [1, 2, 3]
  end

  test "from_list on the empty list is None" do
    assert @ne.from_list([]) == :none
  end

  test "push prepends a new head" do
    {:some, ne} = @ne.from_list([1, 2, 3])
    pushed = @ne.push(0, ne)
    assert @ne.head(pushed) == 0
    assert @ne.to_list(pushed) == [0, 1, 2, 3]
  end

  test "map applies over head and tail" do
    {:some, ne} = @ne.from_list([1, 2, 3])
    doubled = @ne.map(ne, fn x -> x * 10 end)
    assert @ne.to_list(doubled) == [10, 20, 30]
  end

  test "to_list then from_list round-trips a non-empty list" do
    {:some, ne} = @ne.from_list([4, 5, 6])
    assert {:some, ne2} = @ne.from_list(@ne.to_list(ne))
    assert @ne.to_list(ne2) == [4, 5, 6]
  end
end
