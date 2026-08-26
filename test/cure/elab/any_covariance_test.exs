defmodule Cure.Elab.AnyCovarianceTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Any is a top type and List lifts widening covariantly" do
    source = """
    mod AnyCovariance
      fn widen(xs: List(Int)) -> List(Any) = xs
      fn first_three() -> List(Any) = widen([1, 2, 3])
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "widening does not cross a function domain" do
    source = """
    mod UnsafeCovariance
      fn widen(fs: List(Int -> Int)) -> List(Any -> Int) = fs
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "recursive occurrences through List and Tuple remain strictly positive" do
    source = """
    mod PositiveJson
      type Json =
        | Leaf(Int)
        | Object(List(Tuple(String, Json)))
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
