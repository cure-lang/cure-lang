defmodule Cure.Core.SizeChangeSparseTest do
  use ExUnit.Case, async: true

  alias Cure.Core.SizeChange

  test "dense conversion omits unknown entries and round-trips dimensions" do
    dense = [[:smaller, :unknown, :equal], [:unknown, :unknown, :smaller]]
    sparse = SizeChange.from_dense(dense)

    assert sparse.rows == 2
    assert sparse.columns == 3
    assert sparse.entries == %{{0, 0} => :smaller, {0, 2} => :equal, {1, 2} => :smaller}
    assert SizeChange.to_dense(sparse) == dense
  end

  test "sparse rectangular composition preserves the size-change semiring" do
    # A : 2×3, B : 3×2, so A∘B : 2×2.
    a = SizeChange.from_dense([[:equal, :unknown, :smaller], [:unknown, :equal, :unknown]])
    b = SizeChange.from_dense([[:smaller, :unknown], [:unknown, :equal], [:equal, :unknown]])

    assert SizeChange.compose_matrices(a, b)
           |> SizeChange.to_dense() == [[:smaller, :unknown], [:unknown, :equal]]
  end

  test "empty sparse matrices retain both dimensions" do
    sparse = SizeChange.from_dense([[], []])
    assert {sparse.rows, sparse.columns, sparse.entries} == {2, 0, %{}}
    assert SizeChange.to_dense(sparse) == [[], []]
  end
end
