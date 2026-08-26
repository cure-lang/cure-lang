defmodule Cure.Compiler.FixityTableMergeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  defp base do
    FixityTable.new()
    |> FixityTable.add_group(:Additive, assoc: :left)
    |> FixityTable.add_group(:Multiplicative, assoc: :left)
  end

  test "merge_op into an empty slot adds the operator" do
    {:ok, t} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)
    assert FixityTable.group_of(t, "<?>") == :Additive
  end

  test "merge_op with the identical group is a no-op" do
    {:ok, t1} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)
    assert {:ok, ^t1} = FixityTable.merge_op(t1, "<?>", :infix, :Additive)
  end

  test "merge_op with a different group in the same slot conflicts" do
    {:ok, t1} = FixityTable.merge_op(base(), "<?>", :infix, :Additive)

    assert {:error, {:conflicting_operator_fixity, {"<?>", :Additive, :Multiplicative}}} =
             FixityTable.merge_op(t1, "<?>", :infix, :Multiplicative)
  end

  test "merge_op does not conflict across different slots (prefix vs infix)" do
    {:ok, t1} = FixityTable.merge_op(base(), "-", :infix, :Additive)
    assert {:ok, _} = FixityTable.merge_op(t1, "-", :prefix, :Multiplicative)
  end

  test "merge_group into an empty name adds it" do
    {:ok, t} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left)
    assert Map.has_key?(t.groups, :G)
  end

  test "merge_group with an identical body is a no-op" do
    {:ok, t1} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left, higher_than: [], lower_than: [])
    assert {:ok, ^t1} = FixityTable.merge_group(t1, :G, assoc: :left, higher_than: [], lower_than: [])
  end

  test "merge_group with a different body conflicts" do
    {:ok, t1} = FixityTable.merge_group(FixityTable.new(), :G, assoc: :left)

    assert {:error, {:conflicting_precedence_group, {:G, _existing, _new}}} =
             FixityTable.merge_group(t1, :G, assoc: :right)
  end
end
