defmodule Cure.Compiler.FixityTableTest do
  @moduledoc "Phase 3: a fixity table computes binding powers from group relations."
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  test "higher_than/lower_than yield a consistent binding-power order" do
    t =
      FixityTable.new()
      |> FixityTable.add_group(:Comparison, assoc: :none, higher_than: [], lower_than: [:Additive])
      |> FixityTable.add_group(:Additive, assoc: :left, higher_than: [:Comparison], lower_than: [:Multiplicative])
      |> FixityTable.add_group(:Multiplicative, assoc: :left, higher_than: [:Additive], lower_than: [])
      |> FixityTable.add_infix("+", :Additive)
      |> FixityTable.add_infix("*", :Multiplicative)
      |> FixityTable.add_infix("<", :Comparison)

    {lp_plus, _} = FixityTable.infix_bp(t, "+")
    {lp_star, _} = FixityTable.infix_bp(t, "*")
    {lp_lt, _} = FixityTable.infix_bp(t, "<")
    assert lp_lt < lp_plus and lp_plus < lp_star
    assert FixityTable.non_assoc?(t, "<")
    assert FixityTable.infix_bp(t, "unknown") == :not_infix
  end

  test "incomparable groups are detected" do
    t =
      FixityTable.new()
      |> FixityTable.add_group(:A, assoc: :left, higher_than: [], lower_than: [])
      |> FixityTable.add_group(:B, assoc: :left, higher_than: [], lower_than: [])
      |> FixityTable.add_infix("<?>", :A)
      |> FixityTable.add_infix("<!>", :B)

    assert FixityTable.incomparable?(t, "<?>", "<!>")
  end
end
