defmodule Cure.Std.OperatorsModuleTest do
  @moduledoc "Phase 3: Std.Operators reproduces the legacy precedence order."
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.FixityTable

  test "assembled built-in table matches legacy relative order" do
    # new accessor: table from Std.Operators
    t = Cure.Stdlib.Preload.builtin_fixity_table()
    {and_lp, _} = FixityTable.infix_bp(t, "and")
    {or_lp, _} = FixityTable.infix_bp(t, "or")
    {plus_lp, _} = FixityTable.infix_bp(t, "+")
    {star_lp, _} = FixityTable.infix_bp(t, "*")
    {lt_lp, _} = FixityTable.infix_bp(t, "<")
    assert or_lp < and_lp
    assert and_lp < lt_lp
    assert lt_lp < plus_lp
    assert plus_lp < star_lp
    assert FixityTable.non_assoc?(t, "<")
    assert FixityTable.non_assoc?(t, "==")
  end
end
