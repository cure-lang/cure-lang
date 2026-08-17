defmodule Cure.Stdlib.DependentRegexBoundedStateTest do
  use ExUnit.Case, async: true

  @regex_source File.read!(Path.expand("../../../lib/std/regex_core.cure", __DIR__))
  @facade_source File.read!(Path.expand("../../../lib/std/regex.cure", __DIR__))

  test "the machine state and transition relation are indexed by their finite bound" do
    assert @regex_source =~ "type MachineState indices (n: Nat)"
    assert @regex_source =~ "Active : Bounded(n)"
    assert @regex_source =~ "type PatternMachine indices (n: Nat)"
    assert @regex_source =~ "(Bounded(n)) -> Char -> List(MachineState(n))"

    refute @regex_source =~ "Active(Nat"
    refute @regex_source =~ "Nat -> Char -> List(MachineState)"
    refute @regex_source =~ "fn nat_less("
    refute @regex_source =~ "fn nat_subtract("
  end

  test "the indexed Regex module still elaborates through the canonical environment" do
    assert {:ok, _env} = Cure.Elab.Program.elaborate(@facade_source)
  end
end
