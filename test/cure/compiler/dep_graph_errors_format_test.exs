defmodule Cure.Compiler.DepGraphErrorsFormatTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors

  test "import cycle formats as a WARNING with code, module chain and file:line hops" do
    hops = [
      %{module: "CycA", path: "a.cure", line: 3},
      %{module: "CycB", path: "b.cure", line: 2},
      %{module: "CycA", path: "a.cure", line: 3}
    ]

    out = Errors.format_error({:import_cycle, hops}, "a.cure")

    assert out =~ "W086"
    assert out =~ "warning"
    assert out =~ "CycA"
    assert out =~ "CycB"
    assert out =~ "a.cure:3"
    assert out =~ "->"
  end

  test "duplicate module formats with code and both files" do
    out = Errors.format_error({:duplicate_module, "Dup", ["one.cure", "two.cure"]}, "one.cure")
    assert out =~ "E087"
    assert out =~ "Dup"
    assert out =~ "one.cure"
    assert out =~ "two.cure"
  end
end
