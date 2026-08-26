defmodule Cure.Compiler.BeamWriterTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.BeamWriter

  test "normalizes BEAM warning groups into the public diagnostic schema" do
    warnings = [
      {~c"nofile", [{{7, 11}, :erl_lint, {:unused_var, :GeneratedValue}}]}
    ]

    assert [warning] = BeamWriter.normalize_warnings(warnings, "src/demo.cure")
    assert warning.file == "src/demo.cure"
    assert warning.line == 7
    assert warning.message == "variable 'GeneratedValue' is unused"
  end

  test "unclassified BEAM warnings remain structured without leaking terms" do
    assert [warning] = BeamWriter.normalize_warnings([{:unexpected, :shape}], "src/demo.cure")
    assert warning.file == "src/demo.cure"
    assert warning.line == 1
    assert warning.message =~ "unclassified warning"
    refute warning.message =~ ":unexpected"
  end
end
