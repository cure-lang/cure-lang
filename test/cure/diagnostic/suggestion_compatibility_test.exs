defmodule Cure.Diagnostic.SuggestionCompatibilityTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors

  test "compatibility suggestions recognize adjacent transpositions" do
    assert Errors.suggest("comiple", ["compile", "check"]) == "compile"
  end

  test "compatibility suggestions rank case-insensitively and deterministically" do
    assert Errors.suggest("STRIGN", ["Stream", "String", "stringy"]) == "String"
    assert Errors.suggest("cot", ["cut", "cat"]) == "cat"
  end

  test "compatibility suggestions retain the conservative edit-distance limit" do
    assert Errors.suggest("compile", ["compile"]) == nil
    assert Errors.suggest("compile", ["release"]) == nil
    assert Errors.suggest(nil, ["compile"]) == nil
  end
end
