defmodule Cure.Doc.DoctestsTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Doctests

  describe "extract_from_source/1" do
    test "captures a single cure>/=> pair" do
      src = """
      ## Adds two ints.
      ##
      ##   cure> Demo.add(2, 3)
      ##   => 5
      fn add(a: Int, b: Int) -> Int = a + b
      """

      assert [%{name: "add_2", expr: "Demo.add(2, 3)", expected: "5"}] =
               Doctests.extract_from_source(src)
    end

    test "captures multiple pairs in one block" do
      src = """
      ## Demo.
      ##   cure> Demo.add(1, 2)
      ##   => 3
      ##   cure> Demo.add(10, -4)
      ##   => 6
      fn add(a: Int, b: Int) -> Int = a + b
      """

      cases = Doctests.extract_from_source(src)
      assert length(cases) == 2
      assert Enum.all?(cases, fn %{expr: e} -> String.starts_with?(e, "Demo.add") end)
    end

    test "ignores cure> without =>" do
      src = """
      ## Lonely.
      ##   cure> Demo.foo()
      fn foo() -> Int = 0
      """

      assert [] = Doctests.extract_from_source(src)
    end

    test "no doctests means empty list" do
      src = "mod Demo\n  fn nothing() -> Int = 0\n"
      assert [] = Doctests.extract_from_source(src)
    end
  end

  test "compile failures use a diagnostic code instead of exposing the raw reason" do
    assert {:fail, diagnostic, registry} = Doctests.run_one("missing_name", "0", "doctest.cure")

    rendered =
      Cure.Diagnostic.Sink.new(format: :plain, color: :never, width: 80, registry: registry)
      |> Cure.Diagnostic.Sink.render(diagnostic)

    assert rendered =~ "UNKNOWN VALUE [E091]"
    assert rendered =~ "fn main() = missing_name"
    assert rendered =~ "^^^^^^^^^^^^"
    refute rendered =~ "compile error:"
    refute rendered =~ "{:unknown_global"
  end

  test "expectation failures remain structured until presentation" do
    assert {:fail, diagnostic, nil} = Doctests.run_one("1", "2", "doctest.cure")
    assert diagnostic.code == "E098"
    assert Cure.Diagnostic.message(diagnostic) == "doctest failed: expected 2, got 1"
  end
end
