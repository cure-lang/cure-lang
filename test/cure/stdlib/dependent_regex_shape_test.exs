defmodule Cure.Stdlib.DependentRegexShapeTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @shape_source File.read!(Path.expand("../../../lib/std_deps/regex/regex.cure", __DIR__))

  test "ShapeCode and Sem elaborate as a genuine large elimination" do
    assert {:ok, _env} = Program.elaborate(@shape_source)
  end

  test "Sem reduces nested pair, list, and unit codes definitionally" do
    source = """
    mod RegexShapeUse
      use Std.Regex

      fn nested(value: Char) -> Sem(PairC(CharC, ListC(UnitC))) =
        %[value, [(), ()]]
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "Sem rejects a value from the wrong computed branch" do
    source = """
    mod RegexShapeWrong
      use Std.Regex

      fn wrong() -> Sem(CharC) = true
    end
    """

    assert {:error, _diagnostic} = Program.elaborate(source)
  end

  test "shape simplification computes ergonomic result types and values" do
    source = """
    mod RegexShapeSimplify
      use Std.Regex

      fn pair_left(char: Char) -> Sem(Simplify(PairC(UnitC, CharC))) =
        simplify_value(PairC(UnitC, CharC), %[(), char])

      fn pair_right(char: Char) -> Sem(Simplify(PairC(CharC, UnitC))) =
        simplify_value(PairC(CharC, UnitC), %[char, ()])

      fn optional_yes() -> Sem(Simplify(OptionC(UnitC))) =
        simplify_value(OptionC(UnitC), Some(()))

      fn optional_no() -> Sem(Simplify(OptionC(UnitC))) =
        simplify_value(OptionC(UnitC), None())

      fn alternatives() -> Sem(Simplify(ChoiceC(UnitC, UnitC))) =
        simplify_value(ChoiceC(UnitC, UnitC), ChoseLeft(()))

      fn repetitions() -> Sem(Simplify(ListC(UnitC))) =
        simplify_value(ListC(UnitC), [(), (), ()])
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
