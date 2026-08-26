defmodule Cure.Stdlib.DependentRegexCoreTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp compile_and_load(source) do
    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    module
  end

  test "Pattern constructors compute their result shapes" do
    source = """
    mod RegexCoreShapes
      use Std.Regex

      fn any(char: Char) -> Bool = true

      fn atom() -> Pattern(CharC) = PatternPredicate(any)
      fn nullable() -> Pattern(UnitC) = PatternEmpty()
      fn pair() -> Pattern(PairC(CharC, UnitC)) = PatternConcat(atom(), nullable())
      fn branch() -> Pattern(ChoiceC(CharC, UnitC)) = PatternAlternate(atom(), nullable())
      fn many() -> Pattern(ListC(CharC)) = PatternRepeat(atom())
      fn capture() -> Pattern(StringC) = PatternGroup(atom())
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "Pattern rejects an incorrect constructor index" do
    source = """
    mod RegexCoreWrong
      use Std.Regex

      fn wrong() -> Pattern(CharC) = PatternEmpty()
    end
    """

    assert {:error, _diagnostic} = Program.elaborate(source)
  end

  test "Regex combinators compute user result types" do
    source = """
    mod RegexTypedShapes
      use Std.Regex

      fn any(char: Char) -> Bool = true
      fn char() -> Regex(Char) = predicate(any)
      fn pair() -> Regex(Tuple(Char, Unit)) = concatenate(char(), empty())
      fn branch() -> Regex(Choice(Char, Unit)) = alternate(char(), empty())
      fn many() -> Regex(List(Char)) = repeat(char())
      fn count(chars: List(Char)) -> Int = match chars
        [] -> 0
        [_ | rest] -> 1 + count(rest)
      fn counted() -> Regex(Int) = map(many(), count)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "smart constructors expose ergonomic result types" do
    source = """
    mod RegexSmartConstructors
      use Std.Regex

      fn exact_x() -> Regex(Unit) = exactly('x')
      fn char() -> Regex(Char) = range('a', 'z')
      fn chars() -> Regex(Char) = one_of(['a', 'b'])
      fn either() -> Regex(Char) = or_same(char(), chars())
      fn maybe() -> Regex(Option(Char)) = optional(char())
      fn many() -> Regex(OneOrMore(Char)) = one_or_more(char())
      fn right() -> Regex(Char) = discard_left(exact_x(), char())
      fn left() -> Regex(Char) = discard_right(char(), exact_x())
      fn text() -> Regex(String) = captured(many())
      fn simplified_pair() -> Regex(Char) = simplified(PairC(UnitC, CharC), concatenate(exact_x(), char()))
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "epsilon-free Thompson machines accept every Pattern constructor" do
    source = """
    mod RegexMachineRuntime
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn empty() -> Pattern(UnitC) = PatternEmpty()
      fn ab() -> Pattern(PairC(CharC, CharC)) = PatternConcat(atom('a'), atom('b'))
      fn either() -> Pattern(ChoiceC(CharC, CharC)) = PatternAlternate(atom('a'), atom('b'))
      fn many() -> Pattern(ListC(CharC)) = PatternRepeat(atom('a'))
      fn grouped() -> Pattern(StringC) = PatternGroup(ab())

      fn empty_yes() -> Bool = pattern_accepts(empty(), "")
      fn empty_no() -> Bool = pattern_accepts(empty(), "a")
      fn concat_yes() -> Bool = pattern_accepts(ab(), "ab")
      fn concat_short() -> Bool = pattern_accepts(ab(), "a")
      fn concat_long() -> Bool = pattern_accepts(ab(), "aba")
      fn alt_left() -> Bool = pattern_accepts(either(), "a")
      fn alt_right() -> Bool = pattern_accepts(either(), "b")
      fn alt_no() -> Bool = pattern_accepts(either(), "c")
      fn star_empty() -> Bool = pattern_accepts(many(), "")
      fn star_many() -> Bool = pattern_accepts(many(), "aaaa")
      fn star_no() -> Bool = pattern_accepts(many(), "aaab")
      fn group_yes() -> Bool = pattern_accepts(grouped(), "ab")
    end
    """

    module = compile_and_load(source)

    for name <- [:empty_yes, :concat_yes, :alt_left, :alt_right, :star_empty, :star_many, :group_yes] do
      assert apply(module, name, [])
    end

    for name <- [:empty_no, :concat_short, :concat_long, :alt_no, :star_no] do
      refute apply(module, name, [])
    end
  end

  test "nullable repetition terminates without epsilon closure" do
    source = """
    mod RegexNullableStar
      use Std.Regex

      fn nested() -> Pattern(ListC(UnitC)) = PatternRepeat(PatternEmpty())
      fn accepts_empty() -> Bool = pattern_accepts(nested(), "")
      fn rejects_char() -> Bool = pattern_accepts(nested(), "x")
    end
    """

    module = compile_and_load(source)
    assert apply(module, :accepts_empty, [])
    refute apply(module, :rejects_char, [])
  end
end
