defmodule Cure.Stdlib.DependentRegexWordBoundaryTest do
  use ExUnit.Case, async: false

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it
  # erases to the tagged pair `{:String, code_points}`. Subjects and the three
  # `String` partitions of a `Match` carry the tag; `Char` still erases to a bare
  # code point.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexWordBoundaryRuntime
      use Std.Regex

      fn cat() -> Regex(Unit) =
        discard_left(exactly('c'), discard_left(exactly('a'), exactly('t')))

      fn accent() -> Regex(Unit) = exactly('é')

      fn bounded(regex: Regex(Unit), unicode: Bool, negated: Bool) -> Regex(Unit) =
        discard_left(
          word_boundary(unicode, negated),
          discard_right(regex, word_boundary(unicode, negated))
        )

      fn ascii_word(input: String) -> Option(Match(Unit)) = search(bounded(cat(), false, false), input)
      fn interior(input: String) -> Option(Match(Unit)) = search(bounded(cat(), false, true), input)
      fn unicode_word(input: String) -> Option(Match(Unit)) = search(bounded(accent(), true, false), input)
      fn ascii_unicode_letter(input: String) -> Option(Match(Unit)) = search(bounded(accent(), false, false), input)
      # `Char` has no natural-literal spelling -- its `ExpressibleByNaturalLiteral`
      # instance bottoms out in the extern `from_code_point`, which never reduces
      # at compile time -- so backspace is written as its escape, not as `8`.
      fn class_backspace(input: String) -> Option(Char) = parse_full(one_of(['\\b']), input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "\\b observes the current search position and ASCII/Unicode word mode", %{runtime_module: module} do
    assert apply(module, :ascii_word, [cure_string(~c"a cat!")]) ==
             {:some, {:Match, :unit, cure_string(~c"a "), cure_string(~c"cat"), cure_string(~c"!"), 2, 3}}

    assert apply(module, :ascii_word, [cure_string(~c"concatenate")]) == :none

    assert apply(module, :unicode_word, [cure_string([?\s, ?é, ?\s])]) ==
             {:some, {:Match, :unit, cure_string(~c" "), cure_string(~c"é"), cure_string(~c" "), 1, 1}}

    assert apply(module, :ascii_unicode_letter, [cure_string([?\s, ?é, ?\s])]) == :none
  end

  test "\\B is the complement and \\b inside a class is backspace", %{runtime_module: module} do
    assert apply(module, :interior, [cure_string(~c"scatx")]) ==
             {:some, {:Match, :unit, cure_string(~c"s"), cure_string(~c"cat"), cure_string(~c"x"), 1, 3}}

    assert apply(module, :class_backspace, [cure_string([8])]) == {:some, 8}
  end
end
