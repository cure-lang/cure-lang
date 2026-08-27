defmodule Cure.Stdlib.DependentRegexParseTest do
  use ExUnit.Case, async: false

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it erases
  # to the tagged pair `{:String, code_points}`. `Regex(String)` results and the
  # three `String` partitions of a `Match` carry that tag; a `Regex(List(Char))`
  # result (`repeat`, a bare literal) stays a bare charlist.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexTypedParsing
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Regex(Char) = predicate(same(char))
      fn pattern_atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn as_text(char: Char) -> String = Std.String.from_characters([char])

      fn parsed_char() -> Option(Char) = parse_full(atom('a'), "a")
      fn parsed_exact() -> Option(Unit) = parse_full(exactly('a'), "a")
      fn parsed_pair() -> Option(Tuple(Char, Char)) = parse_full(concatenate(atom('a'), atom('b')), "ab")
      fn parsed_map() -> Option(String) = parse_full(map(atom('a'), as_text), "a")
      fn parsed_optional_some() -> Option(Option(Char)) = parse_full(optional(atom('a')), "a")
      fn parsed_optional_none() -> Option(Option(Char)) = parse_full(optional(atom('a')), "")
      fn parsed_many() -> Option(List(Char)) = parse_full(repeat(atom('a')), "aaa")
      fn parsed_one_or_more() -> Option(OneOrMore(Char)) = parse_full(one_or_more(atom('a')), "aaa")
      fn parsed_capture() -> Option(String) = parse_full(captured(concatenate(atom('a'), atom('b'))), "ab")
      fn parsed_right() -> Option(Char) = parse_full(discard_left(exactly('a'), atom('b')), "ab")
      fn parsed_left() -> Option(Char) = parse_full(discard_right(atom('a'), exactly('b')), "ab")
      fn parsed_same_alt() -> Option(Char) = parse_full(or_same(atom('a'), atom('b')), "b")
      fn parsed_literal() -> Option(List(Char)) = parse_full(/a[bc]*/, "abcb")
      fn parsed_prefix() -> Option(Tuple(List(Char), String)) = parse_prefix(repeat(atom('a')), "aaab")
      fn searched() -> Option(Match(String)) = search(captured(one_or_more(atom('a'))), "xxaaay")
      fn searched_leftmost_longest() -> Option(Match(String)) =
        search(
          captured(or_same(as_string(concatenate(atom('a'), atom('a'))), as_string(atom('a')))),
          "xaay"
        )
      fn searched_unicode_positions() -> Option(Match(String)) =
        search(captured(one_or_more(atom('é'))), "λééx")
      fn search_matches() -> Bool = matches(atom('a'), "xxax")
      fn search_misses() -> Bool = matches(atom('z'), "xxax")
      fn failed() -> Option(Char) = parse_full(atom('a'), "b")
      fn staged_many(input: String) -> Option(List(Char)) = parse_full(/[a]*/, input)
      fn unstaged_many(input: String) -> Option(List(Char)) = parse_pattern_full(PatternRepeat(pattern_atom('a')), input)
      fn staged_capture(input: String) -> Option(String) = parse_full(/([ab])/, input)
      fn unstaged_capture(input: String) -> Option(String) = parse_pattern_full(PatternGroup(PatternAlternateMode(pattern_atom('a'), pattern_atom('b'), false)), input)
    end
    """

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "public typed parsing executes every core Regex conversion", %{runtime_module: module} do
    assert apply(module, :parsed_char, []) == {:some, ?a}
    assert apply(module, :parsed_exact, []) == {:some, :unit}
    assert apply(module, :parsed_pair, []) == {:some, {?a, ?b}}
    assert apply(module, :parsed_map, []) == {:some, cure_string(~c"a")}
    assert apply(module, :parsed_optional_some, []) == {:some, {:some, ?a}}
    assert apply(module, :parsed_optional_none, []) == {:some, :none}
    assert apply(module, :parsed_many, []) == {:some, ~c"aaa"}
    assert apply(module, :parsed_one_or_more, []) == {:some, {:OneOrMore, ?a, ~c"aa"}}
    assert apply(module, :parsed_capture, []) == {:some, cure_string(~c"ab")}
    assert apply(module, :parsed_right, []) == {:some, ?b}
    assert apply(module, :parsed_left, []) == {:some, ?a}
    assert apply(module, :parsed_same_alt, []) == {:some, ?b}
  end

  test "literal expansion feeds the typed engine without runtime pattern parsing", %{runtime_module: module} do
    assert apply(module, :parsed_literal, []) == {:some, ~c"bcb"}
  end

  test "prefix parsing returns the typed value and untouched suffix", %{runtime_module: module} do
    assert apply(module, :parsed_prefix, []) == {:some, {~c"aaa", cure_string(~c"b")}}
  end

  test "search is leftmost, longest, typed, and reports all input partitions", %{runtime_module: module} do
    assert apply(module, :searched, []) ==
             {:some,
              {:Match, cure_string(~c"aaa"), cure_string(~c"xx"), cure_string(~c"aaa"), cure_string(~c"y"), 2, 3}}

    assert apply(module, :searched_leftmost_longest, []) ==
             {:some, {:Match, cure_string(~c"aa"), cure_string(~c"x"), cure_string(~c"aa"), cure_string(~c"y"), 1, 2}}

    assert apply(module, :searched_unicode_positions, []) ==
             {:some, {:Match, cure_string(~c"éé"), cure_string(~c"λ"), cure_string(~c"éé"), cure_string(~c"x"), 1, 2}}

    assert apply(module, :search_matches, [])
    refute apply(module, :search_misses, [])
  end

  test "failed full parsing returns None", %{runtime_module: module} do
    assert apply(module, :failed, []) == :none
  end

  test "staged literals and unstaged Pattern proofs agree on exhaustive small subjects", %{runtime_module: module} do
    subjects =
      for size <- 0..4,
          word <-
            List.duplicate(~c"abc", size)
            |> List.foldl([[]], fn alphabet, words -> for c <- alphabet, w <- words, do: [c | w] end),
          do: Enum.reverse(word)

    for subject <- subjects do
      input = cure_string(subject)

      assert apply(module, :staged_many, [input]) ==
               apply(module, :unstaged_many, [input]),
             "repeat subject=#{inspect(subject)}"

      assert apply(module, :staged_capture, [input]) ==
               apply(module, :unstaged_capture, [input]),
             "capture subject=#{inspect(subject)}"
    end
  end
end
