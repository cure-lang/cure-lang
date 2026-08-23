defmodule Cure.Stdlib.DependentRegexLookaroundTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @runs [max_runs: 200, max_run_time: :infinity]

  @admitted_assertion_shapes [
    :positive_lookahead,
    :negative_lookahead,
    :positive_lookbehind,
    :negative_lookbehind,
    :nested_assertion,
    :mixed_direction_nesting,
    :alternation,
    :greedy_repetition,
    :lazy_repetition,
    :possessive_repetition,
    :atomic_in_assertion,
    :negative_atomic_in_assertion,
    :assertion_in_atomic,
    :subject_anchor,
    :word_boundary,
    :scoped_options,
    :capture_conditional,
    :exact_full_match
  ]

  @admitted_shape_cases [
    {:positive_search, :positive_reference, [:positive_lookahead]},
    {:negative_search, :negative_reference, [:negative_lookahead]},
    {:lookbehind_search, :lookbehind_reference, [:positive_lookbehind]},
    {:negative_lookbehind_search, :negative_lookbehind_reference, [:negative_lookbehind]},
    {:nested_positive_search, :nested_positive_reference, [:nested_assertion]},
    {:nested_lookbehind_search, :nested_lookbehind_reference, [:mixed_direction_nesting]},
    {:alternate_assertion_search, :alternate_assertion_reference, [:alternation]},
    {:greedy_assertion_search, :contains_b_reference, [:greedy_repetition]},
    {:lazy_assertion_search, :contains_b_reference, [:lazy_repetition]},
    {:possessive_assertion_search, :contains_b_reference, [:possessive_repetition]},
    {:atomic_assertion_search, :always_false_reference, [:atomic_in_assertion]},
    {:negative_atomic_assertion_search, :contains_abc_reference, [:negative_atomic_in_assertion]},
    {:assertion_atomic_search, :always_false_reference, [:assertion_in_atomic]},
    {:anchored_assertion_search, :starts_with_ab_reference, [:subject_anchor]},
    {:boundary_assertion_search, :starts_with_a_reference, [:word_boundary]},
    {:scoped_assertion_search, :contains_upper_a_reference, [:scoped_options]},
    {:conditional_assertion_search, :contains_lower_a_or_b_reference, [:capture_conditional]},
    {:positive_full, :positive_full_reference, [:exact_full_match]}
  ]

  setup_all do
    source = """
    mod RegexLookaround
      use Std.Regex

      fn positive_lookahead() -> Bool = matches(/a(?=b)b/, "ab")
      fn positive_lookahead_failure() -> Bool = matches(/a(?=c)b/, "ab")
      fn negative_lookahead() -> Bool = matches(/a(?!c)b/, "ab")
      fn negative_lookahead_failure() -> Bool = matches(/a(?!b)b/, "ab")
      fn positive_lookahead_prefix() -> Bool = matches(/(?=ab)a/, "abc")
      fn nested_negative_lookahead() -> Bool = matches(/(?!(?=b)b)a/, "a")
      fn nested_positive_lookbehind() -> Bool = matches(/(?<=a(?=b))b/, "ab")
      fn nested_negative_lookbehind() -> Bool = matches(/(?<!a(?!b))c/, "abc")
      fn one_scalar_lookbehind() -> Bool = matches(/(?<=a)b/, "ab")
      fn one_scalar_lookbehind_failure() -> Bool = matches(/(?<=c)b/, "ab")
      fn negative_lookbehind() -> Bool = matches(/(?<!c)b/, "ab")
      fn negative_lookbehind_failure() -> Bool = matches(/(?<!a)b/, "ab")
      fn multi_scalar_lookbehind() -> Bool = matches(/(?<=ab)c/, "abc")
      fn unicode_lookahead() -> Bool = matches(/(?=é)é/, "é")
      fn crlf_lookbehind() -> Bool = matches(/(?<=\r\n)c/, "\r\nc")
      fn cursor_search_lookbehind() -> Bool = matches(/(?<=a)b/, "zab")
      fn nullable_lookahead() -> Bool = matches(/(?=a?)a/, "a")
      fn full_parse_lookahead() -> Bool = match parse_full(/a(?=b)b/, "ab")
        Some(_) -> true
        None() -> false
      fn full_parse_lookahead_failure() -> Bool = match parse_full(/a(?=c)b/, "ab")
        Some(_) -> true
        None() -> false
      fn lookbehind_at_subject_start() -> Bool = matches(/(?<=a)b/, "b")
      fn zero_width_prefix() -> Bool = matches(/(?=a)a/, "a")
      fn lookbehind_subject_anchor() -> Bool = matches(/(?<=^a)b/, "ab")
      fn lookbehind_subject_anchor_failure() -> Bool = matches(/(?<=^a)b/, "zab")
      fn lookbehind_end_anchor_failure() -> Bool = matches(/(?<=a$)b/, "ab")
      fn lookbehind_word_boundary() -> Bool = matches(/(?<=\\ba)b/, "ab")
      fn lookbehind_word_boundary_failure() -> Bool = matches(/(?<=\\ba)b/, "zab")
      fn named_lookahead() -> Bool = match search_named(/(?<x>a)(?=b)/, "ab")
        Some(_) -> true
        None() -> false
      fn positive_search(input: String) -> Bool = matches(/(?=ab)a/, input)
      fn negative_search(input: String) -> Bool = matches(/(?!ab)a/, input)
      fn nested_positive_search(input: String) -> Bool = matches(/(?=a(?=b))a/, input)
      fn nested_negative_search(input: String) -> Bool = matches(/(?!a(?=b))a/, input)
      fn nested_lookbehind_search(input: String) -> Bool = matches(/(?<=a(?=b))b/, input)
      fn atomic_inside_lookahead() -> Bool = matches(/(?=(?>a|ab)c)abc/, "abc")
      fn assertion_inside_atomic() -> Bool = matches(/(?>a(?=b)|ab)c/, "abc")
      fn scoped_caseless() -> Bool = matches(/a(?i:b)c/, "aBc")
      fn scoped_caseless_does_not_leak() -> Bool = matches(/a(?i:b)c/, "aBC")
      fn scoped_caseless_remove() -> Bool = matches(/(?i:(?-i:a))/, "A")
      fn scoped_assertion_caseless() -> Bool = matches(/a(?=(?i:b))B/, "aB")
      fn lookbehind_search(input: String) -> Bool = matches(/(?<=ab)c/, input)
      fn negative_lookbehind_search(input: String) -> Bool = matches(/(?<!ab)c/, input)
      fn positive_full(input: String) -> Bool = match parse_full(/a(?=b)b/, input)
        Some(_) -> true
        None() -> false
      fn alternate_assertion_search(input: String) -> Bool = matches(/(?=(a|b)c)[ab]c/, input)
      fn greedy_assertion_search(input: String) -> Bool = matches(/(?=a*b)a*b/, input)
      fn lazy_assertion_search(input: String) -> Bool = matches(/(?=a*?b)a*?b/, input)
      fn possessive_assertion_search(input: String) -> Bool = matches(/(?=a*+b)a*b/, input)
      fn atomic_assertion_search(input: String) -> Bool = matches(/(?=(?>a|ab)c)abc/, input)
      fn negative_atomic_assertion_search(input: String) -> Bool = matches(/(?!(?>a|ab)c)abc/, input)
      fn assertion_atomic_search(input: String) -> Bool = matches(/(?>a(?=b)|ab)c/, input)
      fn anchored_assertion_search(input: String) -> Bool = matches(/(?=^ab)ab/, input)
      fn boundary_assertion_search(input: String) -> Bool = matches(/(?=\\ba)a/, input)
      fn scoped_assertion_search(input: String) -> Bool = matches(/(?=(?i:a))A/, input)
      fn conditional_assertion_search(input: String) -> Bool = matches(/(?=(a)?)(?(1)a|b)/, input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "positive and negative lookahead are zero-width assertions", %{runtime_module: module} do
    assert apply(module, :positive_lookahead, [])
    refute apply(module, :positive_lookahead_failure, [])
    assert apply(module, :negative_lookahead, [])
    refute apply(module, :negative_lookahead_failure, [])
    assert apply(module, :positive_lookahead_prefix, [])
    assert apply(module, :nested_negative_lookahead, [])
  end

  test "atomic scopes and assertions preserve ordered commitment", %{runtime_module: module} do
    refute apply(module, :atomic_inside_lookahead, [])
    refute apply(module, :assertion_inside_atomic, [])
  end

  test "scoped modifiers stay local, including inside assertions", %{runtime_module: module} do
    assert apply(module, :scoped_caseless, [])
    refute apply(module, :scoped_caseless_does_not_leak, [])
    refute apply(module, :scoped_caseless_remove, [])
    assert apply(module, :scoped_assertion_caseless, [])
  end

  test "lookbehind checks the bounded subject history", %{runtime_module: module} do
    assert apply(module, :one_scalar_lookbehind, [])
    refute apply(module, :one_scalar_lookbehind_failure, [])
    assert apply(module, :negative_lookbehind, [])
    refute apply(module, :negative_lookbehind_failure, [])
    assert apply(module, :multi_scalar_lookbehind, [])
    assert apply(module, :nested_positive_lookbehind, [])
    assert apply(module, :nested_negative_lookbehind, [])
    assert apply(module, :unicode_lookahead, [])
    assert apply(module, :crlf_lookbehind, [])
    assert apply(module, :cursor_search_lookbehind, [])
    assert apply(module, :nullable_lookahead, [])
    assert apply(module, :full_parse_lookahead, [])
    refute apply(module, :full_parse_lookahead_failure, [])
    refute apply(module, :lookbehind_at_subject_start, [])
    assert apply(module, :lookbehind_subject_anchor, [])
    refute apply(module, :lookbehind_subject_anchor_failure, [])
    refute apply(module, :lookbehind_end_anchor_failure, [])
    assert apply(module, :lookbehind_word_boundary, [])
    refute apply(module, :lookbehind_word_boundary_failure, [])
    assert apply(module, :named_lookahead, [])
  end

  test "a successful assertion alone does not consume input", %{runtime_module: module} do
    assert apply(module, :zero_width_prefix, [])
  end

  test "lookaround validation keeps structured diagnostics" do
    cases = [
      {"(?<=a*)b", :VariableLengthLookbehind},
      {"(?=(?=(?=(?=(?=a)))))a", :NestedAssertionDepthExceeded},
      {"(?<=aaaaaaaaa)b", :LookbehindTooWide}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod InvalidLookaround\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta, {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}},
               _context} = _reason} =
               Cure.Elab.Program.elaborate(source),
             "expected #{inspect(pattern)} to reject as #{inspect(expected)}"
    end)
  end

  test "positive lookahead captures are published in the surrounding named frame" do
    source = """
    mod AssertionCapturePublication
      use Std.Regex

      fn run(input: String) -> Option(NamedParse(Tuple(Unit, Unit))) =
        parse_full_named(/(?=(?<ahead>a))a/, input)

      fn negative(input: String) -> Option(NamedParse(Tuple(Unit, Unit))) =
        parse_full_named(/(?!(?<blocked>a))b/, input)

    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert {:some, {:NamedParse, {:unit, :unit}, captures}} =
             apply(module, :run, [{:String, ~c"a"}])

    assert captures == [{:NamedCapture, {:String, ~c"ahead"}, {:some, {:String, ~c"a"}}}]

    assert {:some, {:NamedParse, {:unit, :unit}, negative_captures}} =
             apply(module, :negative, [{:String, ~c"b"}])

    assert negative_captures == [{:NamedCapture, {:String, ~c"blocked"}, :none}]
    assert apply(module, :negative, [{:String, ~c"a"}]) == :none
  end

  test "assertion capture backtracking discards failed alternatives" do
    source = """
    mod AssertionCaptureBacktracking
      use Std.Regex

      fn run(input: String) -> Option(String) =
        match search_named(/(?=(?<ahead>a|b))b/, input)
          None() -> None()
          Some(found) -> named_capture("ahead", found)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :run, [{:String, ~c"b"}]) == {:some, {:String, ~c"b"}}
    assert apply(module, :run, [{:String, ~c"a"}]) == :none
  end

  defp chars_gen(0), do: Gen.return([])

  defp chars_gen(size) do
    Gen.bind(Gen.member_of(~c"abc"), fn head ->
      Gen.bind(chars_gen(size - 1), fn tail -> Gen.return([head | tail]) end)
    end)
  end

  defp lookaround_case_gen do
    Gen.bind(Gen.integer(0, 6), fn size ->
      Gen.bind(chars_gen(size), fn input -> Gen.return(input) end)
    end)
  end

  defp contains_at?(input, needle, index) do
    Enum.slice(input, index, length(needle)) == needle
  end

  defp positive_reference(input), do: Enum.any?(0..length(input), &contains_at?(input, ~c"ab", &1))

  defp negative_reference(input) do
    input
    |> Enum.with_index()
    |> Enum.any?(fn {char, index} -> char == ?a and not contains_at?(input, ~c"ab", index) end)
  end

  defp lookbehind_reference(input), do: Enum.any?(0..length(input), &contains_at?(input, ~c"abc", &1))

  defp negative_lookbehind_reference(input) do
    input
    |> Enum.with_index()
    |> Enum.any?(fn {char, index} ->
      char == ?c and (index < 2 or Enum.slice(input, index - 2, 2) != ~c"ab")
    end)
  end

  defp nested_positive_reference(input), do: Enum.any?(0..length(input), &contains_at?(input, ~c"ab", &1))

  defp nested_negative_reference(input) do
    input
    |> Enum.with_index()
    |> Enum.any?(fn {char, index} -> char == ?a and not contains_at?(input, ~c"ab", index) end)
  end

  defp nested_lookbehind_reference(input) do
    input
    |> Enum.with_index()
    |> Enum.any?(fn {char, index} -> char == ?b and index > 0 and contains_at?(input, ~c"ab", index - 1) end)
  end

  defp alternate_assertion_reference(input) do
    Enum.any?(0..length(input), fn index ->
      contains_at?(input, ~c"ac", index) or contains_at?(input, ~c"bc", index)
    end)
  end

  defp contains_b_reference(input), do: ?b in input
  defp always_false_reference(_input), do: false
  defp starts_with_ab_reference(input), do: Enum.take(input, 2) == ~c"ab"
  defp starts_with_a_reference(input), do: List.first(input) == ?a
  defp contains_upper_a_reference(input), do: ?A in input
  defp contains_abc_reference(input), do: Enum.any?(0..length(input), &contains_at?(input, ~c"abc", &1))
  defp contains_lower_a_or_b_reference(input), do: Enum.any?(input, &(&1 in ~c"ab"))
  defp positive_full_reference(input), do: input == ~c"ab"

  test "lookaround search and full parsing agree with an independent finite reference", %{runtime_module: module} do
    assert :ok =
             Property.check_all(lookaround_case_gen(), @runs, fn input ->
               subject = {:String, input}

               apply(module, :positive_search, [subject]) == positive_reference(input) and
                 apply(module, :negative_search, [subject]) == negative_reference(input) and
                 apply(module, :nested_positive_search, [subject]) == nested_positive_reference(input) and
                 apply(module, :nested_negative_search, [subject]) == nested_negative_reference(input) and
                 apply(module, :nested_lookbehind_search, [subject]) == nested_lookbehind_reference(input) and
                 apply(module, :lookbehind_search, [subject]) == lookbehind_reference(input) and
                 apply(module, :negative_lookbehind_search, [subject]) == negative_lookbehind_reference(input) and
                 apply(module, :positive_full, [subject]) == (input == ~c"ab")
             end)
  end

  test "admitted nested lookarounds agree exhaustively on the bounded model", %{runtime_module: module} do
    for input <- small_words(4) do
      subject = {:String, input}

      assert apply(module, :positive_search, [subject]) == positive_reference(input),
             "positive lookahead mismatch for #{inspect(input)}"

      assert apply(module, :negative_search, [subject]) == negative_reference(input),
             "negative lookahead mismatch for #{inspect(input)}"

      assert apply(module, :nested_positive_search, [subject]) == nested_positive_reference(input),
             "nested positive lookahead mismatch for #{inspect(input)}"

      assert apply(module, :nested_negative_search, [subject]) == nested_negative_reference(input),
             "nested negative lookahead mismatch for #{inspect(input)}"

      assert apply(module, :nested_lookbehind_search, [subject]) ==
               nested_lookbehind_reference(input),
             "nested lookbehind mismatch for #{inspect(input)}"

      assert apply(module, :lookbehind_search, [subject]) == lookbehind_reference(input),
             "lookbehind mismatch for #{inspect(input)}"

      assert apply(module, :negative_lookbehind_search, [subject]) ==
               negative_lookbehind_reference(input),
             "negative lookbehind mismatch for #{inspect(input)}"

      assert apply(module, :positive_full, [subject]) == (input == ~c"ab"),
             "full assertion parse mismatch for #{inspect(input)}"
    end

    assert length(small_words(4)) == 121
  end

  test "every admitted assertion machine shape has an exhaustive independent oracle", %{
    runtime_module: module
  } do
    covered_shapes =
      @admitted_shape_cases
      |> Enum.flat_map(fn {_runtime, _reference, shapes} -> shapes end)
      |> Enum.uniq()
      |> Enum.sort()

    assert covered_shapes == Enum.sort(@admitted_assertion_shapes)

    for {runtime, reference, shapes} <- @admitted_shape_cases,
        input <- admitted_words(3) do
      subject = {:String, input}

      assert apply(module, runtime, [subject]) == reference_result(reference, input),
             "#{inspect(shapes)} case #{runtime} disagreed for #{inspect(input)}"
    end

    assert length(admitted_words(3)) == 85
  end

  defp small_words(max_length) do
    for length <- 0..max_length,
        word <- words_of_length(length),
        do: word
  end

  defp words_of_length(0), do: [[]]

  defp words_of_length(length) do
    for prefix <- words_of_length(length - 1), char <- ~c"abc", do: prefix ++ [char]
  end

  defp admitted_words(max_length) do
    for length <- 0..max_length,
        word <- admitted_words_of_length(length),
        do: word
  end

  defp admitted_words_of_length(0), do: [[]]

  defp admitted_words_of_length(length) do
    for prefix <- admitted_words_of_length(length - 1), char <- ~c"abcA", do: prefix ++ [char]
  end

  defp reference_result(:positive_reference, input), do: positive_reference(input)
  defp reference_result(:negative_reference, input), do: negative_reference(input)
  defp reference_result(:lookbehind_reference, input), do: lookbehind_reference(input)
  defp reference_result(:negative_lookbehind_reference, input), do: negative_lookbehind_reference(input)
  defp reference_result(:nested_positive_reference, input), do: nested_positive_reference(input)
  defp reference_result(:nested_lookbehind_reference, input), do: nested_lookbehind_reference(input)
  defp reference_result(:alternate_assertion_reference, input), do: alternate_assertion_reference(input)
  defp reference_result(:contains_b_reference, input), do: contains_b_reference(input)
  defp reference_result(:always_false_reference, input), do: always_false_reference(input)
  defp reference_result(:starts_with_ab_reference, input), do: starts_with_ab_reference(input)
  defp reference_result(:starts_with_a_reference, input), do: starts_with_a_reference(input)
  defp reference_result(:contains_upper_a_reference, input), do: contains_upper_a_reference(input)
  defp reference_result(:contains_abc_reference, input), do: contains_abc_reference(input)

  defp reference_result(:contains_lower_a_or_b_reference, input),
    do: contains_lower_a_or_b_reference(input)

  defp reference_result(:positive_full_reference, input), do: positive_full_reference(input)
end
