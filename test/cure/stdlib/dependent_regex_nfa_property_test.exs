defmodule Cure.Stdlib.DependentRegexNfaPropertyTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @runs [max_runs: 500, max_run_time: :infinity]

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so it
  # erases to the tagged pair `{:String, code_points}`. The generators below
  # produce bare charlists, so every subject is wrapped before it crosses into a
  # compiled Cure function.
  #
  # `Std.Regex` splits its two layers on this line: `pattern_accepts` and
  # `parse_pattern_full` take a `String` and convert internally, while the raw
  # evidence machine (`pattern_evidence`) works in code points. The source below
  # therefore converts once, at the `pattern_evidence` calls.
  defp cure_string(chars), do: {:String, chars}

  setup_all do
    source = """
    mod RegexNfaProperties
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn empty() -> Pattern(UnitC) = PatternEmpty()
      fn ab() -> Pattern(PairC(CharC, CharC)) = PatternConcat(atom('a'), atom('b'))
      fn either() -> Pattern(ChoiceC(CharC, CharC)) = PatternAlternate(atom('a'), atom('b'))
      fn many_a() -> Pattern(ListC(CharC)) = PatternRepeat(atom('a'))
      fn many_either() -> Pattern(ListC(ChoiceC(CharC, CharC))) = PatternRepeat(either())
      fn many_a_then_b() -> Pattern(PairC(ListC(CharC), CharC)) = PatternConcat(many_a(), atom('b'))
      fn nullable_choice() -> Pattern(ChoiceC(UnitC, CharC)) = PatternAlternate(empty(), atom('a'))
      fn nullable_star() -> Pattern(ListC(ChoiceC(UnitC, CharC))) = PatternRepeat(nullable_choice())
      fn grouped() -> Pattern(StringC) = PatternGroup(ab())
      fn empty_then_a() -> Pattern(PairC(UnitC, CharC)) = PatternConcat(empty(), atom('a'))

      fn accepts(kind: Int, input: String) -> Bool = pickup
        kind == 0 -> pattern_accepts(empty(), input)
        kind == 1 -> pattern_accepts(atom('a'), input)
        kind == 2 -> pattern_accepts(ab(), input)
        kind == 3 -> pattern_accepts(either(), input)
        kind == 4 -> pattern_accepts(many_a(), input)
        kind == 5 -> pattern_accepts(many_either(), input)
        kind == 6 -> pattern_accepts(many_a_then_b(), input)
        kind == 7 -> pattern_accepts(nullable_star(), input)
        kind == 8 -> pattern_accepts(grouped(), input)
        else -> pattern_accepts(empty_then_a(), input)

      fn evidence_present(value: Option(List(Evidence))) -> Bool = match value
        Some(_) -> true
        None() -> false

      fn has_evidence(kind: Int, input: String) -> Bool = pickup
        kind == 0 -> evidence_present(pattern_evidence(empty(), Std.String.characters(input)))
        kind == 1 -> evidence_present(pattern_evidence(atom('a'), Std.String.characters(input)))
        kind == 2 -> evidence_present(pattern_evidence(ab(), Std.String.characters(input)))
        kind == 3 -> evidence_present(pattern_evidence(either(), Std.String.characters(input)))
        kind == 4 -> evidence_present(pattern_evidence(many_a(), Std.String.characters(input)))
        kind == 5 -> evidence_present(pattern_evidence(many_either(), Std.String.characters(input)))
        kind == 6 -> evidence_present(pattern_evidence(many_a_then_b(), Std.String.characters(input)))
        kind == 7 -> evidence_present(pattern_evidence(nullable_star(), Std.String.characters(input)))
        kind == 8 -> evidence_present(pattern_evidence(grouped(), Std.String.characters(input)))
        else -> evidence_present(pattern_evidence(empty_then_a(), Std.String.characters(input)))

      fn legacy_pattern_evidence({shape: ShapeCode}, pattern: Pattern(shape), input: List(Char)) -> Option(List(Evidence)) = match compile_pattern(pattern)
        mk_pair(_count, MkPatternMachine(starts, next)) ->
          run_evidence(next, input, distinct_threads(initial_threads(filter_boundary_states(starts, position_boundary(true, true, false, false, None(), input)))))

      fn current_evidence(kind: Int, input: String) -> Option(List(Evidence)) = pickup
        kind == 0 -> pattern_evidence(empty(), Std.String.characters(input))
        kind == 1 -> pattern_evidence(atom('a'), Std.String.characters(input))
        kind == 2 -> pattern_evidence(ab(), Std.String.characters(input))
        kind == 3 -> pattern_evidence(either(), Std.String.characters(input))
        kind == 4 -> pattern_evidence(many_a(), Std.String.characters(input))
        kind == 5 -> pattern_evidence(many_either(), Std.String.characters(input))
        kind == 6 -> pattern_evidence(many_a_then_b(), Std.String.characters(input))
        kind == 7 -> pattern_evidence(nullable_star(), Std.String.characters(input))
        kind == 8 -> pattern_evidence(grouped(), Std.String.characters(input))
        else -> pattern_evidence(empty_then_a(), Std.String.characters(input))

      fn legacy_evidence(kind: Int, input: String) -> Option(List(Evidence)) = pickup
        kind == 0 -> legacy_pattern_evidence(empty(), Std.String.characters(input))
        kind == 1 -> legacy_pattern_evidence(atom('a'), Std.String.characters(input))
        kind == 2 -> legacy_pattern_evidence(ab(), Std.String.characters(input))
        kind == 3 -> legacy_pattern_evidence(either(), Std.String.characters(input))
        kind == 4 -> legacy_pattern_evidence(many_a(), Std.String.characters(input))
        kind == 5 -> legacy_pattern_evidence(many_either(), Std.String.characters(input))
        kind == 6 -> legacy_pattern_evidence(many_a_then_b(), Std.String.characters(input))
        kind == 7 -> legacy_pattern_evidence(nullable_star(), Std.String.characters(input))
        kind == 8 -> legacy_pattern_evidence(grouped(), Std.String.characters(input))
        else -> legacy_pattern_evidence(empty_then_a(), Std.String.characters(input))

      fn legacy_prefix({shape: ShapeCode}, pattern: Pattern(shape), input: List(Char), greedy: Bool) -> Option(EvidencePrefix) = match compile_pattern(pattern)
        mk_pair(_count, MkPatternMachine(starts, next)) ->
          let threads = distinct_threads(initial_threads(filter_boundary_states(starts, position_boundary(true, true, false, false, None(), input))))
          pickup
            greedy -> run_last_prefix_evidence(next, input, threads, None())
            else -> run_first_prefix_evidence(next, input, threads)

      fn current_prefix(kind: Int, input: String, greedy: Bool) -> Option(EvidencePrefix) = pickup
        kind == 0 -> pattern_prefix_evidence(empty(), Std.String.characters(input), greedy)
        kind == 1 -> pattern_prefix_evidence(atom('a'), Std.String.characters(input), greedy)
        kind == 2 -> pattern_prefix_evidence(ab(), Std.String.characters(input), greedy)
        kind == 3 -> pattern_prefix_evidence(either(), Std.String.characters(input), greedy)
        kind == 4 -> pattern_prefix_evidence(many_a(), Std.String.characters(input), greedy)
        kind == 5 -> pattern_prefix_evidence(many_either(), Std.String.characters(input), greedy)
        kind == 6 -> pattern_prefix_evidence(many_a_then_b(), Std.String.characters(input), greedy)
        kind == 7 -> pattern_prefix_evidence(nullable_star(), Std.String.characters(input), greedy)
        kind == 8 -> pattern_prefix_evidence(grouped(), Std.String.characters(input), greedy)
        else -> pattern_prefix_evidence(empty_then_a(), Std.String.characters(input), greedy)

      fn legacy_prefix_for(kind: Int, input: String, greedy: Bool) -> Option(EvidencePrefix) = pickup
        kind == 0 -> legacy_prefix(empty(), Std.String.characters(input), greedy)
        kind == 1 -> legacy_prefix(atom('a'), Std.String.characters(input), greedy)
        kind == 2 -> legacy_prefix(ab(), Std.String.characters(input), greedy)
        kind == 3 -> legacy_prefix(either(), Std.String.characters(input), greedy)
        kind == 4 -> legacy_prefix(many_a(), Std.String.characters(input), greedy)
        kind == 5 -> legacy_prefix(many_either(), Std.String.characters(input), greedy)
        kind == 6 -> legacy_prefix(many_a_then_b(), Std.String.characters(input), greedy)
        kind == 7 -> legacy_prefix(nullable_star(), Std.String.characters(input), greedy)
        kind == 8 -> legacy_prefix(grouped(), Std.String.characters(input), greedy)
        else -> legacy_prefix(empty_then_a(), Std.String.characters(input), greedy)

      fn parsed({value: Type}, result: Option(value)) -> Bool = match result
        Some(_) -> true
        None() -> false

      fn parses(kind: Int, input: String) -> Bool = pickup
        kind == 0 -> parsed(parse_pattern_full(empty(), input))
        kind == 1 -> parsed(parse_pattern_full(atom('a'), input))
        kind == 2 -> parsed(parse_pattern_full(ab(), input))
        kind == 3 -> parsed(parse_pattern_full(either(), input))
        kind == 4 -> parsed(parse_pattern_full(many_a(), input))
        kind == 5 -> parsed(parse_pattern_full(many_either(), input))
        kind == 6 -> parsed(parse_pattern_full(many_a_then_b(), input))
        kind == 7 -> parsed(parse_pattern_full(nullable_star(), input))
        kind == 8 -> parsed(parse_pattern_full(grouped(), input))
        else -> parsed(parse_pattern_full(empty_then_a(), input))
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  defp chars_gen(0), do: Gen.return([])

  defp chars_gen(size) do
    Gen.bind(Gen.member_of(~c"abc"), fn head ->
      Gen.bind(chars_gen(size - 1), fn tail -> Gen.return([head | tail]) end)
    end)
  end

  defp case_gen do
    Gen.bind(Gen.integer(0, 9), fn kind ->
      Gen.bind(Gen.integer(0, 8), fn size ->
        Gen.bind(chars_gen(size), fn input -> Gen.return({kind, input}) end)
      end)
    end)
  end

  defp reference(0, input), do: input == []
  defp reference(1, input), do: input == ~c"a"
  defp reference(2, input), do: input == ~c"ab"
  defp reference(3, input), do: input in [~c"a", ~c"b"]
  defp reference(4, input), do: Enum.all?(input, &(&1 == ?a))
  defp reference(5, input), do: Enum.all?(input, &(&1 in ~c"ab"))
  defp reference(6, input), do: input != [] and List.last(input) == ?b and Enum.all?(Enum.drop(input, -1), &(&1 == ?a))
  defp reference(7, input), do: Enum.all?(input, &(&1 == ?a))
  defp reference(8, input), do: input == ~c"ab"
  defp reference(9, input), do: input == ~c"a"

  test "Thompson acceptance agrees with structural denotation on generated words", %{runtime_module: module} do
    assert :ok =
             Property.check_all(case_gen(), @runs, fn {kind, input} ->
               accepted = apply(module, :accepts, [kind, cure_string(input)])

               accepted == reference(kind, input) and
                 apply(module, :has_evidence, [kind, cure_string(input)]) == accepted and
                 apply(module, :parses, [kind, cure_string(input)]) == accepted
             end)
  end

  test "all small words agree for every representative constructor tree", %{runtime_module: module} do
    words =
      for size <- 0..5,
          word <-
            List.duplicate(~c"ab", size)
            |> List.foldl([[]], fn alphabet, words -> for c <- alphabet, w <- words, do: [c | w] end),
          do: Enum.reverse(word)

    for kind <- 0..9, input <- words do
      assert apply(module, :accepts, [kind, cure_string(input)]) == reference(kind, input),
             "kind=#{kind} input=#{inspect(input)}"

      assert apply(module, :has_evidence, [kind, cure_string(input)]) == reference(kind, input),
             "evidence kind=#{kind} input=#{inspect(input)}"

      assert apply(module, :parses, [kind, cure_string(input)]) == reference(kind, input),
             "typed parse kind=#{kind} input=#{inspect(input)}"
    end
  end

  test "certified execution replays the legacy winner's exact evidence", %{runtime_module: module} do
    assert :ok =
             Property.check_all(case_gen(), @runs, fn {kind, input} ->
               subject = cure_string(input)

               apply(module, :current_evidence, [kind, subject]) ==
                 apply(module, :legacy_evidence, [kind, subject]) and
                 apply(module, :current_prefix, [kind, subject, false]) ==
                   apply(module, :legacy_prefix_for, [kind, subject, false]) and
                 apply(module, :current_prefix, [kind, subject, true]) ==
                   apply(module, :legacy_prefix_for, [kind, subject, true])
             end)
  end
end
