defmodule Cure.Stdlib.DependentRegexExhaustiveModelTest do
  use ExUnit.Case, async: false

  @moduletag timeout: 600_000

  @max_depth 2
  @max_word_length 3
  @batch_size 48

  setup_all do
    patterns = patterns(@max_depth)

    modules =
      patterns
      |> Enum.chunk_every(@batch_size)
      |> Enum.with_index()
      |> Enum.map(fn {batch, index} -> compile_batch(batch, index) end)

    {:ok, modules: modules, patterns: patterns}
  end

  test "all core trees through depth two agree with denotation and evidence", %{modules: modules, patterns: patterns} do
    words = words(@max_word_length)

    for word <- words do
      input = {:String, word}
      accepts = Enum.flat_map(modules, &apply(elem(&1, 0), :all_accepts, [input]))
      evidence = Enum.flat_map(modules, &apply(elem(&1, 0), :all_evidence, [input]))

      expected = Enum.map(patterns, &denotes?(&1, word))

      assert accepts == expected, "acceptance mismatch for #{inspect(word)}"
      assert evidence == expected, "evidence mismatch for #{inspect(word)}"
    end

    assert length(patterns) == 1_515
    assert length(words) == 15
  end

  defp compile_batch(batch, index) do
    module_name = "RegexExhaustiveSmallModel#{index}"

    source = """
    mod #{module_name}
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn evidence_present(value: Option(List(Evidence))) -> Bool = match value
        Some(_) -> true
        None() -> false

      fn all_accepts(input: String) -> List(Bool) = [#{Enum.map_join(batch, ", ", &"pattern_accepts(#{source_pattern(&1)}, input)")}]

      fn all_evidence(input: String) -> List(Bool) = [#{Enum.map_join(batch, ", ", &"evidence_present(pattern_evidence(#{source_pattern(&1)}, Std.String.characters(input)))")}]
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {module, batch}
  end

  defp patterns(0), do: [:empty, {:atom, ?a}, {:atom, ?b}]

  defp patterns(depth) do
    children = patterns(depth - 1)

    leaves = patterns(0)
    unary = for child <- children, constructor <- [:group, :repeat], do: {constructor, child}

    binary =
      for left <- children, right <- children, constructor <- [:concat, :alternate], do: {constructor, left, right}

    leaves ++ unary ++ binary
  end

  defp source_pattern(:empty), do: "PatternEmpty()"
  defp source_pattern({:atom, char}), do: "PatternPredicate(same('#{<<char::utf8>>}'))"
  defp source_pattern({:group, child}), do: "PatternGroup(#{source_pattern(child)})"
  defp source_pattern({:repeat, child}), do: "PatternRepeat(#{source_pattern(child)})"
  defp source_pattern({:concat, left, right}), do: "PatternConcat(#{source_pattern(left)}, #{source_pattern(right)})"

  defp source_pattern({:alternate, left, right}),
    do: "PatternAlternate(#{source_pattern(left)}, #{source_pattern(right)})"

  defp words(max_length) do
    for length <- 0..max_length,
        word <- words_of_length(length),
        do: word
  end

  defp words_of_length(0), do: [[]]

  defp words_of_length(length) do
    for prefix <- words_of_length(length - 1), char <- [?a, ?b], do: prefix ++ [char]
  end

  defp denotes?(:empty, word), do: word == []
  defp denotes?({:atom, char}, word), do: word == [char]
  defp denotes?({:group, child}, word), do: denotes?(child, word)
  defp denotes?({:alternate, left, right}, word), do: denotes?(left, word) or denotes?(right, word)

  defp denotes?({:concat, left, right}, word) do
    Enum.any?(0..length(word), fn split ->
      denotes?(left, Enum.take(word, split)) and denotes?(right, Enum.drop(word, split))
    end)
  end

  defp denotes?({:repeat, child}, word) do
    word == [] or
      Enum.any?(1..length(word), fn split ->
        denotes?(child, Enum.take(word, split)) and denotes?({:repeat, child}, Enum.drop(word, split))
      end)
  end
end
