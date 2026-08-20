defmodule Cure.Stdlib.DependentRegexLookaroundTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @runs [max_runs: 200, max_run_time: :infinity]

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
      {"(?<=(a))b", :AssertionCapturesUnsupported},
      {"(?=(?=(?=(?=(?=a)))))a", :NestedAssertionDepthExceeded},
      {"(?<=aaaaaaaaa)b", :LookbehindTooWide}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod InvalidLookaround\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context} = _reason} =
               Cure.Elab.Program.elaborate(source),
             "expected #{inspect(pattern)} to reject as #{inspect(expected)}"
    end)
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
end
