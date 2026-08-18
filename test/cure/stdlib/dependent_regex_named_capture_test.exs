defmodule Cure.Stdlib.DependentRegexNamedCaptureTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  setup_all do
    source = ~S'''
    mod RegexNamedCaptures
      use Std.Regex

      fn parsed(input: String) -> Option(NamedParse(String)) =
        parse_full_named(/(?<word>ab)/, input)

      fn flat(input: String) -> Option(NamedMatch(String)) =
        search_named(/(?<word>ab)/, input)

      fn quoted(input: String) -> Option(NamedMatch(String)) =
        search_named(/(?'word'ab)/, input)

      fn python_style(input: String) -> Option(NamedMatch(String)) =
        search_named(/(?P<word>ab)/, input)

      fn nested(input: String) -> Option(NamedMatch(String)) =
        search_named(/(?<outer>(?<inner>é+))/u, input)

      fn alternate(input: String) -> Option(NamedMatch(Choice(String, String))) =
        search_named(/(?<left>a)|(?<right>b)/, input)

      fn empty(input: String) -> Option(NamedMatch(String)) =
        search_named(/(?<empty>)/, input)

      fn repeated(input: String) -> Option(NamedMatch(List(String))) =
        search_named(/(?<item>a)+/, input)

      fn branch_reset(input: String) -> Option(NamedMatch(Choice(String, String))) =
        search_named(/(?|(?<word>a)|(?<word>b))/, input)

      fn branch_reset_empty(input: String) -> Option(NamedMatch(Choice(String, String))) =
        search_named(/(?|(?<word>)|(?<word>a))/, input)

      fn branch_reset_nested(input: String) -> Option(NamedMatch(Choice(Choice(String, String), Choice(String, String)))) =
        search_named(/(?|(?|(?<word>a)|(?<word>b))|(?|(?<word>c)|(?<word>d)))/, input)

      fn conditional(input: String) -> Option(NamedParse(Tuple(Option(String), Choice(Unit, Unit)))) =
        parse_full_named(/(?<flag>a)?(?(1)b|c)/, input)

      fn named_conditional(input: String) -> Option(NamedParse(Tuple(Option(String), Choice(Unit, Unit)))) =
        parse_full_named(/(?<flag>a)?(?(<flag>)b|c)/, input)

      fn conditional_search(input: String) -> Option(NamedMatch(Tuple(Option(String), Choice(Unit, Unit)))) =
        search_named(/(?<flag>a)?(?(1)b|c)/, input)

      fn conditional_empty(input: String) -> Option(NamedParse(Tuple(String, Choice(Unit, Unit)))) =
        parse_full_named(/(?<flag>)(?(flag)a|b)/, input)

      fn conditional_failed_capture(input: String) -> Option(NamedParse(Tuple(Choice(Tuple(String, Unit), Unit), Choice(Unit, Unit)))) =
        parse_full_named(/(?:(?<flag>a)x|a)(?(flag)b|c)/, input)

      fn replay_probe() -> Option(List(NamedCapture)) =
        replay_named_capture_routine(
          [Regular(BeginCaptureSlot(Z())), Observe('a'), Regular(EndCaptureSlot(Z()))],
          CaptureLayout([CaptureSlot(Z(), Some("probe"))])
        )
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "named captures preserve full-match parsing", %{runtime_module: module} do
    assert {:some, {:NamedParse, {:String, ~c"ab"}, [{:NamedCapture, {:String, ~c"word"}, {:some, {:String, ~c"ab"}}}]}} =
             apply(module, :parsed, [{:String, ~c"ab"}])

    assert apply(module, :parsed, [{:String, ~c"ac"}]) == :none
  end

  test "the named replay records observed characters", %{runtime_module: module} do
    assert apply(module, :replay_probe, []) ==
             {:some, [{:NamedCapture, {:String, ~c"probe"}, {:some, {:String, ~c"a"}}}]}
  end

  test "flat named capture returns its text", %{runtime_module: module} do
    assert {:some, {:NamedMatch, _match, captures}} = apply(module, :flat, [{:String, ~c"xxabyy"}])
    assert captures == [{:NamedCapture, {:String, ~c"word"}, {:some, {:String, ~c"ab"}}}]
  end

  test "all PCRE named-capture spellings normalize to the same layout", %{runtime_module: module} do
    for name <- [:quoted, :python_style] do
      assert {:some, {:NamedMatch, _match, captures}} = apply(module, name, [{:String, ~c"ab"}])
      assert captures == [{:NamedCapture, {:String, ~c"word"}, {:some, {:String, ~c"ab"}}}]
    end
  end

  test "nested, alternate, empty, and repeated captures have explicit participation", %{runtime_module: module} do
    assert {:some, {:NamedMatch, _match, nested}} = apply(module, :nested, [{:String, [0xE9]}])

    assert nested == [
             {:NamedCapture, {:String, ~c"outer"}, {:some, {:String, [0xE9]}}},
             {:NamedCapture, {:String, ~c"inner"}, {:some, {:String, [0xE9]}}}
           ]

    assert {:some, {:NamedMatch, _match, left}} = apply(module, :alternate, [{:String, ~c"a"}])

    assert left == [
             {:NamedCapture, {:String, ~c"left"}, {:some, {:String, ~c"a"}}},
             {:NamedCapture, {:String, ~c"right"}, :none}
           ]

    assert {:some, {:NamedMatch, _match, right}} = apply(module, :alternate, [{:String, ~c"b"}])

    assert right == [
             {:NamedCapture, {:String, ~c"left"}, :none},
             {:NamedCapture, {:String, ~c"right"}, {:some, {:String, ~c"b"}}}
           ]

    assert {:some, {:NamedMatch, _match, empty}} = apply(module, :empty, [{:String, ~c""}])
    assert empty == [{:NamedCapture, {:String, ~c"empty"}, {:some, {:String, []}}}]

    assert {:some, {:NamedMatch, _match, repeated}} = apply(module, :repeated, [{:String, ~c"aaa"}])
    assert repeated == [{:NamedCapture, {:String, ~c"item"}, {:some, {:String, ~c"a"}}}]
  end

  test "branch reset reuses the corresponding named slot", %{runtime_module: module} do
    assert {:some, {:NamedMatch, _match, captures}} = apply(module, :branch_reset, [{:String, ~c"b"}])
    assert captures == [{:NamedCapture, {:String, ~c"word"}, {:some, {:String, ~c"b"}}}]
  end

  test "nested branch reset preserves the nested result shape and shared slot", %{runtime_module: module} do
    assert {:some, {:NamedMatch, _match, captures}} = apply(module, :branch_reset_nested, [{:String, ~c"d"}])
    assert captures == [{:NamedCapture, {:String, ~c"word"}, {:some, {:String, ~c"d"}}}]
  end

  test "branch reset rejects arms with different capture layouts" do
    source = "mod BadBranchReset\n  use Std.Regex\n  fn run() = /(?|(a)|(b)(c))/\nend\n"

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta,
              {:author_diagnostics, [{:macro_failure, :BranchResetCaptureLayoutMismatch, _}]}}, _context}} =
             Program.elaborate(source)
  end

  test "capture conditionals select the arm from participation", %{runtime_module: module} do
    assert {:some, {:NamedParse, _value, captures}} = apply(module, :conditional, [{:String, ~c"ab"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, {:some, {:String, ~c"a"}}}]

    assert {:some, {:NamedParse, _value, captures}} = apply(module, :conditional, [{:String, ~c"c"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, :none}]
    assert apply(module, :conditional, [{:String, ~c"ac"}]) == :none
    assert apply(module, :conditional, [{:String, ~c"b"}]) == :none

    assert {:some, {:NamedParse, _value, captures}} = apply(module, :named_conditional, [{:String, ~c"ab"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, {:some, {:String, ~c"a"}}}]
  end

  test "capture conditionals also work through named search", %{runtime_module: module} do
    assert {:some, {:NamedMatch, _match, captures}} = apply(module, :conditional_search, [{:String, ~c"xxabyy"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, {:some, {:String, ~c"a"}}}]
  end

  test "empty captures participate in conditionals", %{runtime_module: module} do
    assert {:some, {:NamedParse, _value, captures}} = apply(module, :conditional_empty, [{:String, ~c"a"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, {:some, {:String, []}}}]
    assert apply(module, :conditional_empty, [{:String, ~c"b"}]) == :none
  end

  test "failed alternatives do not leak conditional participation", %{runtime_module: module} do
    assert {:some, {:NamedParse, _value, captures}} = apply(module, :conditional_failed_capture, [{:String, ~c"ac"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, :none}]
    assert apply(module, :conditional_failed_capture, [{:String, ~c"ab"}]) == :none

    assert {:some, {:NamedParse, _value, captures}} = apply(module, :conditional_failed_capture, [{:String, ~c"axb"}])
    assert captures == [{:NamedCapture, {:String, ~c"flag"}, {:some, {:String, ~c"a"}}}]
  end

  test "unknown conditional capture references are diagnosed" do
    missing = "mod BadConditional\n  use Std.Regex\n  fn run() = /(?(missing)a)/\nend\n"

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta,
              {:author_diagnostics, [{:macro_failure, :UnknownRegexCaptureReference, _}]}}, _context}} =
             Program.elaborate(missing)
  end

  test "conditional arms with different capture layouts are diagnosed" do
    source = "mod BadConditionalLayout\n  use Std.Regex\n  fn run() = /(?<flag>a)?(?(flag)(b)|(c)(d))/\nend\n"

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta,
              {:author_diagnostics, [{:macro_failure, :ConditionalCaptureLayoutMismatch, _}]}}, _context}} =
             Program.elaborate(source)
  end

  test "malformed and duplicate names are structured macro diagnostics" do
    cases = [
      {~S"(?<>)", :EmptyRegexCaptureName},
      {~S"(?<1word>a)", :MalformedRegexCaptureName},
      {~S"(?<word>a)(?<word>b)", :DuplicateRegexCaptureName},
      {~S"(?<word>a", :UnclosedRegexGroup}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod BadNamedCapture\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta, {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}},
               _context}} =
               Program.elaborate(source)
    end)
  end
end
