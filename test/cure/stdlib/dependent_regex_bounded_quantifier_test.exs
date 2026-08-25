defmodule Cure.Stdlib.DependentRegexBoundedQuantifierTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program
  alias Cure.Compiler.Errors

  setup_all do
    source = ~S'''
    mod RegexBoundedQuantifiers
      use Std.Regex

      fn exact(input: String) -> Option(Nat) = parse_full(/a{3}/, input)
      fn at_least(input: String) -> Option(Nat) = parse_full(/a{2,}/, input)
      fn ranged(input: String) -> Option(Nat) = parse_full(/a{2,4}/, input)
      fn ranged_lazy(input: String) -> Option(Tuple(Nat, String)) = parse_full(/a{2,4}?(a*)/, input)
      fn captured_exact(input: String) -> Option(List(String)) = parse_full(/(a){2}/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "exact, lower-bounded, ranged, and lazy quantifiers preserve list shape", %{runtime_module: module} do
    assert apply(module, :exact, [{:String, ~c"aaa"}]) == {:some, 3}
    assert apply(module, :exact, [{:String, ~c"aa"}]) == :none
    assert apply(module, :at_least, [{:String, ~c"aaaa"}]) == {:some, 4}
    assert apply(module, :ranged, [{:String, ~c"aaaa"}]) == {:some, 4}
    assert apply(module, :ranged, [{:String, ~c"aaaaa"}]) == :none

    assert apply(module, :ranged_lazy, [{:String, ~c"aaaaa"}]) ==
             {:some, {2, {:String, ~c"aaa"}}}

    assert apply(module, :captured_exact, [{:String, ~c"aa"}]) ==
             {:some, [{:String, ~c"a"}, {:String, ~c"a"}]}
  end

  test "malformed bounded quantifiers reject with dedicated structured reasons" do
    cases = [
      {"a{}", :MissingRegexQuantifierMinimum, "{}"},
      {"a{,3}", :MissingRegexQuantifierMinimum, "{,3}"},
      {"a{3,2}", :RegexQuantifierRangeReversed, "{3,2}"},
      {"a{3", :UnclosedRegexQuantifier, "{3"},
      {"a{65}", :RegexQuantifierTooLarge, "{65}"},
      {"{3}", :QuantifierWithoutAtom, "{3}"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod BadBounded\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta, {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}},
               _context} = reason} =
               Program.elaborate(source)

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      span = diagnostic.primary.span

      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
      refute Cure.Diagnostic.message(diagnostic) =~ "`#{expected}`"
    end)
  end
end
