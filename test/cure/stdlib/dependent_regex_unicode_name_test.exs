defmodule Cure.Stdlib.DependentRegexUnicodeNameTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  setup_all do
    source = ~S'''
    mod RegexUnicodeNames
      use Std.Regex

      fn latin_capital_a(input: String) -> Option(Unit) = parse_full(/\N{LATIN CAPITAL LETTER A}/, input)
      fn euro(input: String) -> Option(Unit) = parse_full(/\N{EURO SIGN}/, input)
      fn control_alias(input: String) -> Option(Unit) = parse_full(/\N{LINE FEED}/, input)
      fn line_feed(input: String) -> Option(String) = parse_full(/\R/, input)
      fn carriage_return_line_feed(input: String) -> Option(String) = parse_full(/\R/, input)
      fn unicode_line_separator(input: String) -> Option(String) = parse_full(/\R/, input)
      fn lf_policy(input: String) -> Option(String) = parse_full(/(*LF)\R/, input)
      fn cr_policy(input: String) -> Option(String) = parse_full(/(*CR)\R/, input)
      fn crlf_policy(input: String) -> Option(String) = parse_full(/(*CRLF)\R/, input)
      fn anycrlf_policy(input: String) -> Option(String) = parse_full(/(*ANYCRLF)\R/, input)
      fn any_policy(input: String) -> Option(String) = parse_full(/(*ANY)\R/, input)
      fn bsr_anycrlf_policy(input: String) -> Option(String) = parse_full(/(*BSR_ANYCRLF)\R/, input)
      fn bsr_unicode_policy(input: String) -> Option(String) = parse_full(/(*BSR_UNICODE)\R/, input)
      fn lf_dot(input: String) -> Option(Char) = parse_full(/(*LF)./, input)
      fn crlf_dot(input: String) -> Option(Char) = parse_full(/(*CRLF)./, input)
      fn crlf_anchor(input: String) -> Option(Match(Unit)) = search(/(*CRLF)a$/m, input)
      fn lf_anchor(input: String) -> Option(Match(Unit)) = search(/(*LF)a$/m, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "Unicode character names lower to checked scalar literals", %{runtime_module: module} do
    assert apply(module, :latin_capital_a, [{:String, ~c"A"}]) == {:some, :unit}
    assert apply(module, :euro, [{:String, [0x20AC]}]) == {:some, :unit}
    assert apply(module, :control_alias, [{:String, [10]}]) == {:some, :unit}
  end

  test "R matches CRLF as one finite line-break alternative and Unicode separators", %{runtime_module: module} do
    assert apply(module, :line_feed, [{:String, [10]}]) == {:some, {:String, [10]}}
    assert apply(module, :carriage_return_line_feed, [{:String, [13, 10]}]) == {:some, {:String, [13, 10]}}
    assert apply(module, :unicode_line_separator, [{:String, [0x2028]}]) == {:some, {:String, [0x2028]}}
    assert apply(module, :line_feed, [{:String, [13, 10, 13]}]) == :none
  end

  test "newline controls select finite R policies", %{runtime_module: module} do
    assert apply(module, :lf_policy, [{:String, [10]}]) == {:some, {:String, [10]}}
    assert apply(module, :lf_policy, [{:String, [13]}]) == :none
    assert apply(module, :lf_policy, [{:String, [13, 10]}]) == :none

    assert apply(module, :cr_policy, [{:String, [13]}]) == {:some, {:String, [13]}}
    assert apply(module, :cr_policy, [{:String, [10]}]) == :none

    assert apply(module, :crlf_policy, [{:String, [13, 10]}]) == {:some, {:String, [13, 10]}}
    assert apply(module, :crlf_policy, [{:String, [13]}]) == :none
    assert apply(module, :crlf_policy, [{:String, [10]}]) == :none

    assert apply(module, :anycrlf_policy, [{:String, [13]}]) == {:some, {:String, [13]}}
    assert apply(module, :anycrlf_policy, [{:String, [10]}]) == {:some, {:String, [10]}}
    assert apply(module, :anycrlf_policy, [{:String, [13, 10]}]) == {:some, {:String, [13, 10]}}
    assert apply(module, :anycrlf_policy, [{:String, [0x2028]}]) == :none

    assert apply(module, :any_policy, [{:String, [0x2028]}]) == {:some, {:String, [0x2028]}}
    assert apply(module, :bsr_anycrlf_policy, [{:String, [0x2028]}]) == :none
    assert apply(module, :bsr_unicode_policy, [{:String, [0x2028]}]) == {:some, {:String, [0x2028]}}
  end

  test "newline policies also govern multiline anchors", %{runtime_module: module} do
    assert {:some, _} = apply(module, :crlf_anchor, [{:String, [97, 13, 10]}])
    assert apply(module, :lf_anchor, [{:String, [97, 13, 10]}]) == :none
  end

  test "newline policies also govern dot", %{runtime_module: module} do
    assert apply(module, :lf_dot, [{:String, [13]}]) == {:some, 13}
    assert apply(module, :lf_dot, [{:String, [10]}]) == :none
    assert apply(module, :crlf_dot, [{:String, [10]}]) == {:some, 10}
  end

  test "unknown and malformed Unicode names have dedicated diagnostics" do
    cases = [
      {~S"\N{}", :EmptyRegexUnicodeName, ~S"\N{}"},
      {~S"\N{LATIN CAPITAL LETTER", :UnclosedRegexUnicodeName, ~S"\N{LATIN CAPITAL LETTER"},
      {~S"\N{NOT A REAL CHARACTER}", :UnknownRegexUnicodeName, ~S"\N{NOT A REAL CHARACTER}"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod BadUnicodeName\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

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
