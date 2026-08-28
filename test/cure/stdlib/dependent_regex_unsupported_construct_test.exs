defmodule Cure.Stdlib.DependentRegexUnsupportedConstructTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  test "non-regular and deliberately unsupported constructs have dedicated diagnostics" do
    cases = [
      {~S"(a)\1", :UnsupportedRegexNumericEscape, ~S"\1"},
      {~S"\0", :UnsupportedRegexNumericEscape, ~S"\0"},
      {~S"\123", :UnsupportedRegexNumericEscape, ~S"\123"},
      {~S"(?<name>a)\k<name>", :UnsupportedRegexBackreference, ~S"\k"},
      {~S"a\g{1}", :UnsupportedRegexBackreference, ~S"\g"},
      {~S"(?R)", :UnsupportedRegexRecursion, "(?R"},
      {~S"(?1)", :UnsupportedRegexRecursion, "(?1"},
      {~S"(?x:a)", :UnsupportedRegexInlineOptions, "(?x"},
      {"(*THEN)", :UnsupportedRegexBacktrackingControl, "(*THEN)"},
      {"(*THEN:branch)", :UnsupportedRegexBacktrackingControl, "(*THEN:branch)"},
      {"(*PRUNE)", :UnsupportedRegexBacktrackingControl, "(*PRUNE)"},
      {"(*PRUNE:branch)", :UnsupportedRegexBacktrackingControl, "(*PRUNE:branch)"},
      {"(*SKIP)", :UnsupportedRegexBacktrackingControl, "(*SKIP)"},
      {"(*SKIP:branch)", :UnsupportedRegexBacktrackingControl, "(*SKIP:branch)"},
      {"(*COMMIT)", :UnsupportedRegexBacktrackingControl, "(*COMMIT)"},
      {"(*COMMIT:branch)", :UnsupportedRegexBacktrackingControl, "(*COMMIT:branch)"},
      {"(*UTF16)a", :UnsupportedRegexEncodingControl, "(*UTF16)"},
      {"(*UTF32)a", :UnsupportedRegexEncodingControl, "(*UTF32)"},
      {~S"a{2,1}", :RegexQuantifierRangeReversed, "{2,1}"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod UnsupportedRegex\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta, {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}},
               _context} = reason} =
               Program.elaborate(source),
             "expected #{inspect(pattern)} to reject as #{inspect(expected)}"

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      span = diagnostic.primary.span

      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
      refute Cure.Diagnostic.message(diagnostic) =~ "`#{expected}`"
    end)
  end

  test "FAIL is a finite refutation control rather than a host-engine escape" do
    source = ~S'''
    mod RegexFailControl
      use Std.Regex

      fn failed(input: String) -> Bool = matches(/a(*FAIL)/, input)
      fn alternated(input: String) -> Bool = matches(/a(*FAIL)|b/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(runtime_module, :failed, [{:String, ~c"a"}]) == false
    assert apply(runtime_module, :alternated, [{:String, ~c"a"}]) == false
    assert apply(runtime_module, :alternated, [{:String, ~c"b"}]) == true
  end

  test "the short F control is the finite FAIL alias" do
    source = ~S'''
    mod RegexShortFailControl
      use Std.Regex

      fn failed(input: String) -> Bool = matches(/a(*F)/, input)
      fn alternated(input: String) -> Bool = matches(/a(*F)|b/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(runtime_module, :failed, [{:String, ~c"a"}]) == false
    assert apply(runtime_module, :alternated, [{:String, ~c"a"}]) == false
    assert apply(runtime_module, :alternated, [{:String, ~c"b"}]) == true
  end

  test "labelled FAIL and ACCEPT controls preserve finite semantics" do
    source = ~S'''
    mod RegexLabelledControl
      use Std.Regex

      fn failed(input: String) -> Bool = matches(/a(*FAIL:branch)/, input)
      fn accepted(input: String) -> Bool = matches(/a(*ACCEPT:branch)/, input)
      fn empty_label(input: String) -> Bool = matches(/a(*FAIL:)/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(runtime_module, :failed, [{:String, ~c"a"}]) == false
    assert apply(runtime_module, :accepted, [{:String, ~c"a"}]) == true
    assert apply(runtime_module, :empty_label, [{:String, ~c"a"}]) == false
  end

  test "terminal ACCEPT is finite, while a continuing branch is diagnosed" do
    source = ~S'''
    mod RegexAcceptControl
      use Std.Regex

      fn accepted(input: String) -> Bool = matches(/a(*ACCEPT)/, input)
      fn alternated(input: String) -> Bool = matches(/a(*ACCEPT)|b/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(runtime_module, :accepted, [{:String, ~c"a"}]) == true
    assert apply(runtime_module, :accepted, [{:String, ~c"b"}]) == false
    assert apply(runtime_module, :alternated, [{:String, ~c"a"}]) == true
    assert apply(runtime_module, :alternated, [{:String, ~c"b"}]) == true

    source_with_continuation = ~S'''
    mod BadAcceptContinuation
      use Std.Regex
      fn run() = /a(*ACCEPT)b/
    end
    '''

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta,
              {:author_diagnostics, [{:macro_failure, :UnsupportedRegexAcceptContinuation, _}]}}, _context}} =
             Cure.Elab.Program.elaborate(source_with_continuation)
  end

  test "MARK controls normalize to zero-width annotations" do
    source = ~S'''
    mod RegexMarkControl
      use Std.Regex

      fn leading(input: String) -> Bool = matches(/(*MARK:leading)a/, input)
      fn inline(input: String) -> Bool = matches(/a(*MARK:middle)b/, input)
      fn alternated(input: String) -> Bool = matches(/(*MARK:left)a|(*MARK:right)b/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(runtime_module, :leading, [{:String, ~c"a"}]) == true
    assert apply(runtime_module, :inline, [{:String, ~c"ab"}]) == true
    assert apply(runtime_module, :alternated, [{:String, ~c"a"}]) == true
    assert apply(runtime_module, :alternated, [{:String, ~c"b"}]) == true
  end

  test "malformed MARK controls have dedicated diagnostics" do
    cases = [
      {"(*MARK)", :MalformedRegexMarkControl, "(*MARK)"},
      {"(*MARK:)", :EmptyRegexMarkName, "(*MARK:)"},
      {"(*MARK:label", :UnclosedRegexMarkControl, "(*MARK:label"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod MalformedRegexMark\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      reason = Program.elaborate(source)

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               reason

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      assert Cure.Diagnostic.message(diagnostic) =~ "MARK"
      span = diagnostic.primary.span
      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
    end)
  end

  test "unclosed labelled controls have a dedicated diagnostic span" do
    cases = [
      {"(*FAIL:branch", :UnclosedRegexControl},
      {"(*ACCEPT:branch", :UnclosedRegexControl}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod UnclosedRegexControl\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      reason = Program.elaborate(source)

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               reason

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      assert Cure.Diagnostic.message(diagnostic) =~ "closing `)`"
      span = diagnostic.primary.span
      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == pattern
    end)
  end

  test "unclosed backtracking controls have a dedicated diagnostic" do
    cases = [
      {"(*THEN", :UnclosedRegexControl},
      {"(*THEN:branch", :UnclosedRegexControl},
      {"(*PRUNE", :UnclosedRegexControl},
      {"(*PRUNE:branch", :UnclosedRegexControl},
      {"(*SKIP", :UnclosedRegexControl},
      {"(*SKIP:branch", :UnclosedRegexControl},
      {"(*COMMIT", :UnclosedRegexControl},
      {"(*COMMIT:branch", :UnclosedRegexControl}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod UnclosedBacktrackingControl\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      reason = Program.elaborate(source)

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               reason

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      assert Cure.Diagnostic.message(diagnostic) =~ "closing `)`"
      span = diagnostic.primary.span
      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == pattern
    end)
  end
end
