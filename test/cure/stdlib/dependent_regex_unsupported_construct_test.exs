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
end
