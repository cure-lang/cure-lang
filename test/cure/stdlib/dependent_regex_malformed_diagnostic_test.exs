defmodule Cure.Stdlib.DependentRegexMalformedDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  test "malformed groups, classes, ranges, and escapes have exact diagnostics" do
    cases = [
      {"(abc", :UnclosedRegexGroup, "(abc"},
      {"[abc", :UnclosedRegexClass, "[abc"},
      {"[z-a]", :ReversedRegexRange, "z-a"},
      {")", :UnexpectedRegexToken, ")"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod MalformedRegex\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context} = reason} =
               Program.elaborate(source),
             "expected #{inspect(pattern)} to reject as #{inspect(expected)}"

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      span = diagnostic.primary.span

      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
      refute Cure.Diagnostic.message(diagnostic) =~ "`#{expected}`"
    end)
  end
end
