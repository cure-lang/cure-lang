defmodule Cure.Stdlib.DependentRegexUnsupportedConstructTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  test "non-regular and deliberately unsupported constructs have dedicated diagnostics" do
    cases = [
      {~S"(a)\1", :UnsupportedRegexBackreference, ~S"\1"},
      {~S"(?<name>a)\k<name>", :UnsupportedRegexNamedCapture, "(?<"},
      {~S"a\g{1}", :UnsupportedRegexBackreference, ~S"\g"},
      {~S"(?R)", :UnsupportedRegexRecursion, "(?R"},
      {~S"(?1)", :UnsupportedRegexRecursion, "(?1"},
      {~S"(?(1)a|b)", :UnsupportedRegexConditional, "(?("},
      {~S"(?<=a)", :UnsupportedRegexLookbehind, "(?<="},
      {~S"(?<!a)", :UnsupportedRegexLookbehind, "(?<!"},
      {~S"(?=a)", :UnsupportedRegexLookahead, "(?="},
      {~S"(?!a)", :UnsupportedRegexLookahead, "(?!"},
      {~S"(?>a)", :UnsupportedRegexAtomicGroup, "(?>"},
      {~S"(?<name>a)", :UnsupportedRegexNamedCapture, "(?<"},
      {~S"(?'name'a)", :UnsupportedRegexNamedCapture, "(?\'"},
      {~S"(?P<name>a)", :UnsupportedRegexNamedCapture, "(?P<"},
      {~S"(?i:a)", :UnsupportedRegexInlineOptions, "(?i"},
      {~S"a*+", :UnsupportedRegexPossessiveQuantifier, "*+"},
      {~S"a{2}+", :UnsupportedRegexPossessiveQuantifier, "{2}+"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod UnsupportedRegex\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

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
