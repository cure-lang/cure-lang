defmodule Cure.Stdlib.DependentRegexUnsupportedConstructTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "non-regular and deliberately unsupported constructs have dedicated diagnostics" do
    cases = [
      {~S"(a)\1", :UnsupportedRegexBackreference},
      {~S"(?<name>a)\k<name>", :UnsupportedRegexNamedCapture},
      {~S"a\g{1}", :UnsupportedRegexBackreference},
      {~S"(?R)", :UnsupportedRegexRecursion},
      {~S"(?1)", :UnsupportedRegexRecursion},
      {~S"(?(1)a|b)", :UnsupportedRegexConditional},
      {~S"(?<=a)", :UnsupportedRegexLookbehind},
      {~S"(?<!a)", :UnsupportedRegexLookbehind},
      {~S"(?=a)", :UnsupportedRegexLookahead},
      {~S"(?!a)", :UnsupportedRegexLookahead},
      {~S"(?>a)", :UnsupportedRegexAtomicGroup},
      {~S"(?<name>a)", :UnsupportedRegexNamedCapture},
      {~S"(?'name'a)", :UnsupportedRegexNamedCapture},
      {~S"(?P<name>a)", :UnsupportedRegexNamedCapture},
      {~S"(?i:a)", :UnsupportedRegexInlineOptions},
      {~S"a*+", :UnsupportedRegexPossessiveQuantifier},
      {~S"a{2}+", :UnsupportedRegexPossessiveQuantifier}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod UnsupportedRegex\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               Program.elaborate(source),
             "expected #{inspect(pattern)} to reject as #{inspect(expected)}"
    end)
  end
end
