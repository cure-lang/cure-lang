defmodule Cure.Stdlib.DependentRegexGraphemeTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  test "diagnoses extended grapheme syntax instead of treating X as a literal" do
    pattern = ~S"\X"
    source = "mod UnsupportedGrapheme\n  use Std.Regex\n  fn run() = /#{pattern}/u\nend\n"

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta,
              {:author_diagnostics, [{:macro_failure, :UnsupportedRegexGrapheme, _arguments}]}},
             _context} = reason} =
             Program.elaborate(source)

    {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
    span = diagnostic.primary.span

    assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == pattern
    refute Cure.Diagnostic.message(diagnostic) =~ "`UnsupportedRegexGrapheme`"
  end
end
