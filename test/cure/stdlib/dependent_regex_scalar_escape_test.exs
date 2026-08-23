defmodule Cure.Stdlib.DependentRegexScalarEscapeTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program
  alias Cure.Compiler.Errors

  setup_all do
    source = ~S'''
    mod RegexScalarEscapes
      use Std.Regex

      fn fixed(input: String) -> Option(Unit) = parse_full(/\x41/, input)
      fn unicode_bmp(input: String) -> Option(Unit) = parse_full(/\u0041/, input)
      fn unicode_astral(input: String) -> Option(Unit) = parse_full(/\U0001F642/, input)
      fn braced_bmp(input: String) -> Option(Unit) = parse_full(/\x{00E9}/, input)
      fn braced_astral(input: String) -> Option(Unit) = parse_full(/\x{1F642}/, input)
      fn fixed_class(input: String) -> Option(Char) = parse_full(/[\x41-\x43]/, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "fixed and braced hexadecimal escapes emit checked Unicode scalars", %{runtime_module: module} do
    assert apply(module, :fixed, [{:String, ~c"A"}]) == {:some, :unit}
    assert apply(module, :unicode_bmp, [{:String, ~c"A"}]) == {:some, :unit}
    assert apply(module, :unicode_astral, [{:String, [0x1F642]}]) == {:some, :unit}
    assert apply(module, :braced_bmp, [{:String, ~c"é"}]) == {:some, :unit}
    assert apply(module, :braced_astral, [{:String, [0x1F642]}]) == {:some, :unit}
    assert apply(module, :fixed_class, [{:String, ~c"B"}]) == {:some, ?B}
  end

  test "malformed and non-scalar hexadecimal escapes have dedicated diagnostics" do
    cases = [
      {~S"\x", :IncompleteRegexHexEscape, ~S"\x"},
      {~S"\x4", :IncompleteRegexHexEscape, ~S"\x4"},
      {~S"\xGG", :InvalidRegexHexEscape, ~S"\xGG"},
      {~S"\x{}", :EmptyRegexScalarEscape, ~S"\x{}"},
      {~S"\x{110000}", :RegexEscapeOutOfRange, ~S"\x{110000}"},
      {~S"\x{D800}", :RegexEscapeNotUnicodeScalar, ~S"\x{D800}"},
      {~S"\x{41", :UnclosedRegexScalarEscape, ~S"\x{41"},
      {~S"[\xGG]", :InvalidRegexHexEscape, ~S"\xGG"},
      {~S"\u", :IncompleteRegexHexEscape, ~S"\u"},
      {~S"\u041", :IncompleteRegexHexEscape, ~S"\u041"},
      {~S"\u00GG", :InvalidRegexHexEscape, ~S"\u00GG"},
      {~S"\uD800", :RegexEscapeNotUnicodeScalar, ~S"\uD800"},
      {~S"\U00110000", :RegexEscapeOutOfRange, ~S"\U00110000"},
      {~S"[\U00GG0000]", :InvalidRegexHexEscape, ~S"\U00GG0000"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod BadScalar\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

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

  test "regex syntax delegates Unicode scalar boundaries to Std.Char" do
    source = File.read!("lib/std_deps/regex/regex_syntax_model.cure")

    refute source =~ "1114111"
    refute source =~ "55296"
    refute source =~ "57343"
    assert source =~ "Std.Char.is_unicode_scalar_code_point"
    assert source =~ "Std.Char.is_utf16_surrogate_code_point"
  end
end
