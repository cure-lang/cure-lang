defmodule Cure.Stdlib.DependentRegexScalarEscapeTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  setup_all do
    source = ~S'''
    mod RegexScalarEscapes
      use Std.Regex

      fn fixed(input: String) -> Option(Unit) = parse_full(/\x41/, input)
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
    assert apply(module, :braced_bmp, [{:String, ~c"é"}]) == {:some, :unit}
    assert apply(module, :braced_astral, [{:String, [0x1F642]}]) == {:some, :unit}
    assert apply(module, :fixed_class, [{:String, ~c"B"}]) == {:some, ?B}
  end

  test "malformed and non-scalar hexadecimal escapes have dedicated diagnostics" do
    cases = [
      {~S"\x", :IncompleteRegexHexEscape},
      {~S"\x4", :IncompleteRegexHexEscape},
      {~S"\xGG", :InvalidRegexHexEscape},
      {~S"\x{}", :EmptyRegexScalarEscape},
      {~S"\x{110000}", :RegexEscapeOutOfRange},
      {~S"\x{D800}", :RegexEscapeNotUnicodeScalar},
      {~S"\x{41", :UnclosedRegexScalarEscape}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod BadScalar\n  use Std.Regex\n  fn run() = /#{pattern}/\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               Program.elaborate(source)
    end)
  end

  test "regex syntax delegates Unicode scalar boundaries to Std.Char" do
    source = File.read!("lib/std/regex_syntax_model.cure")

    refute source =~ "1114111"
    refute source =~ "55296"
    refute source =~ "57343"
    assert source =~ "Std.Char.is_unicode_scalar_code_point"
    assert source =~ "Std.Char.is_utf16_surrogate_code_point"
  end
end
