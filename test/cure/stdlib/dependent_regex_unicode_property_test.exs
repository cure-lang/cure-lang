defmodule Cure.Stdlib.DependentRegexUnicodePropertyTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program
  alias Cure.Compiler.Errors

  setup_all do
    source = ~S'''
    mod RegexUnicodeProperties
      use Std.Regex

      fn letter(input: String) -> Option(Char) = parse_full(/\p{L}/u, input)
      fn long_letter(input: String) -> Option(Char) = parse_full(/\p{Letter}/u, input)
      fn uppercase(input: String) -> Option(Char) = parse_full(/\p{Lu}/u, input)
      fn decimal(input: String) -> Option(Char) = parse_full(/\p{Decimal_Number}/u, input)
      fn ascii(input: String) -> Option(Char) = parse_full(/\p{ASCII}/u, input)
      fn not_ascii(input: String) -> Option(Char) = parse_full(/\P{ASCII}/u, input)
      fn cased(input: String) -> Option(Char) = parse_full(/\p{Cased}/u, input)
      fn lowercase_binary(input: String) -> Option(Char) = parse_full(/\p{Lowercase}/u, input)
      fn uppercase_binary(input: String) -> Option(Char) = parse_full(/\p{Uppercase}/u, input)
      fn alphabetic(input: String) -> Option(Char) = parse_full(/\p{Alphabetic}/u, input)
      fn white_space(input: String) -> Option(Char) = parse_full(/\p{White_Space}/u, input)
      fn hex_digit(input: String) -> Option(Char) = parse_full(/\p{Hex_Digit}/u, input)
      fn math(input: String) -> Option(Char) = parse_full(/\p{Math}/u, input)
      fn currency(input: String) -> Option(Char) = parse_full(/\p{Currency_Symbol}/u, input)
      fn latin_script(input: String) -> Option(Char) = parse_full(/\p{Latin}/u, input)
      fn greek_script(input: String) -> Option(Char) = parse_full(/\p{Greek}/u, input)
      fn greek_script_qualified(input: String) -> Option(Char) = parse_full(/\p{Script=Greek}/u, input)
      fn greek_script_short(input: String) -> Option(Char) = parse_full(/\p{sc=Grek}/u, input)
      fn cyrillic_script(input: String) -> Option(Char) = parse_full(/\p{Cyrillic}/u, input)
      fn category_qualified(input: String) -> Option(Char) = parse_full(/\p{General_Category=Letter}/u, input)
      fn category_short(input: String) -> Option(Char) = parse_full(/\p{gc=Nd}/u, input)
      fn assigned_category(input: String) -> Option(Char) = parse_full(/\p{Assigned}/u, input)
      fn hiragana_script(input: String) -> Option(Char) = parse_full(/\p{Hiragana}/u, input)
      fn hiragana_script_extension(input: String) -> Option(Char) = parse_full(/\p{scx=Hira}/u, input)
      fn hiragana_script_extension_long(input: String) -> Option(Char) = parse_full(/\p{Script_Extensions=Hiragana}/u, input)
      fn arabic_bidi(input: String) -> Option(Char) = parse_full(/\p{Bidi_Class=AL}/u, input)
      fn arabic_bidi_long(input: String) -> Option(Char) = parse_full(/\p{Bidi_Class=Arabic_Letter}/u, input)
      fn hebrew_bidi(input: String) -> Option(Char) = parse_full(/\p{bc=R}/u, input)
      fn hebrew_bidi_long(input: String) -> Option(Char) = parse_full(/\p{bc=Right_To_Left}/u, input)
      fn bidi_mirrored(input: String) -> Option(Char) = parse_full(/\p{Bidi_Mirrored}/u, input)
      fn emoji_binary(input: String) -> Option(Char) = parse_full(/\p{Emoji}/u, input)
      fn not_emoji_binary(input: String) -> Option(Char) = parse_full(/\P{Emoji}/u, input)
      fn pictographic_binary(input: String) -> Option(Char) = parse_full(/\p{Extended_Pictographic}/u, input)
      fn id_start_binary(input: String) -> Option(Char) = parse_full(/\p{ID_Start}/u, input)
      fn not_number(input: String) -> Option(Char) = parse_full(/\P{N}/u, input)
      fn class_union(input: String) -> Option(Char) = parse_full(/[\p{L}\p{N}_]/u, input)
      fn class_negated_property(input: String) -> Option(Char) = parse_full(/[\P{L}]/u, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "Unicode general-category properties and aliases match without a host regex engine", %{runtime_module: module} do
    assert apply(module, :letter, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :long_letter, [{:String, ~c"é"}]) == {:some, ?é}
    assert apply(module, :uppercase, [{:String, ~c"É"}]) == {:some, ?É}
    assert apply(module, :uppercase, [{:String, ~c"é"}]) == :none
    assert apply(module, :decimal, [{:String, ~c"١"}]) == {:some, ?١}
    assert apply(module, :ascii, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :ascii, [{:String, [0x80]}]) == :none
    assert apply(module, :not_ascii, [{:String, [0x80]}]) == {:some, 0x80}
    assert apply(module, :not_ascii, [{:String, ~c"A"}]) == :none
    assert apply(module, :cased, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :cased, [{:String, ~c"1"}]) == :none
    assert apply(module, :lowercase_binary, [{:String, ~c"é"}]) == {:some, ?é}
    assert apply(module, :lowercase_binary, [{:String, ~c"É"}]) == :none
    assert apply(module, :uppercase_binary, [{:String, ~c"É"}]) == {:some, ?É}
    assert apply(module, :uppercase_binary, [{:String, ~c"é"}]) == :none
    assert apply(module, :alphabetic, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :alphabetic, [{:String, ~c"1"}]) == :none
    assert apply(module, :white_space, [{:String, [0x2028]}]) == {:some, 0x2028}
    assert apply(module, :white_space, [{:String, ~c"A"}]) == :none
    assert apply(module, :hex_digit, [{:String, ~c"Ｆ"}]) == {:some, 0xFF26}
    assert apply(module, :hex_digit, [{:String, ~c"G"}]) == :none
    assert apply(module, :math, [{:String, ~c"+"}]) == {:some, ?+}
    assert apply(module, :math, [{:String, ~c"A"}]) == :none
    assert apply(module, :currency, [{:String, ~c"$"}]) == {:some, ?$}
    assert apply(module, :currency, [{:String, ~c"A"}]) == :none
    assert apply(module, :latin_script, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :latin_script, [{:String, ~c"λ"}]) == :none
    assert apply(module, :greek_script, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :greek_script, [{:String, ~c"Ж"}]) == :none
    assert apply(module, :greek_script_qualified, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :greek_script_qualified, [{:String, ~c"A"}]) == :none
    assert apply(module, :greek_script_short, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :greek_script_short, [{:String, ~c"A"}]) == :none
    assert apply(module, :cyrillic_script, [{:String, ~c"Ж"}]) == {:some, ?Ж}
    assert apply(module, :cyrillic_script, [{:String, ~c"A"}]) == :none
    assert apply(module, :category_qualified, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :category_qualified, [{:String, ~c"1"}]) == :none
    assert apply(module, :category_short, [{:String, ~c"١"}]) == {:some, 0x661}
    assert apply(module, :category_short, [{:String, ~c"A"}]) == :none
    assert apply(module, :assigned_category, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :assigned_category, [{:String, [0x378]}]) == :none
    assert apply(module, :hiragana_script, [{:String, ~c"あ"}]) == {:some, ?あ}
    assert apply(module, :hiragana_script, [{:String, ~c"A"}]) == :none
    assert apply(module, :hiragana_script_extension, [{:String, ~c"ー"}]) == {:some, 0x30FC}
    assert apply(module, :hiragana_script_extension, [{:String, ~c"A"}]) == :none
    assert apply(module, :hiragana_script_extension_long, [{:String, ~c"ー"}]) == {:some, 0x30FC}
    assert apply(module, :hiragana_script_extension_long, [{:String, ~c"A"}]) == :none
    assert apply(module, :arabic_bidi, [{:String, ~c"ع"}]) == {:some, ?ع}
    assert apply(module, :arabic_bidi, [{:String, ~c"A"}]) == :none
    assert apply(module, :arabic_bidi_long, [{:String, ~c"ع"}]) == {:some, ?ع}
    assert apply(module, :arabic_bidi_long, [{:String, ~c"A"}]) == :none
    assert apply(module, :hebrew_bidi, [{:String, ~c"א"}]) == {:some, ?א}
    assert apply(module, :hebrew_bidi, [{:String, ~c"A"}]) == :none
    assert apply(module, :hebrew_bidi_long, [{:String, ~c"א"}]) == {:some, ?א}
    assert apply(module, :hebrew_bidi_long, [{:String, ~c"A"}]) == :none
    assert apply(module, :bidi_mirrored, [{:String, ~c"("}]) == {:some, ?(}
    assert apply(module, :bidi_mirrored, [{:String, ~c"A"}]) == :none
    assert apply(module, :emoji_binary, [{:String, ~c"🙂"}]) == {:some, 0x1F642}
    assert apply(module, :emoji_binary, [{:String, ~c"A"}]) == :none
    assert apply(module, :not_emoji_binary, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :not_emoji_binary, [{:String, ~c"🙂"}]) == :none
    assert apply(module, :pictographic_binary, [{:String, ~c"🙂"}]) == {:some, 0x1F642}
    assert apply(module, :pictographic_binary, [{:String, ~c"A"}]) == :none
    assert apply(module, :id_start_binary, [{:String, ~c"A"}]) == {:some, ?A}
    assert apply(module, :id_start_binary, [{:String, ~c"1"}]) == :none
    assert apply(module, :not_number, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :not_number, [{:String, ~c"١"}]) == :none
  end

  test "property classes compose inside bracket classes and respect negation", %{runtime_module: module} do
    assert apply(module, :class_union, [{:String, ~c"λ"}]) == {:some, ?λ}
    assert apply(module, :class_union, [{:String, ~c"١"}]) == {:some, ?١}
    assert apply(module, :class_union, [{:String, ~c"_"}]) == {:some, ?_}
    assert apply(module, :class_negated_property, [{:String, ~c"!"}]) == {:some, ?!}
    assert apply(module, :class_negated_property, [{:String, ~c"λ"}]) == :none
  end

  test "unknown, empty, malformed, and unclosed properties reject distinctly" do
    cases = [
      {~S"\p{}", :EmptyRegexUnicodeProperty, ~S"\p{}"},
      {~S"\p{Bogus}", :UnknownRegexUnicodeProperty, ~S"\p{Bogus}"},
      {~S"\pL", :MalformedRegexUnicodeProperty, ~S"\pL"},
      {~S"\p{L", :UnclosedRegexUnicodeProperty, ~S"\p{L"},
      {~S"[\p{}]", :EmptyRegexUnicodeProperty, ~S"\p{}"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod BadProperty\n  use Std.Regex\n  fn run() = /#{pattern}/u\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context} = reason} =
               Program.elaborate(source)

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      span = diagnostic.primary.span

      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
      refute Cure.Diagnostic.message(diagnostic) =~ "`#{expected}`"

      if expected == :UnknownRegexUnicodeProperty do
        assert Cure.Diagnostic.message(diagnostic) =~ "pinned"
      end
    end)
  end
end
