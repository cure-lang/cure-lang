defmodule Cure.Stdlib.DependentRegexUnicodePropertyTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  setup_all do
    source = ~S'''
    mod RegexUnicodeProperties
      use Std.Regex

      fn letter(input: String) -> Option(Char) = parse_full(/\p{L}/u, input)
      fn long_letter(input: String) -> Option(Char) = parse_full(/\p{Letter}/u, input)
      fn uppercase(input: String) -> Option(Char) = parse_full(/\p{Lu}/u, input)
      fn decimal(input: String) -> Option(Char) = parse_full(/\p{Decimal_Number}/u, input)
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
      {~S"\p{}", :EmptyRegexUnicodeProperty},
      {~S"\p{Bogus}", :UnknownRegexUnicodeProperty},
      {~S"\pL", :MalformedRegexUnicodeProperty},
      {~S"\p{L", :UnclosedRegexUnicodeProperty}
    ]

    Enum.each(cases, fn {pattern, expected} ->
      source = "mod BadProperty\n  use Std.Regex\n  fn run() = /#{pattern}/u\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context}} =
               Program.elaborate(source)
    end)
  end
end
