defmodule Cure.Stdlib.DependentRegexPosixClassTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  setup_all do
    source = ~S'''
    mod RegexPosixClasses
      use Std.Regex

      fn alpha(input: String) -> Option(Char) = parse_full(/[[:alpha:]]/, input)
      fn unicode_alpha(input: String) -> Option(Char) = parse_full(/[[:alpha:]]/u, input)
      fn unicode_alnum(input: String) -> Option(Char) = parse_full(/[[:alnum:]]/u, input)
      fn unicode_lower(input: String) -> Option(Char) = parse_full(/[[:lower:]]/u, input)
      fn unicode_upper(input: String) -> Option(Char) = parse_full(/[[:upper:]]/u, input)
      fn unicode_xdigit(input: String) -> Option(Char) = parse_full(/[[:xdigit:]]/u, input)
      fn graph(input: String) -> Option(Char) = parse_full(/[[:graph:]]/, input)
      fn unicode_graph(input: String) -> Option(Char) = parse_full(/[[:graph:]]/u, input)
      fn unicode_print(input: String) -> Option(Char) = parse_full(/[[:print:]]/u, input)
      fn unicode_punct(input: String) -> Option(Char) = parse_full(/[[:punct:]]/u, input)
      fn unicode_blank(input: String) -> Option(Char) = parse_full(/[[:blank:]]/u, input)
      fn unicode_cntrl(input: String) -> Option(Char) = parse_full(/[[:cntrl:]]/u, input)
      fn unicode_digit(input: String) -> Option(Char) = parse_full(/[[:digit:]]/u, input)
      fn unicode_space(input: String) -> Option(Char) = parse_full(/[[:space:]]/u, input)
      fn unicode_word(input: String) -> Option(Char) = parse_full(/[[:word:]]/u, input)
      fn ascii(input: String) -> Option(Char) = parse_full(/[[:ascii:]]/u, input)
      fn inner_not_alpha(input: String) -> Option(Char) = parse_full(/[[:^alpha:]]/u, input)
      fn outer_not_alpha(input: String) -> Option(Char) = parse_full(/[^[:alpha:]]/u, input)
      fn union(input: String) -> Option(Char) = parse_full(/[x[:digit:]]/u, input)
    end
    '''

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  defp string(char), do: {:String, [char]}

  test "POSIX classes follow ASCII and Unicode modifier semantics", %{runtime_module: module} do
    assert apply(module, :alpha, [string(?A)]) == {:some, ?A}
    assert apply(module, :alpha, [string(?é)]) == :none
    assert apply(module, :unicode_alpha, [string(?é)]) == {:some, ?é}
    assert apply(module, :unicode_alnum, [string(?١)]) == {:some, ?١}
    assert apply(module, :unicode_lower, [string(?é)]) == {:some, ?é}
    assert apply(module, :unicode_upper, [string(?É)]) == {:some, ?É}
    assert apply(module, :unicode_xdigit, [string(?Ａ)]) == {:some, ?Ａ}
    assert apply(module, :graph, [string(?é)]) == :none
    assert apply(module, :unicode_graph, [string(?€)]) == {:some, ?€}
    assert apply(module, :unicode_print, [string(0xA0)]) == {:some, 0xA0}
    assert apply(module, :unicode_punct, [string(?!)]) == {:some, ?!}
    assert apply(module, :unicode_blank, [string(0xA0)]) == {:some, 0xA0}
    assert apply(module, :unicode_cntrl, [string(10)]) == {:some, 10}
    assert apply(module, :unicode_digit, [string(?١)]) == {:some, ?١}
    assert apply(module, :unicode_space, [string(0xA0)]) == {:some, 0xA0}
    assert apply(module, :unicode_word, [string(?_)]) == {:some, ?_}
    assert apply(module, :ascii, [string(?A)]) == {:some, ?A}
    assert apply(module, :ascii, [string(?é)]) == :none
  end

  test "POSIX classes compose with class union and both negation layers", %{runtime_module: module} do
    assert apply(module, :inner_not_alpha, [string(?!)]) == {:some, ?!}
    assert apply(module, :inner_not_alpha, [string(?λ)]) == :none
    assert apply(module, :outer_not_alpha, [string(?!)]) == {:some, ?!}
    assert apply(module, :outer_not_alpha, [string(?λ)]) == :none
    assert apply(module, :union, [string(?x)]) == {:some, ?x}
    assert apply(module, :union, [string(?١)]) == {:some, ?١}
  end

  test "malformed POSIX classes have dedicated exact diagnostics" do
    cases = [
      {"[[:bogus:]]", :UnknownRegexPosixClass, "[:bogus:]"},
      {"[[::]]", :EmptyRegexPosixClass, "[::]"},
      {"[[:alpha]", :UnclosedRegexPosixClass, "[:alpha]"}
    ]

    Enum.each(cases, fn {pattern, expected, expected_span} ->
      source = "mod BadPosix\n  use Std.Regex\n  fn run() = /#{pattern}/u\nend\n"

      assert {:error,
              {:source_context,
               {:computed_macro_error, _meta,
                {:author_diagnostics, [{:macro_failure, ^expected, _arguments}]}}, _context} = reason} =
               Program.elaborate(source)

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "nofile", source)
      span = diagnostic.primary.span
      assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == expected_span
    end)
  end
end
