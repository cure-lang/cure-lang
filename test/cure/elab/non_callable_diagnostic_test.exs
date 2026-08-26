defmodule Cure.Elab.NonCallableDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "applying a literal points at the non-callable value and its stranded argument" do
    source = "mod M\n  fn bad() -> Int = 1(2)\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "literal_call.cure")

    assert {:applied_non_function, %{argument_index: 0}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `INT` VALUE IS NOT CALLABLE [E093] ------------------------ literal_call.cure

             Parentheses apply a function or constructor, but this expression has type `Int`.
             It cannot accept the argument written after it.

             at literal_call.cure:2:21
             2 |   fn bad() -> Int = 1(2)
               |                     ^ - this expression has type `Int`, not a function type; this argument has nowhere to go

             Hint: Remove the parentheses, or replace this expression with a function or constructor
             """)

    assert diagnostic.payload.actual_type == "Int"
    refute inspect(diagnostic.payload) =~ "{:data"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 20, 1, 21)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(1, 22, 1, 23)

    repaired = String.replace(source, "1(2)", "1")
    assert {:ok, _env} = Program.elaborate(repaired, file: "literal_call.cure")
  end

  test "applying a call result points at the expression that already produced a value" do
    source =
      "mod M\n  fn id(value: Int) -> Int = value\n  fn bad() -> Int = id(1)(2)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "extra_argument.cure")

    assert {:applied_non_function, %{argument_index: 0}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `INT` VALUE IS NOT CALLABLE [E093] ---------------------- extra_argument.cure

             Parentheses apply a function or constructor, but this expression has type `Int`.
             It cannot accept the argument written after it.

             at extra_argument.cure:3:21
             3 |   fn bad() -> Int = id(1)(2)
               |                     ^^^^^ - this expression has type `Int`, not a function type; this argument has nowhere to go

             Hint: Remove the parentheses, or replace this expression with a function or constructor
             """)

    assert diagnostic.primary.span.start_column == 21

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 20, 2, 25)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(2, 26, 2, 27)

    repaired = String.replace(source, "id(1)(2)", "id(1)")
    assert {:ok, _env} = Program.elaborate(repaired, file: "extra_argument.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
