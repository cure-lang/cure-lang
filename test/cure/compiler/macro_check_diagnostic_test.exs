defmodule Cure.Compiler.MacroCheckDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "a macro check missing `else` labels the condition and inserts the unique keyword" do
    source = "check true fail BadInput(value)"
    {diagnostic, registry} = diagnostic(source, "check_else.cure")

    assert diagnostic.key == :macro_check_else_missing

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO CHECK NEEDS `ELSE` [E094] ----------------------------- check_else.cure

             A macro check uses `else` between its condition and failure value; 'fail'
             appears where `else` belongs.

             A valid continuation here starts with 'else'.

             at check_else.cure:1:12
             1 | check true fail BadInput(value)
               | ----- ---- ^ this macro check starts here; the checked condition ends here; insert `else` before the rejected branch

             Hint: Insert `else` before the rejected branch
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "else ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column, insertion.start_byte, insertion.end_byte} == {1, 12, 11, 11}

    assert [%{"newText" => "else ", "range" => range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert range == %{
             "start" => %{"line" => 0, "character" => 11},
             "end" => %{"line" => 0, "character" => 11}
           }
  end

  test "a macro check missing `fail` points before the authored failure value" do
    {diagnostic, _registry} = diagnostic("check true else BadInput(value)", "check_fail.cure")

    assert diagnostic.key == :macro_check_fail_missing
    assert {diagnostic.primary.span.start_column, diagnostic.primary.span.end_column} == {17, 17}

    assert Enum.map(diagnostic.secondary, & &1.message) == [
             "this macro check starts here",
             "the rejected branch starts after this `else`"
           ]

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "fail ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_byte, insertion.end_byte} == {16, 16}
  end

  test "a non-call failure value gets its own authored range and no speculative edit" do
    {diagnostic, registry} = diagnostic("check true else fail 42", "check_value.cure")

    assert diagnostic.key == :macro_check_failure_constructor_invalid
    assert {diagnostic.primary.span.start_column, diagnostic.primary.span.end_column} == {22, 24}
    assert diagnostic.primary.message == "call a declared macro failure here"
    assert diagnostic.suggestions == []

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 21},
             "end" => %{"line" => 0, "character" => 23}
           }
  end

  defp diagnostic(source, file) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, file: file, emit_events: false)
    Errors.to_diagnostic({:parse_error, [error]}, file, source)
  end
end
