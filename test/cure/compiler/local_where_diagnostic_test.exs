defmodule Cure.Compiler.LocalWhereDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file, kind) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:declaration_separator_missing, %{kind: ^kind}}, &1))
    assert {:declaration_separator_missing, _} = error
    {error, Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an unindented local definition points back to its where block" do
    source = "fn run() -> Int = 1\nwhere\nvalue = 2\n"
    {error, {diagnostic, registry}} = diagnostic(source, "where_indent.cure", :where_block_indent_missing)

    assert {:declaration_separator_missing,
            %{
              kind: :where_block_indent_missing,
              expected: :indent,
              observed: "value",
              token_type: :identifier
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LOCAL DEFINITIONS MUST BE INDENTED [E094] ----------------- where_indent.cure

             Definitions belonging to this `where` block must be indented beneath it.

             A valid continuation here starts with an indented block.

             at where_indent.cure:3:1
             2 | where
               | ----- this local `where` block starts here
             3 | value = 2
               | ^^^^^ indent this definition beneath `where`

             Hint: Indent each local definition beneath `where`
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "a local value without equals gets an insertion before its value" do
    source = "fn run() -> Int = value\nwhere\n  value 2\n"
    {error, {diagnostic, registry}} = diagnostic(source, "where_equals.cure", :where_binding_assign_missing)

    assert {:declaration_separator_missing,
            %{
              kind: :where_binding_assign_missing,
              declaration: "value",
              expected: :assign,
              observed: 2,
              token_type: :integer
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LOCAL DEFINITION NEEDS AN EQUALS SIGN [E094] -------------- where_equals.cure

             The local definition `value` needs `=` between its name and value.

             A valid continuation here starts with '='.

             at where_equals.cure:3:9
             2 | where
               | ----- this local `where` block starts here
             3 |   value 2
               |   ----- ^ this is the local definition name; insert `=` before this local value

             Hint: Insert `=` before the local value
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "= ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {3, 9}

    assert [%{"newText" => "= ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 2, "character" => 8},
             "end" => %{"line" => 2, "character" => 8}
           }
  end

  test "an indented local value and function still parse" do
    source = "fn run() -> Int = value\nwhere\n  value = 2\n  fn helper() -> Int = value\n"
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
  end
end
