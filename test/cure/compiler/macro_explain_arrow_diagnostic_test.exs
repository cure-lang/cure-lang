defmodule Cure.Compiler.MacroExplainArrowDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(point, file) do
    source = "macro Every\n  explain\n    #{point} \"message\"\n"
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(
        errors,
        &match?({:branch_arrow_missing, %{family: :explain_clause}}, &1)
      )

    assert {:branch_arrow_missing, _} = error
    {error, Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a category explanation inserts its missing fat arrow after the failure point" do
    {error, {diagnostic, registry}} = diagnostic("Duration", "explain_arrow.cure")

    assert {:branch_arrow_missing,
            %{
              family: :explain_clause,
              expected: :fat_arrow,
              observed: "message",
              token_type: :string
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXPLANATION CLAUSE ARROW IS MISSING [E094] --------------- explain_arrow.cure

             An explanation clause needs `=>` between its failure point and message.

             A valid continuation here starts with '=>'.

             at explain_arrow.cure:3:14
             3 |     Duration "message"
               |     -------- ^ this is the failure point; insert `=>` before this explanation message

             Hint: Insert `=>` before the explanation message
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "=> ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {3, 14}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "=> ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 2, "character" => 13},
             "end" => %{"line" => 2, "character" => 13}
           }
  end

  test "a keyword explanation labels the complete authored failure point" do
    {error, {diagnostic, registry}} = diagnostic(~s(keyword "every"), "keyword_explain_arrow.cure")

    assert {:branch_arrow_missing, %{family: :explain_clause, observed: "message"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EXPLANATION CLAUSE ARROW IS MISSING [E094] ------- keyword_explain_arrow.cure

             An explanation clause needs `=>` between its failure point and message.

             A valid continuation here starts with '=>'.

             at keyword_explain_arrow.cure:3:21
             3 |     keyword "every" "message"
               |     -------         ^ this explanation clause starts here; insert `=>` before this explanation message
               |     --------------- the failure point ends here

             Hint: Insert `=>` before the explanation message
             """)
  end

  test "both explanation point forms still parse with their arrow" do
    for point <- ["Duration", ~s(keyword "every")] do
      source = "macro Every\n  explain\n    #{point} => \"message\"\n"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end
  end
end
