defmodule Cure.Compiler.MacroRuleSeparatorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "a computed rule missing `by` has exact labels and a machine edit" do
    source = "macro Mk\n  syntax mk computed build_it\n"
    {diagnostic, registry} = diagnostic(source, "computed_by.cure")

    assert diagnostic.key == :computed_rule_by_missing

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED RULE NEEDS `BY` [E094] ---------------------------- computed_by.cure

             A computed rule uses `by` before the elaborator function that implements it;
             'build_it' appears where `by` belongs.

             A valid continuation here starts with 'by'.

             at computed_by.cure:2:22
             2 |   syntax mk computed build_it
               |   ------    -------- ^ this computed rule starts here; the computed modifier ends here; insert `by` before this expression

             Hint: Insert `by` before this expression
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "by ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column, insertion.start_byte, insertion.end_byte} == {2, 22, 30, 30}

    assert [%{"newText" => "by ", "range" => range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert range == %{
             "start" => %{"line" => 1, "character" => 21},
             "end" => %{"line" => 1, "character" => 21}
           }
  end

  test "an `expands` section missing `with` inserts only the known separator" do
    {diagnostic, _registry} = diagnostic("macro Mk\n  expands build_it\n", "expands_with.cure")

    assert diagnostic.key == :macro_expands_with_missing
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {2, 11}
    assert [%{applicability: :machine_applicable, edits: [%{replacement: "with "}]}] = diagnostic.suggestions
  end

  test "rules and examples ending before their separator get manual complete-repair hints" do
    cases = [
      {:macro_rule_becomes_missing, "macro Mk\n  syntax mk\n", "becomes.cure"},
      {:literal_rule_becomes_missing, "macro Unit\n  literal <n: Number> ms\n", "literal_becomes.cure"},
      {:macro_example_expands_missing, "macro Mk\n  syntax mk becomes 1\n    example mk 1\n", "example_expands.cure"}
    ]

    for {key, source, file} <- cases do
      {diagnostic, registry} = diagnostic(source, file)
      assert diagnostic.key == key
      assert diagnostic.primary.span.start_byte == diagnostic.primary.span.end_byte
      assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
      assert Renderer.lsp(diagnostic, registry)["range"]["start"] == Renderer.lsp(diagnostic, registry)["range"]["end"]
    end
  end

  defp diagnostic(source, file) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, file: file, emit_events: false)
    error = Enum.find(errors, &match?({:macro_rule_separator_syntax, _}, &1))
    assert error
    Errors.to_diagnostic({:parse_error, [error]}, file, source)
  end
end
