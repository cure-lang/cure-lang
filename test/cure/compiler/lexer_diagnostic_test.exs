defmodule Cure.Compiler.LexerDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    assert {:error, reason} = Cure.Compiler.compile_string(source, file: file, emit_events: false)
    Cure.Compiler.Errors.to_diagnostic(reason, file, source)
  end

  test "an unterminated string with a final newline points before that newline" do
    source = "mod DiagnosticLexer\n  fn run() -> String = \"not closed\n"
    {diagnostic, registry} = diagnostic(source, "lexer syntax error.cure")

    assert diagnostic.code == "E094"
    assert diagnostic.key == :unterminated_string

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- STRING IS NOT CLOSED [E094] ------------------------- lexer syntax error.cure

             This string reaches the end of the source without its closing double quote.

             A valid continuation here starts with '"'.

             at lexer syntax error.cure:2:35
             2 |   fn run() -> String = "not closed
               |                                   ^ insert the closing `"` here

             Hint: Insert `"` to close the construct
             """)

    assert %{span: insertion} = diagnostic.primary
    assert {insertion.start_line, insertion.start_column} == {2, 35}
    assert insertion.start_byte == insertion.end_byte

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "\"", span: ^insertion}]}] =
             diagnostic.suggestions

    assert [%{"newText" => "\"", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 1, "character" => 34},
             "end" => %{"line" => 1, "character" => 34}
           }
  end

  test "character and quoted-identifier delimiters use their own repairs" do
    cases = [
      {"fn value() -> Char = 'x\n", "Character is not closed", "'", "insert the closing `'` here"},
      {"fn `value() -> Int = 1\n", "Quoted name is not closed", "`", "insert the closing backtick here"}
    ]

    for {source, title, replacement, label} <- cases do
      {diagnostic, _registry} = diagnostic(source, "lexer_delimiter.cure")
      assert diagnostic.title == title
      assert diagnostic.primary.message == label
      assert diagnostic.primary.span.start_line == 1
      assert diagnostic.primary.span.start_byte == diagnostic.primary.span.end_byte

      assert [%{applicability: :machine_applicable, edits: [%{replacement: ^replacement}]}] =
               diagnostic.suggestions
    end
  end

  test "CRLF input places the repair before the complete line ending" do
    source = "fn value() -> String = \"open\r\n"
    {diagnostic, _registry} = diagnostic(source, "lexer_crlf.cure")

    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {1, 29}
    assert diagnostic.primary.span.start_byte == byte_size("fn value() -> String = \"open")
  end
end
