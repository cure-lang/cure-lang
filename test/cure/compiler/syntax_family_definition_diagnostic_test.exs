defmodule Cure.Compiler.SyntaxFamilyDefinitionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "an unnested syntax-family body points from the header to the next macro entry" do
    source = "macro Build\n  syntax family Definition\n  accepts Definition\n"
    {diagnostic, registry} = diagnostic(source, "family_indent.cure")

    assert diagnostic.key == :syntax_family_indent_missing

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SYNTAX FAMILY BODY MUST BE INDENTED [E094] --------------- family_indent.cure

             The fields, included families, and productions of `Definition` must be nested
             below its `syntax family` declaration.

             A valid continuation here starts with an indented block.

             at family_indent.cure:3:3
             2 |   syntax family Definition
               |   ------        ---------- this syntax family declaration starts here; the syntax family header ends here
             3 |   accepts Definition
               |   ^ indent the syntax family members below this declaration

             Hint: Indent one or more family members below the declaration
             """)

    assert diagnostic.suggestions == [
             %Cure.Diagnostic.Suggestion{
               message: "Indent one or more family members below the declaration",
               applicability: :manual,
               edits: []
             }
           ]

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 2},
             "end" => %{"line" => 2, "character" => 2}
           }
  end

  test "an invalid syntax-family member has its own range and valid continuations" do
    source = "macro Build\n  syntax family Definition\n    42\n"
    {diagnostic, registry} = diagnostic(source, "family_member.cure")

    assert diagnostic.key == :syntax_family_member_invalid

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SYNTAX FAMILY MEMBER IS INVALID [E094] ------------------- family_member.cure

             '42' cannot declare a member of the `Definition` syntax family. Write a typed
             field, `includes Family`, or a `syntax` production.

             A valid continuation here starts with a typed field or 'includes' or 'syntax'.

             at family_member.cure:3:5
             2 |   syntax family Definition
               |   ------        ---------- this syntax family declaration starts here; the syntax family header ends here
             3 |     42
               |     ^^ write a field, include, or production here

             Hint: Replace this line with a typed field, an `includes` line, or a `syntax` production
             """)

    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column,
            diagnostic.primary.span.end_column} == {3, 5, 7}

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 4},
             "end" => %{"line" => 2, "character" => 6}
           }
  end

  defp diagnostic(source, file) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, file: file, emit_events: false)
    error = Enum.find(errors, &match?({:syntax_family_definition_syntax, _}, &1))
    assert error
    Errors.to_diagnostic({:parse_error, [error]}, file, source)
  end
end
