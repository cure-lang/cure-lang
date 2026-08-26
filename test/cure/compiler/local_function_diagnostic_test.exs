defmodule Cure.Compiler.LocalFunctionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "a local function missing `fn` identifies the declaration and inserts it" do
    source = "local helper(x: Int) -> Int = x\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "local_fn.cure", emit_events: false)
    assert {:error, [error]} = Parser.parse(tokens, emit_events: false)

    assert {:declaration_separator_missing,
            %{
              kind: :local_function_keyword_missing,
              expected: :fn,
              observed: "helper",
              token_type: :identifier,
              span: %Cure.Diagnostic.Span{} = span,
              opener_span: %Cure.Diagnostic.Span{},
              previous_span: %Cure.Diagnostic.Span{},
              line: 1,
              column: 7
            }} = error

    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, "local_fn.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LOCAL FUNCTION NEEDS `FN` [E094] ------------------------------ local_fn.cure

             A private function declaration must put `fn` between `local` and the function
             name.

             A valid continuation here starts with 'fn'.

             at local_fn.cure:1:7
             1 | local helper(x: Int) -> Int = x
               | ----- ^^^^^^ this starts a private declaration; insert `fn` before this function name

             Hint: Insert `fn` before the local function name
             """)

    assert [%{"edits" => [edit], "applicability" => "machine_applicable"}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"]

    assert edit == %{
             "newText" => "fn ",
             "uri" => "file://#{Path.expand("local_fn.cure")}",
             "range" => %{
               "start" => %{"line" => 0, "character" => 6},
               "end" => %{"line" => 0, "character" => 6}
             }
           }

    assert span.start_column == 7
  end
end
