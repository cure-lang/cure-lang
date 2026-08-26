defmodule Cure.Compiler.ConstructorDomainDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an unclosed named constructor domain labels its binder and type" do
    source = "mod M\n  type A = MkA\n  type Box indices ()\n    Mk : (x: A\n"
    {error, {diagnostic, registry}} = diagnostic(source, "named_domain.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :named_constructor_domain}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NAMED CONSTRUCTOR DOMAIN IS NOT CLOSED [E094] ------------- named_domain.cure

             This named constructor domain reaches the end of the declaration without its
             closing ')'.

             at named_domain.cure:5:1
             4 |     Mk : (x: A
               |          --  - this named constructor domain starts here; this is the dependent argument binder; the argument type ends here
             5 |#{" "}
               | ^ close this named constructor domain with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {5, 1}
  end

  test "an unclosed implicit constructor domain inserts before the newline" do
    source = "mod M\n  type A = MkA\n  type Box indices ()\n    Mk : {x: A\n"
    {error, {diagnostic, registry}} = diagnostic(source, "implicit_domain.cure")

    assert {:container_elements_syntax,
            %{kind: :container_unclosed, container: :implicit_constructor_domain, token_type: :newline}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLICIT CONSTRUCTOR DOMAIN IS NOT CLOSED [E094] ------- implicit_domain.cure

             This implicit constructor domain reaches the end of the declaration without its
             closing '}'.

             at implicit_domain.cure:4:15
             4 |     Mk : {x: A
               |          --  -^ this implicit constructor domain starts here; this is the dependent argument binder; the argument type ends here; close this implicit constructor domain with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{edits: [%{replacement: "}", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {4, 15}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "}", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 3, "character" => 14},
             "end" => %{"line" => 3, "character" => 14}
           }
  end
end
