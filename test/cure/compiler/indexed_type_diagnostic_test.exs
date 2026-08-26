defmodule Cure.Compiler.IndexedTypeDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, fn
        {:indexed_type_syntax, _} -> true
        {:container_elements_syntax, %{container: :type_indices}} -> true
        _ -> false
      end)

    assert {_, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a missing index-list opener gets an exact insertion" do
    source = "type Vec indices n: Type)\n"
    {error, {diagnostic, registry}} = diagnostic(source, "indices_open.cure")
    assert {:indexed_type_syntax, %{kind: :type_indices_opener_missing, declaration: "Vec"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE INDICES NEED PARENTHESES [E094] ---------------------- indices_open.cure

             The indexed type `Vec` must put its index telescope inside parentheses after
             `indices`.

             A valid continuation here starts with '('.

             at indices_open.cure:1:18
             1 | type Vec indices n: Type)
               |          ------- ^ the index telescope follows this keyword; insert `(` before the first type index

             Hint: Insert `(` before the type indices
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "(", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 18}
    assert insertion.start_byte == insertion.end_byte
  end

  test "a missing index opener and closer reports only the owned opener problem" do
    source = "type Vec indices n: Type\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "indices_recovery.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert Enum.any?(errors, &match?({:indexed_type_syntax, %{kind: :type_indices_opener_missing}}, &1))
    refute Enum.any?(errors, &match?({:expected_token, :rparen, _, _, _, _, _}, &1))
  end

  test "an unclosed index telescope labels its opener and final index" do
    source = "type Vec indices (n: Type"
    {error, {diagnostic, registry}} = diagnostic(source, "indices_close.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :type_indices, declaration: "Vec"}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE INDEX LIST IS NOT CLOSED [E094] --------------------- indices_close.cure

             The indexed type `Vec` reaches the end of its index telescope without the
             closing ')'.

             at indices_close.cure:1:26
             1 | type Vec indices (n: Type
               |                  --------^ these type indices start here; the previous type index ends here; close these type indices with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
  end

  test "adjacent indices get a zero-width comma insertion and LSP edit" do
    source = "type Vec indices (n: Type m: Type)\n"
    {error, {diagnostic, registry}} = diagnostic(source, "indices_comma.cure")

    assert {:container_elements_syntax,
            %{kind: :container_separator_missing, container: :type_indices, declaration: "Vec"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE INDICES NEED A COMMA [E094] ------------------------- indices_comma.cure

             The indexed type `Vec` has another index here, but consecutive indices must be
             separated by a comma.

             at indices_comma.cure:1:27
             1 | type Vec indices (n: Type m: Type)
               |                  -------- ^ these type indices start here; the previous type index ends here; insert a comma before this type index

             Hint: Insert `,` between these type indices
             """)

    assert [%{edits: [%{replacement: ", ", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {1, 27}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 26},
             "end" => %{"line" => 0, "character" => 26}
           }
  end
end
