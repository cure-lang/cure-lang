defmodule Cure.Compiler.MacroObligationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file, kind) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, fn
        {:container_elements_syntax, %{kind: ^kind, container: :macro_obligation_capture}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax, _} = error
    {error, Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an obligation without an opening parenthesis points at its capture" do
    source =
      "macro Checked\n  syntax child <id: Expression> where BeamEncode id) becomes id\n"

    {error, {diagnostic, registry}} =
      diagnostic(source, "obligation_open.cure", :container_opener_missing)

    assert {:container_elements_syntax,
            %{
              kind: :container_opener_missing,
              container: :macro_obligation_capture,
              interface: "BeamEncode",
              expected: :lparen,
              observed: "id"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO OBLIGATION NEEDS PARENTHESES [E094] -------------- obligation_open.cure

             The `BeamEncode` obligation must put the capture it constrains inside
             parentheses.

             A valid continuation here starts with '('.

             at obligation_open.cure:2:50
             2 |   syntax child <id: Expression> where BeamEncode id) becomes id
               |                                 ----- ---------- ^ this obligation starts here; this is the required interface; insert `(` before this capture

             Hint: Insert `(` before the constrained capture
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "(", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 50}
  end

  test "an obligation closes before the rule verb" do
    source =
      "macro Checked\n  syntax child <id: Expression> where BeamEncode(id becomes id\n"

    {error, {diagnostic, registry}} =
      diagnostic(source, "obligation_close.cure", :container_unclosed)

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :macro_obligation_capture,
              interface: "BeamEncode",
              capture: "id",
              expected: :rparen,
              observed: "becomes"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO OBLIGATION IS NOT CLOSED [E094] ----------------- obligation_close.cure

             The `BeamEncode` obligation for `id` is missing the ')' that closes its capture.

             at obligation_close.cure:2:53
             2 |   syntax child <id: Expression> where BeamEncode(id becomes id
               |                                 ----- ------------- ^ this obligation starts here; this is the required interface; the capture starts here; the capture ends here; close this obligation with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 53}

    assert [%{"newText" => ")", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 1, "character" => 52},
             "end" => %{"line" => 1, "character" => 52}
           }
  end

  test "a parenthesized obligation still records its interface and capture" do
    source =
      "macro Checked\n  syntax child <id: Expression> where BeamEncode(id) becomes id\n"

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
  end
end
