defmodule Cure.Compiler.SendDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :send_comma_missing}}, &1))
    assert {:declaration_separator_missing, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a keyword send without its comma labels the target and inserts the separator" do
    source = "send worker message"
    {error, {diagnostic, registry}} = diagnostic(source, "send_comma.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :send_comma_missing,
              expected: :comma,
              observed: "message",
              token_type: :identifier
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SEND NEEDS A COMMA [E094] ----------------------------------- send_comma.cure

             The keyword `send` form needs `,` between its target and message.

             A valid continuation here starts with ','.

             at send_comma.cure:1:13
             1 | send worker message
               | ---- ------ ^ this send starts here; the send target ends here; insert a comma before this message

             Hint: Insert `,` before the send message
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 13}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 12},
             "end" => %{"line" => 0, "character" => 12}
           }
  end

  test "an absent message does not receive a partial comma-only edit" do
    {_error, {diagnostic, _registry}} = diagnostic("send worker", "send_eof.cure")
    assert diagnostic.suggestions == []
  end

  test "a correctly separated keyword send preserves its AST" do
    {:ok, tokens} = Lexer.tokenize("send worker, message", emit_events: false)

    assert {:ok, {:send, meta, [{:variable, _target_meta, "worker"}, {:variable, _message_meta, "message"}]}} =
             Parser.parse(tokens, emit_events: false)

    assert meta[:melquiades_form] == :keyword
  end
end
