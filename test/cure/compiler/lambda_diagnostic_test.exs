defmodule Cure.Compiler.LambdaDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer

  test "an end-terminated lambda labels its opener and exact insertion point" do
    source = "fn (x) -> x; x;"

    assert {:error, {:parse_error, [{:lambda_block_unterminated, details}]}} =
             Cure.Compiler.compile_string(source, file: "lambda.cure", emit_events: false)

    assert details.expected == :end
    assert details.observed == :eof
    assert details.span.start_byte == byte_size(source)
    assert details.span.end_byte == byte_size(source)
    assert details.opener_span.start_byte == 0
    assert details.opener_span.end_byte == 2

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:parse_error, [{:lambda_block_unterminated, details}]},
        "lambda.cure",
        source
      )

    assert diagnostic.code == "E035"

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA BODY IS NOT CLOSED [E035] -------------------------------- lambda.cure

             This multi-statement lambda body reaches the end of its container without a
             closing delimiter.

             A valid continuation here starts with 'end'.

             at lambda.cure:1:16
             1 | fn (x) -> x; x;
               | --             ^ this lambda starts here; the unclosed body reaches here

             Hint: Insert `end` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [edit]}] = diagnostic.suggestions
    assert edit.replacement == "end"
    assert edit.span == details.span
    assert {:ok, _module, _warnings} = Cure.Compiler.compile_string(source <> edit.replacement, emit_events: false)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 0, "character" => 15},
             "end" => %{"line" => 0, "character" => 15}
           }

    assert [related] = lsp["relatedInformation"]
    assert related["message"] == "this lambda starts here"

    assert related["location"]["range"] == %{
             "start" => %{"line" => 0, "character" => 0},
             "end" => %{"line" => 0, "character" => 2}
           }

    assert [suggestion] = lsp["data"]["suggestions"]
    assert suggestion["applicability"] == "machine_applicable"
    assert [%{"newText" => "end", "range" => edit_range}] = suggestion["edits"]
    assert edit_range == lsp["range"]
  end

  test "a brace-delimited lambda labels its brace, final expression, and closing edit" do
    source = "fn(x) -> { x; x"

    assert {:error, {:parse_error, [{:lambda_block_unterminated, details}]}} =
             Cure.Compiler.compile_string(source, file: "brace_lambda.cure", emit_events: false)

    assert details.expected == :rbrace
    assert details.observed == :eof
    assert details.body_style == :brace
    assert details.opener_span.start_byte == 9
    assert details.opener_span.end_byte == 10
    assert details.previous_span.start_byte == 14
    assert details.previous_span.end_byte == 15

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:parse_error, [{:lambda_block_unterminated, details}]},
        "brace_lambda.cure",
        source
      )

    assert diagnostic.code == "E035"

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA BODY IS NOT CLOSED [E035] -------------------------- brace_lambda.cure

             This brace-delimited lambda body reaches the end of its container without the
             '}' that closes it.

             A valid continuation here starts with '}'.

             at brace_lambda.cure:1:16
             1 | fn(x) -> { x; x
               |          -    -^ this lambda body starts here; the previous body expression ends here; close this lambda body with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [edit]}] = diagnostic.suggestions
    assert edit.replacement == "}"
    assert edit.span == details.span

    assert {:ok, _module, _warnings} =
             Cure.Compiler.compile_string(source <> edit.replacement, emit_events: false)

    lsp = Renderer.lsp(diagnostic, registry)
    assert length(lsp["relatedInformation"]) == 2
    assert [%{"newText" => "}", "range" => edit_range}] = lsp["data"]["suggestions"] |> hd() |> Map.fetch!("edits")
    assert edit_range == lsp["range"]
  end
end
