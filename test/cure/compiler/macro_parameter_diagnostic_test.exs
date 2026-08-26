defmodule Cure.Compiler.MacroParameterDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file, pattern) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, pattern)
    assert error
    {error, Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a failure declaration without an opening parenthesis gets a precise insertion" do
    source = "macro Checked\n  fail Wrong value: Int)\n"

    {error, {diagnostic, registry}} =
      diagnostic(source, "fail_open.cure", fn
        {:container_elements_syntax, %{kind: :container_opener_missing, container: :failure_parameters}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax,
            %{
              kind: :container_opener_missing,
              container: :failure_parameters,
              declaration: "Wrong",
              expected: :lparen,
              observed: "value"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO PARAMETER LIST IS MISSING [E094] ----------------------- fail_open.cure

             The macro declaration `Wrong` must put its parameters inside parentheses.

             A valid continuation here starts with '('.

             at fail_open.cure:2:14
             2 |   fail Wrong value: Int)
               |   ---- ----- ^ this failure declaration starts here; this is its name; open this parameter list with `(`

             Hint: Insert `(` before the first parameter
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "(", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 14}
  end

  test "an unclosed failure parameter list points at the authored list" do
    source = "macro Checked\n  fail Wrong(value: Int\n"

    {error, {diagnostic, registry}} =
      diagnostic(source, "fail_close.cure", fn
        {:container_elements_syntax, %{kind: :container_unclosed, container: :failure_parameters}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :failure_parameters, expected: :rparen}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FAILURE PARAMETER LIST IS NOT CLOSED [E094] ----------------- fail_close.cure

             The parameter list for `Wrong` reaches its body without the closing ')'.

             at fail_close.cure:3:1
             2 |   fail Wrong(value: Int
               |   ---- ---------------- this failure declaration starts here; this is its name; the parameter list starts here; the previous parameter ends here
             3 | 
               | ^ close this macro parameter list with `)`

             Hint: Insert `)` to close the construct
             """)
  end

  test "a lifted callback closes its parameters before a return annotation" do
    source =
      "lift module Cure.Generated.X\n  callback init(arg: Int returns Int = arg\n"

    {error, {diagnostic, registry}} =
      diagnostic(source, "callback_close.cure", fn
        {:container_elements_syntax, %{kind: :container_unclosed, container: :lift_callback_parameters}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :lift_callback_parameters,
              expected: :rparen,
              observed: "returns"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LIFTED CALLBACK PARAMETER LIST IS NOT CLOSED [E094] ----- callback_close.cure

             The parameter list for `init` reaches its body without the closing ')'.

             at callback_close.cure:2:26
             2 |   callback init(arg: Int returns Int = arg
               |   -------- ------------- ^ this lifted callback starts here; this is its name; the parameter list starts here; the previous parameter ends here; close this macro parameter list with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {2, 26}
  end

  test "unannotated and annotated lifted callbacks retain distinct separators" do
    cases = [
      {"callback_arrow.cure", "lift module Cure.Generated.X\n  callback init(arg: Int) arg\n", false, :arrow,
       "Lifted callback needs an arrow", "-> ", 27},
      {"callback_equals.cure", "lift module Cure.Generated.X\n  callback init(arg: Int) returns Int arg\n", true,
       :assign, "Lifted callback needs an equals sign", "= ", 39}
    ]

    for {file, source, annotated, expected, title, replacement, column} <- cases do
      {error, {diagnostic, registry}} =
        diagnostic(source, file, fn
          {:declaration_separator_missing, %{kind: :lift_callback_body_separator_missing}} -> true
          _ -> false
        end)

      assert {:declaration_separator_missing,
              %{
                kind: :lift_callback_body_separator_missing,
                declaration: :init,
                annotated: ^annotated,
                expected: ^expected,
                observed: "arg"
              }} = error

      assert diagnostic.title == title

      rendered = Renderer.plain(diagnostic, registry, width: 80)

      if file == "callback_arrow.cure" do
        assert rendered ==
                 String.trim_trailing("""
                 -- LIFTED CALLBACK NEEDS AN ARROW [E094] ------------------- callback_arrow.cure

                 The lifted callback `init` needs `->` between its parameter list and body.

                 A valid continuation here starts with '->'.

                 at callback_arrow.cure:2:27
                 2 |   callback init(arg: Int) arg
                   |   -------- ----           ^ this lifted callback starts here; this is the callback name; insert `->` before this callback body

                 Hint: Insert `->` before the callback body
                 """)
      else
        assert rendered ==
                 String.trim_trailing("""
                 -- LIFTED CALLBACK NEEDS AN EQUALS SIGN [E094] ------------ callback_equals.cure

                 The lifted callback `init` needs `=` between its declared return type and body.

                 A valid continuation here starts with '='.

                 at callback_equals.cure:2:39
                 2 |   callback init(arg: Int) returns Int arg
                   |   -------- ----                   --- ^ this lifted callback starts here; this is the callback name; the callback head ends here; insert `=` before this callback body

                 Hint: Insert `=` before the callback body
                 """)
      end

      assert [%{applicability: :machine_applicable, edits: [%{replacement: ^replacement, span: insertion}]}] =
               diagnostic.suggestions

      assert {insertion.start_line, insertion.start_column} == {2, column}

      assert [%{"newText" => ^replacement, "range" => edit_range}] =
               Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

      assert edit_range["start"] == %{"line" => 1, "character" => column - 1}
      assert edit_range["end"] == edit_range["start"]
    end
  end

  test "valid failure declarations and lifted callbacks preserve their forms" do
    sources = [
      "macro Checked\n  fail Wrong(value: Int)\n",
      "lift module Cure.Generated.X\n  callback init(arg: Int) -> arg\n",
      "lift module Cure.Generated.X\n  callback init(arg: Int) returns Int = arg\n"
    ]

    for source <- sources do
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end
  end
end
