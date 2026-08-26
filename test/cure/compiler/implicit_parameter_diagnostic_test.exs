defmodule Cure.Compiler.ImplicitParameterDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "a missing implicit-parameter brace is inserted before the next parameter" do
    source = "fn head({t: Type, xs: List(t)) -> t = xs"
    file = "implicit_param_close.cure"
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, %{container: :implicit_parameter}}, &1))

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :implicit_parameter,
              binder: "t",
              observed: ","
            }} = error

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLICIT PARAMETER IS NOT CLOSED [E094] ----------- implicit_param_close.cure

             The implicit parameter `t` reaches the end of its annotation without the closing
             '}'.

             at implicit_param_close.cure:1:17
             1 | fn head({t: Type, xs: List(t)) -> t = xs
               |         --  ----^ this implicit parameter starts here; this is the implicit parameter name; the parameter annotation ends here; close this implicit parameter with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 17}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "}", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 16},
             "end" => %{"line" => 0, "character" => 16}
           }
  end

  test "a correctly closed implicit parameter remains accepted" do
    source = "fn head({t: Type}, xs: List(t)) -> t = xs"
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
  end
end
