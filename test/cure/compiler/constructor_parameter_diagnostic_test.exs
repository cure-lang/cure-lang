defmodule Cure.Compiler.ConstructorParameterDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:container_elements_syntax, _}, &1))
    assert {:container_elements_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "adjacent constructor parameters get an exact comma insertion" do
    source = "type Pair = Pair(Int Bool)"
    {error, {diagnostic, registry}} = diagnostic(source, "ctor_params_comma.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_separator_missing,
              container: :constructor_parameters,
              constructor: "Pair"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CONSTRUCTOR PARAMETERS NEED A COMMA [E094] ----------- ctor_params_comma.cure

             The constructor `Pair` has another parameter type here, but consecutive
             parameters must be separated by a comma.

             at ctor_params_comma.cure:1:22
             1 | type Pair = Pair(Int Bool)
               |                 ---- ^ this constructor's parameter list starts here; the previous constructor parameter ends here; insert a comma before this constructor parameter

             Hint: Insert `,` between these constructor parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 22}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 21},
             "end" => %{"line" => 0, "character" => 21}
           }
  end

  test "an unclosed constructor parameter list owns its opener and final parameter" do
    source = "type Maybe = Some(Int"
    {error, {diagnostic, registry}} = diagnostic(source, "ctor_params_close.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :constructor_parameters,
              constructor: "Some",
              observed: :eof
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CONSTRUCTOR PARAMETER LIST IS NOT CLOSED [E094] ------ ctor_params_close.cure

             The constructor `Some` reaches the end of its parameter list without the closing
             ')'.

             at ctor_params_close.cure:1:22
             1 | type Maybe = Some(Int
               |                  ----^ this constructor's parameter list starts here; the previous constructor parameter ends here; close this constructor's parameters with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
  end
end
