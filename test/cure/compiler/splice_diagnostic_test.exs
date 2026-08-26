defmodule Cure.Compiler.SpliceDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(
        errors,
        &match?(
          {:container_elements_syntax, %{kind: :container_unclosed, container: container}}
          when container in [:splice, :splice_group],
          &1
        )
      )

    assert {:container_elements_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an unclosed single splice points after its expression and inserts a parenthesis" do
    source = "$(value"
    {error, {diagnostic, registry}} = diagnostic(source, "splice_close.cure")

    assert {:container_elements_syntax,
            %{kind: :container_unclosed, container: :splice, expected: :rparen, observed: :eof}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SYNTAX SPLICE IS NOT CLOSED [E094] ------------------------ splice_close.cure

             This splice reaches the end of its expression without the closing ')'.

             at splice_close.cure:1:8
             1 | $(value
               | -------^ the syntax splice starts here; the spliced expression ends here; close this syntax splice with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 8}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ")", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 7}
           }
  end

  test "an unclosed group splice keeps its distinct producer identity" do
    {error, {diagnostic, registry}} = diagnostic("$(items ...", "group_splice_close.cure")

    assert {:container_elements_syntax,
            %{kind: :container_unclosed, container: :splice_group, expected: :rparen, observed: :eof}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SYNTAX SPLICE IS NOT CLOSED [E094] ------------------ group_splice_close.cure

             This group splice reaches the end of its expression without the closing ')'.

             at group_splice_close.cure:1:12
             1 | $(items ...
               | -------    ^ the syntax splice starts here; the spliced expression ends here; close this syntax splice with `)`

             Hint: Insert `)` to close the construct
             """)
  end

  test "closed single and group splices preserve their AST forms" do
    for {source, tag} <- [{"$(value)", :splice}, {"$(items ...)", :splice_group}] do
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, {^tag, _meta, [_expression]}} = Parser.parse(tokens, emit_events: false)
    end
  end
end
