defmodule Cure.Compiler.InlineBranchBlockDiagnosticTest do
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

  test "an unclosed inline match labels its opener and complete final branch" do
    source = "match x { 0 -> 1"
    {error, {diagnostic, registry}} = diagnostic(source, "match_block.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :branch_block, family: :match}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN BRANCH BLOCK IS NOT CLOSED [E094] ------------------ match_block.cure

             This inline `match` reaches the end of its branches without the closing '}'.

             at match_block.cure:1:17
             1 | match x { 0 -> 1
               |         - ------^ this inline match's branch block starts here; the final branch ends here; close this branch block with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)

    assert [%{"newText" => "}", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 16},
             "end" => %{"line" => 0, "character" => 16}
           }
  end

  test "an unclosed single-scrutinee with retains its branch family" do
    source = "with x { 0 -> 1"
    {error, {diagnostic, registry}} = diagnostic(source, "with_block.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :branch_block, family: :with}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH BRANCH BLOCK IS NOT CLOSED [E094] ---------------------- with_block.cure

             This inline `with` reaches the end of its branches without the closing '}'.

             at with_block.cure:1:16
             1 | with x { 0 -> 1
               |        - ------^ this inline with's branch block starts here; the final branch ends here; close this branch block with `}`

             Hint: Insert `}` to close the construct
             """)
  end

  test "an unclosed multi-scrutinee with labels the complete authored branch" do
    source = "with x y { 0, 0 -> 1"
    {error, {diagnostic, registry}} = diagnostic(source, "multi_with_block.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :branch_block,
              family: :multi_with,
              previous_span: previous
            }} = error

    assert {previous.start_column, previous.end_column} == {12, 21}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH BRANCH BLOCK IS NOT CLOSED [E094] ---------------- multi_with_block.cure

             This multi-scrutinee `with` reaches the end of its branches without the closing
             '}'.

             at multi_with_block.cure:1:21
             1 | with x y { 0, 0 -> 1
               |          - ---------^ this multi-scrutinee with's branch block starts here; the final branch ends here; close this branch block with `}`

             Hint: Insert `}` to close the construct
             """)
  end

  test "correctly closed inline branch blocks remain accepted" do
    for source <- [
          "match x { 0 -> 1 }",
          "with x { 0 -> 1 }",
          "with x y { 0, 0 -> 1 }"
        ] do
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end
  end
end
