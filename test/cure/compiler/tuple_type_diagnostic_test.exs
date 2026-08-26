defmodule Cure.Compiler.TupleTypeDiagnosticTest do
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

  test "Tuple(...) reports its exact opener, previous position, and missing closer" do
    source = "typealias P = Tuple(Int"
    {error, {diagnostic, registry}} = diagnostic(source, "tuple_close.cure")
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :tuple_type}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE TYPE IS NOT CLOSED [E094] ---------------------------- tuple_close.cure

             This tuple type reaches the end of the source without the ')' that closes its
             positions.

             at tuple_close.cure:1:24
             1 | typealias P = Tuple(Int
               |                    ----^ this tuple type starts here; the previous type position ends here; close this tuple type with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
  end

  test "Tuple(...) inserts a missing comma at the next position" do
    source = "typealias P = Tuple(Int Bool)"
    {error, {diagnostic, registry}} = diagnostic(source, "tuple_comma.cure")

    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :tuple_type}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE TYPE POSITIONS NEED A COMMA [E094] ------------------- tuple_comma.cure

             This type has another position here, but consecutive type positions must be
             separated by a comma.

             at tuple_comma.cure:1:25
             1 | typealias P = Tuple(Int Bool)
               |                    ---- ^ this tuple type starts here; the previous type position ends here; insert a comma before this type position

             Hint: Insert `,` between these type positions
             """)

    assert [%{edits: [%{replacement: ", ", span: insertion}]}] = diagnostic.suggestions
    assert insertion.start_byte == 24
    assert insertion.end_byte == 24

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 24},
             "end" => %{"line" => 0, "character" => 24}
           }
  end

  test "%[...] uses its authored bracket delimiter" do
    source = "typealias P = %[Int"
    {error, {diagnostic, registry}} = diagnostic(source, "sigil_close.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :tuple_type_sigil}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE TYPE IS NOT CLOSED [E094] ---------------------------- sigil_close.cure

             This tuple type reaches the end of the source without the ']' that closes its
             positions.

             at sigil_close.cure:1:20
             1 | typealias P = %[Int
               |               -----^ this tuple type starts here; the previous type position ends here; close this tuple type with `]`

             Hint: Insert `]` to close the construct
             """)

    assert [%{edits: [%{replacement: "]"}]}] = diagnostic.suggestions
  end

  test "grouped types distinguish their positions from expression elements" do
    source = "typealias P = (Int Bool) -> Int"
    {error, {diagnostic, registry}} = diagnostic(source, "group_comma.cure")

    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :grouped_type}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- GROUPED TYPE POSITIONS NEED A COMMA [E094] ----------------- group_comma.cure

             This type has another position here, but consecutive type positions must be
             separated by a comma.

             at group_comma.cure:1:20
             1 | typealias P = (Int Bool) -> Int
               |               ---- ^ this grouped type starts here; the previous type position ends here; insert a comma before this type position

             Hint: Insert `,` between these type positions
             """)
  end

  test "a grouped higher-order constructor type retains its GADT source context" do
    source = "mod M\n  type A = MkA\n  type Box indices ()\n    MkBox : ((A) -> A -> Box\n"
    {error, {diagnostic, registry}} = diagnostic(source, "gadt_group.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :grouped_type, token_type: :dedent}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- GROUPED TYPE IS NOT CLOSED [E094] --------------------------- gadt_group.cure

             This grouped type reaches the end of the source without the ')' that closes its
             positions.

             at gadt_group.cure:5:1
             4 |     MkBox : ((A) -> A -> Box
               |             -            --- this grouped type starts here; the previous type position ends here
             5 |#{" "}
               | ^ close this grouped type with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {5, 1}
  end
end
