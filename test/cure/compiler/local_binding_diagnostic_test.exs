defmodule Cure.Compiler.LocalBindingDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :local_binding_assign_missing}}, &1))
    assert {:declaration_separator_missing, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a let binding labels its pattern and annotation and inserts equals" do
    source = "let x: Int 1"
    {error, {diagnostic, registry}} = diagnostic(source, "let_assign.cure")

    assert {:declaration_separator_missing, %{kind: :local_binding_assign_missing, family: :let, declaration: "x"}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LET BINDING NEEDS AN EQUALS SIGN [E094] --------------------- let_assign.cure

             The `let` binding for `x` needs `=` before the value it binds.

             A valid continuation here starts with '='.

             at let_assign.cure:1:12
             1 | let x: Int 1
               | --- ------ ^ this let binding starts here; this is the binding pattern; the binding head ends here; insert `=` before this binding value

             Hint: Insert `=` before the binding value
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "= ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 12}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "= ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 11},
             "end" => %{"line" => 0, "character" => 11}
           }
  end

  test "a have binding retains its distinct title and authored name" do
    source = "have witness: Int 1"
    {error, {diagnostic, registry}} = diagnostic(source, "have_assign.cure")

    assert {:declaration_separator_missing,
            %{kind: :local_binding_assign_missing, family: :have, declaration: "witness"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- HAVE BINDING NEEDS AN EQUALS SIGN [E094] ------------------- have_assign.cure

             The `have` binding for `witness` needs `=` before the value it binds.

             A valid continuation here starts with '='.

             at have_assign.cure:1:19
             1 | have witness: Int 1
               | ---- ------------ ^ this have binding starts here; this is the binding pattern; the binding head ends here; insert `=` before this binding value

             Hint: Insert `=` before the binding value
             """)
  end

  test "an absent binding value does not receive a partial machine edit" do
    {_error, {diagnostic, _registry}} = diagnostic("let x", "let_eof.cure")
    assert diagnostic.suggestions == []
  end
end
