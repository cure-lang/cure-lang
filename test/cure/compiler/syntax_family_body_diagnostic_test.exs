defmodule Cure.Compiler.SyntaxFamilyBodyDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  test "a non-field entry lists the resolved family's valid fields" do
    source = """
    mod M
      macro complete <name: ModuleName>
        syntax family Definition
          state Type
          optional initial Expression
        accepts Definition
        expands with expand
      complete Broken
        state Int
        42
    """

    {diagnostic, registry} = diagnostic(source, "family_entry.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- STRUCTURED MACRO ENTRY IS INVALID [E094] ------------------ family_entry.cure

             '42' does not start a field of the `Definition` structured macro body. Valid
             fields are `state`, `initial`.

             A valid continuation here starts with 'state' or 'initial'.

             at family_entry.cure:10:5
              9 |     state Int
                |           --- the previous structured entry ends here
             10 |     42
                |     ^^ start this entry with a valid structured field

             Hint: Start this entry with one of: `state`, `initial`
             """)

    assert diagnostic.payload.context.valid_fields == ["state", "initial"]

    assert [%{message: "Start this entry with one of: `state`, `initial`", applicability: :manual, edits: []}] =
             diagnostic.suggestions

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 9, "character" => 4},
             "end" => %{"line" => 9, "character" => 6}
           }
  end

  test "an invalid nested row names its field and owning production family" do
    source = """
    mod M
      macro machine <name: ModuleName>
        syntax family Transition
          syntax <from: Name> to <dest: Name>
        syntax family Definition
          one_or_more transitions Transition
        accepts Definition
        expands with build
      machine Turnstile
        transitions
          42
    """

    {diagnostic, registry} = diagnostic(source, "family_production.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- STRUCTURED MACRO PRODUCTION IS INVALID [E094] -------- family_production.cure

             '42' does not match any production accepted by `transitions` in `Transition`.
             Follow one of the forms declared by that syntax family.

             A valid continuation here starts with a declared family production.

             at family_production.cure:11:7
             10 |     transitions
                |     ----------- the previous structured entry ends here
             11 |       42
                |       ^^ this does not match a declared family production

             Hint: Rewrite this entry using one of the syntax family's declared production forms
             """)

    assert diagnostic.payload.context.field == "transitions"
    assert diagnostic.payload.context.family == "Transition"
    assert [%{message: message, applicability: :manual, edits: []}] = diagnostic.suggestions
    assert message =~ "declared production forms"

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 10, "character" => 6},
             "end" => %{"line" => 10, "character" => 8}
           }
  end

  defp diagnostic(source, file) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, file: file, emit_events: false)
    error = Enum.find(errors, &match?({:syntax_family_body_syntax, _}, &1))
    assert error
    Errors.to_diagnostic({:parse_error, [error]}, file, source)
  end
end
