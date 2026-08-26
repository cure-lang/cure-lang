defmodule Cure.Compiler.RefinementDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:refinement_type_syntax, _}, &1))
    assert {:refinement_type_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an invalid binder is blamed at the authored token" do
    source = "typealias P = {42: Int | true}"
    {error, {diagnostic, registry}} = diagnostic(source, "refine_binder.cure")
    assert {:refinement_type_syntax, %{kind: :refinement_binder_invalid}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REFINEMENT BINDER NEEDS A NAME [E094] -------------------- refine_binder.cure

             42 cannot name the value refined by this type. Use a lower-case name such as
             `value`.

             A valid continuation here starts with an identifier.

             at refine_binder.cure:1:16
             1 | typealias P = {42: Int | true}
               |               -^^ this refinement type starts here; write a lower-case refinement binder here

             Hint: Replace this with a descriptive lower-case binder
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "a missing colon gets an exact insertion" do
    source = "typealias P = {x Int | true}"
    {error, {diagnostic, registry}} = diagnostic(source, "refine_colon.cure")
    assert {:refinement_type_syntax, %{kind: :refinement_colon_missing}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REFINEMENT BINDER NEEDS A COLON [E094] -------------------- refine_colon.cure

             A refinement binder must be followed by `:` and the base type whose values it
             describes.

             A valid continuation here starts with ':'.

             at refine_colon.cure:1:18
             1 | typealias P = {x Int | true}
               |               -- ^ this refinement type starts here; this is the refinement binder; insert `:` before the base type

             Hint: Insert `:` before the refinement's base type
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 17
    assert insertion.end_byte == 17
  end

  test "a missing proposition separator labels binder and base type" do
    source = "typealias P = {x: Int true}"
    {error, {diagnostic, registry}} = diagnostic(source, "refine_bar.cure")
    assert {:refinement_type_syntax, %{kind: :refinement_bar_missing}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REFINEMENT TYPE NEEDS A SEPARATOR [E094] -------------------- refine_bar.cure

             A refinement type uses `|` between its base type and the proposition values must
             satisfy.

             A valid continuation here starts with '|'.

             at refine_bar.cure:1:23
             1 | typealias P = {x: Int true}
               |               --  --- ^ this refinement type starts here; this is the refinement binder; the base type ends here; insert `|` before the proposition

             Hint: Insert `|` before the refinement proposition
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "| ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 22
    assert insertion.end_byte == 22

    assert [%{"newText" => "| ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 22},
             "end" => %{"line" => 0, "character" => 22}
           }
  end

  test "an unclosed refinement labels its proposition and inserts a brace" do
    source = "typealias P = {x: Int | true"
    {error, {diagnostic, registry}} = diagnostic(source, "refine_close.cure")
    assert {:refinement_type_syntax, %{kind: :refinement_unclosed}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REFINEMENT TYPE IS NOT CLOSED [E094] ---------------------- refine_close.cure

             This refinement type reaches the end of its container without the '}' that
             closes its proposition.

             A valid continuation here starts with '}'.

             at refine_close.cure:1:29
             1 | typealias P = {x: Int | true
               |               --        ----^ this refinement type starts here; this is the refinement binder; the proposition ends here; close this refinement type with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 3
  end

  test "a mismatched refinement closer labels the complete authored type and replaces it" do
    source = "typealias P = {x: Int | true]"
    {error, {diagnostic, registry}} = diagnostic(source, "refine_mismatch.cure")

    assert {:refinement_type_syntax,
            %{kind: :mismatched_closer, family: :refinement_type, expected: :rbrace, observed: "]"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REFINEMENT TYPE HAS THE WRONG CLOSER [E094] ------------ refine_mismatch.cure

             This refinement type starts with '{', so ']' cannot close it. Use '}' after the
             proposition.

             at refine_mismatch.cure:1:29
             1 | typealias P = {x: Int | true]
               |               --        ----^ this refinement type starts here; this is the refinement binder; the proposition ends here; replace this with `}`

             Hint: Replace ']' with `}`
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: replacement}]}] =
             diagnostic.suggestions

    assert {replacement.start_column, replacement.end_column} == {29, 30}
  end
end
