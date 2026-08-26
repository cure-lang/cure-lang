defmodule Cure.Compiler.SigmaTypeDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:sigma_type_syntax, _}, &1))
    assert {:sigma_type_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an invalid Sigma binder is blamed at the authored token" do
    source = "typealias P = Sigma(42: Int, Bool)"
    {error, {diagnostic, registry}} = diagnostic(source, "sigma_binder.cure")
    assert {:sigma_type_syntax, %{kind: :sigma_binder_invalid}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SIGMA BINDER NEEDS A NAME [E094] -------------------------- sigma_binder.cure

             42 cannot name the first value in this dependent pair. Use a lower-case binder
             such as `value`.

             A valid continuation here starts with an identifier.

             at sigma_binder.cure:1:21
             1 | typealias P = Sigma(42: Int, Bool)
               |                    -^^ this Sigma type starts here; write a lower-case Sigma binder here

             Hint: Replace this with a descriptive lower-case Sigma binder
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "a missing binder colon gets an exact insertion" do
    source = "typealias P = Sigma(x Int, Bool)"
    {error, {diagnostic, registry}} = diagnostic(source, "sigma_colon.cure")
    assert {:sigma_type_syntax, %{kind: :sigma_colon_missing}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SIGMA BINDER NEEDS A COLON [E094] -------------------------- sigma_colon.cure

             A Sigma binder must be followed by `:` and the type of its first value.

             A valid continuation here starts with ':'.

             at sigma_colon.cure:1:23
             1 | typealias P = Sigma(x Int, Bool)
               |                    -- ^ this Sigma type starts here; this is the Sigma binder; insert `:` before the first value's type

             Hint: Insert `:` before the first value's type
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 22
    assert insertion.end_byte == 22
  end

  test "a missing component comma labels the binder and domain" do
    source = "typealias P = Sigma(x: Int Bool)"
    {error, {diagnostic, registry}} = diagnostic(source, "sigma_comma.cure")
    assert {:sigma_type_syntax, %{kind: :sigma_comma_missing}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SIGMA TYPE NEEDS A SEPARATOR [E094] ------------------------ sigma_comma.cure

             A Sigma type uses `,` between the first value's type and the dependent type of
             its second value.

             A valid continuation here starts with ','.

             at sigma_comma.cure:1:28
             1 | typealias P = Sigma(x: Int Bool)
               |                    --  --- ^ this Sigma type starts here; this is the Sigma binder; the first value's type ends here; insert `,` before the dependent result type

             Hint: Insert `,` before the dependent result type
             """)

    assert [%{edits: [%{replacement: ", ", span: insertion}]}] = diagnostic.suggestions
    assert insertion.start_byte == 27
    assert insertion.end_byte == 27

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 27},
             "end" => %{"line" => 0, "character" => 27}
           }
  end

  test "an unclosed Sigma type labels its result and inserts the closer" do
    source = "typealias P = Sigma(x: Int, Bool"
    {error, {diagnostic, registry}} = diagnostic(source, "sigma_close.cure")
    assert {:sigma_type_syntax, %{kind: :sigma_unclosed}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SIGMA TYPE IS NOT CLOSED [E094] ---------------------------- sigma_close.cure

             This Sigma type reaches the end of the source without the ')' that closes its
             dependent pair.

             A valid continuation here starts with ')'.

             at sigma_close.cure:1:33
             1 | typealias P = Sigma(x: Int, Bool
               |                    --       ----^ this Sigma type starts here; this is the Sigma binder; the dependent result type ends here; close this Sigma type with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
  end

  test "a mismatched Sigma closer labels the complete authored type and replaces it" do
    source = "typealias P = Sigma(x: Int, Bool]"
    {error, {diagnostic, registry}} = diagnostic(source, "sigma_mismatch.cure")

    assert {:sigma_type_syntax, %{kind: :mismatched_closer, family: :sigma_type, expected: :rparen, observed: "]"}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SIGMA TYPE HAS THE WRONG CLOSER [E094] ------------------ sigma_mismatch.cure

             This Sigma type starts with '(', so ']' cannot close it. Use ')' after the
             dependent result type.

             at sigma_mismatch.cure:1:33
             1 | typealias P = Sigma(x: Int, Bool]
               |                    --       ----^ this Sigma type starts here; this is the Sigma binder; the dependent result type ends here; replace this with `)`

             Hint: Replace ']' with `)`
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")", span: replacement}]}] =
             diagnostic.suggestions

    assert {replacement.start_column, replacement.end_column} == {33, 34}
  end

  test "a valid Sigma type owns its name, delimiters, binder, domain, and result" do
    source = "mod M\n  typealias P = Sigma(x: Int, Bool)\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "sigma_meta.cure", emit_events: false)

    assert {:ok, {:container, _, [{:type_annotation, _, [{:sigma_type, meta, _}]}]}} =
             Parser.parse(tokens, emit_events: false)

    info = Keyword.fetch!(meta, :source_info)
    assert {info.whole.start_column, info.whole.end_column} == {17, 36}
    assert {info.name.start_column, info.name.end_column} == {17, 22}
    assert {info.opener.start_column, info.opener.end_column} == {22, 23}
    assert {info.closer.start_column, info.closer.end_column} == {35, 36}
    assert {info.fields["binder"].start_column, info.fields["binder"].end_column} == {23, 24}
    assert {info.annotation.start_column, info.annotation.end_column} == {26, 29}
    assert {info.body.start_column, info.body.end_column} == {31, 35}
    assert Enum.map(info.arguments, &{&1.start_column, &1.end_column}) == [{26, 29}, {31, 35}]
  end
end
