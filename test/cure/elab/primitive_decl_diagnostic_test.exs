defmodule Cure.Elab.PrimitiveDeclDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a missing marker points at the primitive name and explains the supported markers" do
    source = "mod M\n  primitive Widget\nend\n"
    {diagnostic, registry} = diagnostic(source, "missing.cure")

    assert diagnostic.code == "E120"
    assert diagnostic.payload.kind == :missing_builtin
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {2, 13}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PRIMITIVE DECLARATION NEEDS A BUILTIN TAG [E120] --------------- missing.cure

             `Widget` is declared as a primitive, but it has no `@builtin(...)` marker. The
             marker tells the compiler which runtime primitive representation this name
             denotes.

             at missing.cure:2:13
             2 |   primitive Widget
               |             ^^^^^^ add a `@builtin(...)` marker for this primitive

             Hint: Add one of `@builtin(:float)`, `@builtin(:binary)`, or `@builtin(:atom)` before this declaration
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 12, 18)
  end

  test "an unknown marker points at its exact spelling and relates the primitive name" do
    source = "mod M\n  @builtin(:sparkle) primitive Sparkle\nend\n"
    {diagnostic, registry} = diagnostic(source, "unknown.cure")

    assert diagnostic.code == "E120"

    assert diagnostic.payload == %{
             kind: :unknown_builtin,
             name: "Sparkle",
             tag: :sparkle,
             declared: nil,
             expected: nil,
             shape: nil
           }

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `:SPARKLE` IS NOT A PRIMITIVE BUILTIN [E120] ------------------- unknown.cure

             The compiler has no primitive representation named `:sparkle`. Primitive
             declarations may currently use only `:float`, `:binary`, or `:atom`.

             at unknown.cure:2:12
             2 |   @builtin(:sparkle) primitive Sparkle
               |            ^^^^^^^^            ------- this builtin tag is not recognized; this is the primitive declaration being validated

             Hint: Use `:float`, `:binary`, or `:atom`, or declare an ordinary Cure type instead
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 11, 19)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(1, 31, 38)
  end

  test "a seeded-floor mismatch offers and validates the unique tag replacement" do
    source = "mod M\n  @builtin(:float) primitive Binary\nend\n"
    {diagnostic, registry} = diagnostic(source, "mismatch.cure")

    assert diagnostic.code == "E120"
    assert diagnostic.payload.kind == :floor_mismatch
    assert diagnostic.payload.declared == :float
    assert diagnostic.payload.expected == :binary

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `BINARY` HAS THE WRONG PRIMITIVE BUILTIN [E120] --------------- mismatch.cure

             `Binary` is part of the compiler's primitive floor and denotes `:binary`, but
             this declaration marks it as `:float`. Those representations are not
             interchangeable.

             at mismatch.cure:2:12
             2 |   @builtin(:float) primitive Binary
               |            ^^^^^^            ------ replace this tag with `:binary`; this is the primitive declaration being validated

             Hint: Change the marker to `@builtin(:binary)`
             """)

    assert [%{applicability: :machine_applicable, edits: [edit]}] = diagnostic.suggestions
    assert edit.replacement == ":binary"
    fixed = replace_span(source, edit.span, edit.replacement)
    assert fixed == "mod M\n  @builtin(:binary) primitive Binary\nend\n"
    assert {:ok, _env} = Program.elaborate(fixed, file: "fixed.cure")

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 11, 17)
    assert [suggestion] = lsp["data"]["suggestions"]
    assert suggestion["applicability"] == "machine_applicable"
    assert [lsp_edit] = suggestion["edits"]
    assert lsp_edit["range"] == range(1, 11, 17)
    assert lsp_edit["newText"] == ":binary"
  end

  defp diagnostic(source, file) do
    assert {:error, {:source_context, reason, context} = wrapped} =
             Program.elaborate(source, file: file)

    assert context.expectation_origin == :primitive_declaration
    assert elem(reason, 0) in [:primitive_missing_builtin, :unknown_primitive_tag, :primitive_floor_mismatch]
    Errors.to_diagnostic(wrapped, file, source)
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end

  defp replace_span(source, span, replacement) do
    prefix = binary_part(source, 0, span.start_byte)
    suffix = binary_part(source, span.end_byte, byte_size(source) - span.end_byte)
    prefix <> replacement <> suffix
  end
end
