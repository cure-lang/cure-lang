# F2 (audit iteration 4): the @edition pragma errors and the compile-boundary
# {:edition_error, {:unknown_edition, _}} previously hit the catch-all formatter,
# which rendered a raw `inspect` tuple ("compilation error … {:edition_pragma_
# unknown, 1, 1}"). A "must fail loudly" error (spec §3.1) has to be legible: it
# names what is wrong and, for an unknown edition, lists the known ones.
defmodule Cure.Compiler.EditionErrorFormatTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Errors, Lexer, Parser}

  defp diagnostic(source) do
    {:ok, tokens} = Lexer.tokenize(source, file: "edition.cure", emit_events: false)
    {:error, errors} = Parser.parse(tokens, file: "edition.cure", emit_events: false)
    Errors.to_diagnostic({:parse_error, errors}, "edition.cure", source)
  end

  test "placement error explains the pragma must lead the file" do
    msg = Errors.format_error({:edition_pragma_placement, 4, 1}, "t.cure")
    assert msg =~ "edition"
    assert msg =~ ~r/first|before any/i
    refute msg =~ "compilation error"
  end

  test "malformed error names the required 4-digit single-line form" do
    msg = Errors.format_error({:edition_pragma_malformed, 1, 1}, "t.cure")
    assert msg =~ "4-digit"
    assert msg =~ "@edition(\"2026\")"
    refute msg =~ "compilation error"
  end

  test "unknown-pragma error lists the known editions" do
    msg = Errors.format_error({:edition_pragma_unknown, 1, 1}, "t.cure")
    assert msg =~ ~r/unknown edition/i
    assert msg =~ Cure.Edition.current()
    refute msg =~ "compilation error"
  end

  test "compile-boundary unknown-edition error names the value and the known set" do
    msg = Errors.format_error({:edition_error, {:unknown_edition, "9999"}}, "t.cure")
    assert msg =~ "9999"
    assert msg =~ ~r/unknown edition/i
    assert msg =~ Cure.Edition.current()
    refute msg =~ "compilation error"
  end

  test "real parser edition failures underline their owned source ranges" do
    cases = [
      {"mod M\n@edition(\"2026\")\n", :edition_pragma_placement, 2, 1, 17,
       "the edition cannot change after parsing has started"},
      {"@edition(2026)\nmod M\n", :edition_pragma_malformed, 1, 10, 14, "this is not a valid edition argument"},
      {"@edition(\"9999\")\nmod M\n", :edition_pragma_unknown, 1, 10, 16, "this edition is not available"}
    ]

    for {source, key, line, start_column, end_column, label} <- cases do
      {diagnostic, registry} = diagnostic(source)
      rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E094"
      assert diagnostic.key == key
      assert diagnostic.primary.span.start_line == line
      assert diagnostic.primary.span.start_column == start_column
      assert diagnostic.primary.span.end_column == end_column
      assert diagnostic.primary.message == label
      assert rendered =~ "#{line} | "
      assert rendered =~ label
      refute rendered =~ "{:edition_pragma"
    end
  end

  test "a unique supported edition produces an exact machine edit and LSP range" do
    source = "@edition(\"9999\")\nmod M\n"
    {diagnostic, registry} = diagnostic(source)

    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
             """
             -- UNKNOWN EDITION [E094] ----------------------------------------- edition.cure

             `9999` is not a supported Cure edition. This compiler supports `2026`.

             at edition.cure:1:10
             1 | @edition("9999")
               |          ^^^^^^ this edition is not available

             Hint: Use the supported edition `2026`
             """
             |> String.trim_trailing()

    assert [%Cure.Diagnostic.Suggestion{applicability: :machine_applicable, edits: [edit]}] =
             diagnostic.suggestions

    assert edit.replacement == "\"2026\""
    assert edit.span.start_column == 10
    assert edit.span.end_column == 16

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 0, "character" => 9},
             "end" => %{"line" => 0, "character" => 15}
           }

    assert [suggestion] = lsp["data"]["suggestions"]
    assert suggestion["applicability"] == "machine_applicable"
    assert [lsp_edit] = suggestion["edits"]
    assert lsp_edit["newText"] == "\"2026\""
    assert lsp_edit["range"] == lsp["range"]
  end

  test "a multiline pragma highlights the complete malformed construct without an unsafe edit" do
    source = "@edition(\n\"2026\")\nmod M\n"
    {diagnostic, registry} = diagnostic(source)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.primary.span.start_line == 1
    assert diagnostic.primary.span.start_column == 1
    assert diagnostic.primary.span.end_line == 2
    assert diagnostic.primary.span.end_column == 8
    assert Enum.all?(diagnostic.suggestions, &(&1.applicability == :manual and &1.edits == []))
    assert rendered =~ "1 | @edition("
    assert rendered =~ "2 | \"2026\")"
  end
end
