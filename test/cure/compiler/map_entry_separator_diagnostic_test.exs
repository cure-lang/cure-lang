defmodule Cure.Compiler.MapEntrySeparatorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :map_entry_separator_missing}}, &1))
    assert {:declaration_separator_missing, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "an explicit map entry gets the unique fat-arrow insertion" do
    source = ~s(%{"x" 1})
    {error, {diagnostic, registry}} = diagnostic(source, "map_arrow.cure")

    assert {:declaration_separator_missing, %{kind: :map_entry_separator_missing, container: :map, ambiguous: false}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MAP ENTRY NEEDS AN ARROW [E094] ------------------------------ map_arrow.cure

             This explicit map entry needs `=>` between its key and value.

             A valid continuation here starts with '=>'.

             at map_arrow.cure:1:7
             1 | %{"x" 1}
               | ----- ^ this map starts here; this map entry starts here; insert `=>` before this map value

             Hint: Insert `=>` before the map value
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "=> ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 7}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "=> ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 6},
             "end" => %{"line" => 0, "character" => 6}
           }
  end

  test "an ambiguous map separator explains both repairs without choosing one" do
    source = "%{foo bar}"
    {error, {diagnostic, registry}} = diagnostic(source, "map_ambiguous.cure")

    assert {:declaration_separator_missing,
            %{kind: :map_entry_separator_missing, container: :map, ambiguous: true, key: "foo"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MAP ENTRIES NEED A SEPARATOR [E094] ---------------------- map_ambiguous.cure

             After `foo`, this could be another punned map entry needing `,`, or the value of
             `foo` needing `=>`.

             at map_ambiguous.cure:1:7
             1 | %{foo bar}
               | ----- ^ this map starts here; this map entry starts here; separate these entries with `,`, or make this the value with `=>`

             Hint: Choose `,` for two punned entries or `=>` for a key-value entry
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "the ambiguous producer retains record ownership" do
    source = "Point{foo bar}"
    {error, {diagnostic, registry}} = diagnostic(source, "record_ambiguous.cure")

    assert {:declaration_separator_missing,
            %{kind: :map_entry_separator_missing, container: :record, ambiguous: true, key: "foo"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- RECORD FIELDS NEED A SEPARATOR [E094] ----------------- record_ambiguous.cure

             After `foo`, this could be another punned record entry needing `,`, or the value
             of `foo` needing `=>`.

             at record_ambiguous.cure:1:11
             1 | Point{foo bar}
               |      ---- ^ this record starts here; this record entry starts here; separate these entries with `,`, or make this the value with `=>`

             Hint: Choose `,` for two punned entries or `=>` for a key-value entry
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "an explicit record entry gets a record-specific machine edit" do
    {error, {diagnostic, _registry}} = diagnostic(~s(Point{"x" 1}), "record_arrow.cure")

    assert {:declaration_separator_missing, %{kind: :map_entry_separator_missing, container: :record, ambiguous: false}} =
             error

    assert diagnostic.title == "Record entry needs an arrow"

    assert [%{message: "Insert `=>` before the record value", edits: [%{replacement: "=> "}]}] =
             diagnostic.suggestions
  end

  test "both valid interpretations remain accepted" do
    for source <- [~s(%{"x" => 1}), "%{foo, bar}", ~s(Point{"x" => 1}), "Point{foo, bar}"] do
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end
  end
end
