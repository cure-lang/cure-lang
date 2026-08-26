defmodule Cure.Compiler.SelectiveImportDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(
        errors,
        &match?({:container_elements_syntax, %{container: :selective_import}}, &1)
      )

    assert {:container_elements_syntax, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "consecutive imported names get a comma insertion at the second name" do
    source = "use Std.List.{map filter}"
    {error, {diagnostic, registry}} = diagnostic(source, "import_comma.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_separator_missing,
              container: :selective_import,
              module: "Std.List",
              observed: "filter"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPORTED NAMES NEED A COMMA [E094] ------------------------ import_comma.cure

             The import from `Std.List` has another name here, but imported names must be
             separated by a comma.

             at import_comma.cure:1:19
             1 | use Std.List.{map filter}
               |              ---- ^ the selective import list starts here; the previous imported name ends here; insert a comma before this imported name

             Hint: Insert `,` between these imported names
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 19}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 18},
             "end" => %{"line" => 0, "character" => 18}
           }
  end

  test "an alias after an unclosed selective import gets a closing brace insertion" do
    source = "use Std.List.{map as L"
    {error, {diagnostic, registry}} = diagnostic(source, "import_close.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :selective_import,
              module: "Std.List",
              expected: :rbrace,
              observed: :as
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SELECTIVE IMPORT IS NOT CLOSED [E094] --------------------- import_close.cure

             The selective import from `Std.List` reaches the end of its names without the
             closing '}'.

             at import_close.cure:1:19
             1 | use Std.List.{map as L
               |              ---- ^ the selective import list starts here; the previous imported name ends here; close these imported names with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 19}
    assert insertion.start_byte == insertion.end_byte
  end

  test "valid selective imports and aliases still parse" do
    for source <- ["use Std.List.{map, filter}", "use Std.List.{map} as L"] do
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end
  end

  test "selective imports may span indented lines" do
    source = """
    use Std.Otp.{
      Pid,
      RawPid,
      MonitorRef
    }
    """

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:import, meta, []}} = Parser.parse(tokens, emit_events: false)
    assert Keyword.fetch!(meta, :items) == ["Pid", "RawPid", "MonitorRef"]
  end

  test "multiline selective imports allow a trailing comma" do
    source = """
    use Std.Otp.{
      Pid,
      RawPid,
    }
    """

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:import, meta, []}} = Parser.parse(tokens, emit_events: false)
    assert Keyword.fetch!(meta, :items) == ["Pid", "RawPid"]
  end
end
