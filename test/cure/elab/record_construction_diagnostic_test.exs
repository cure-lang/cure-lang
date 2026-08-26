defmodule Cure.Elab.RecordConstructionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an unknown record labels only its name and offers a unique typo repair" do
    source = "mod M\n  rec Point\n    x: Int\n  fn bad() = Ponit{x: 1}\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "unknown_record.cure")

    assert {:unknown_record, :Ponit} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CANNOT FIND RECORD `PONIT` [E021] ----------------------- unknown_record.cure

             No record named `Ponit` is available in this module or its imports.

             at unknown_record.cure:4:14
             4 |   fn bad() = Ponit{x: 1}
               |              ^^^^^ this record name is not in scope

             Hint: Did you mean `Point`?
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 13, 18)
    assert lsp["relatedInformation"] == []
    assert lsp["data"]["payload"]["candidates"] == ["Point"]

    assert [suggestion] = lsp["data"]["suggestions"]
    assert suggestion["applicability"] == "machine_applicable"
    assert [%{"newText" => "Point", "range" => edit_range}] = suggestion["edits"]
    assert edit_range == range(3, 13, 18)

    assert {:ok, _environment} =
             source
             |> String.replace("Ponit", "Point")
             |> Program.elaborate(file: "unknown_record_fixed.cure")
  end

  test "an unknown construction field labels the field and its record owner" do
    source = point_module("  fn bad() -> Point = Point{xx: 1, y: 2}\n")
    {diagnostic, registry, error} = diagnostic(source, "unknown_construct_field.cure")

    assert {:record_field_mismatch, %{record: :Point, unknown: [:xx], missing: [:x]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN RECORD FIELD [E022] -------------------- unknown_construct_field.cure

             `xx` is not a field of `Point`. Did you mean `x`?

             at unknown_construct_field.cure:5:29
             5 |   fn bad() -> Point = Point{xx: 1, y: 2}
               |                       ----- ^^ this constructs `Point`; this field is not declared by the record

             Hint: Replace it with `x`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 28, 30)
    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [range(4, 22, 27)]
    assert lsp["data"]["payload"]["operation"] == "record"

    fixed = String.replace(source, "xx:", "x:")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "unknown_construct_field_fixed.cure")
  end

  test "a missing construction field points at the closing brace without inventing a value edit" do
    source = point_module("  fn bad() -> Point = Point{x: 1}\n")
    {diagnostic, registry, error} = diagnostic(source, "missing_construct_field.cure")

    assert {:record_field_mismatch, %{record: :Point, unknown: [], missing: [:y]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MISSING RECORD FIELD [E022] -------------------- missing_construct_field.cure

             This `Point` value is missing `y`.

             at missing_construct_field.cure:5:33
             5 |   fn bad() -> Point = Point{x: 1}
               |                       -----     ^ this constructs `Point`; add the missing field `y` before this closing brace

             Hint: Add the missing field `y` before the closing `}`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 32, 33)
    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [range(4, 22, 27)]
    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "Point{x: 1}", "Point{x: 1, y: 2}")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "missing_construct_field_fixed.cure")
  end

  test "an unknown update field labels the record, base value, and offending field" do
    source = point_module("  fn bad(p: Point) -> Point = Point{p | z: 1}\n")
    {diagnostic, registry, error} = diagnostic(source, "unknown_update_field.cure")

    assert {:record_field_mismatch, %{record: :Point, unknown: [:z], missing: []}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN RECORD FIELD [E022] ----------------------- unknown_update_field.cure

             `z` is not a field of `Point`. Available fields are `x`, `y`.

             at unknown_update_field.cure:5:41
             5 |   fn bad(p: Point) -> Point = Point{p | z: 1}
               |                               ----- -   ^ this is a `Point` update; unchanged fields come from this value; this field is not declared by the record
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 40, 41)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(4, 30, 35),
             range(4, 36, 37)
           ]

    assert lsp["data"]["payload"]["operation"] == "record_update"
    assert lsp["data"]["suggestions"] == []

    fixed = String.replace(source, "z:", "x:")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "unknown_update_field_fixed.cure")
  end

  defp point_module(body) do
    "mod M\n  rec Point\n    x: Int\n    y: Int\n" <> body <> "end\n"
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
