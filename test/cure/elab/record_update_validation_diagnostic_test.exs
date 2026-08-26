defmodule Cure.Elab.RecordUpdateValidationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a construction rejects duplicate fields and labels both authored names" do
    source = point_module("  fn bad() -> Point = Point{x: 1, x: 2, y: 3}\n")
    {diagnostic, registry, error} = diagnostic(source, "dup_construct.cure")

    assert {:duplicate_field, %{name: :x, record: :Point, operation: :construction, spans: [_, _]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- DUPLICATE FIELD [E105] ----------------------------------- dup_construct.cure

             The field `x` is supplied more than once while constructing `Point`. A record
             value can provide each field only once.

             at dup_construct.cure:5:35
             5 |   fn bad() -> Point = Point{x: 1, x: 2, y: 3}
               |                             -     ^ this field was first supplied here; this field is supplied again

             Hint: Remove one `x` field
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 34, 35)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(4, 28, 29)
    assert related["message"] == "this field was first supplied here"

    assert Map.take(lsp["data"]["payload"], ["kind", "name", "operation", "record"]) == %{
             "kind" => "duplicate_field",
             "name" => "x",
             "operation" => "construction",
             "record" => "Point"
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "x: 1, x: 2, ", "x: 1, ")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "dup_construct_fixed.cure")
  end

  test "an update rejects duplicate overrides and labels both authored names" do
    source = point_module("  fn bad(p: Point) -> Point = Point{p | x: 1, x: 2}\n")
    {diagnostic, registry, error} = diagnostic(source, "dup_update.cure")

    assert {:duplicate_field, %{name: :x, record: :Point, operation: :update, spans: [_, _]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- DUPLICATE FIELD [E105] -------------------------------------- dup_update.cure

             The field `x` is supplied more than once while updating `Point`. A record value
             can provide each field only once.

             at dup_update.cure:5:47
             5 |   fn bad(p: Point) -> Point = Point{p | x: 1, x: 2}
               |                                         -     ^ this field was first supplied here; this field is supplied again

             Hint: Remove one `x` field
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 46, 47)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(4, 40, 41)
    assert lsp["data"]["payload"]["operation"] == "update"

    fixed = String.replace(source, ", x: 2", "")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "dup_update_fixed.cure")
  end

  test "an update base with the wrong type labels the base and target record" do
    source = point_module("  fn bad(p: Int) -> Point = Point{p | x: 1}\n")
    {diagnostic, registry, error} = diagnostic(source, "bad_base.cure")

    assert {:record_update_base_mismatch, %{record: :"M#Point", actual: :"Std.Int#Int"}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `POINT` UPDATE NEEDS A `POINT` VALUE [E093] ------------------- bad_base.cure

             The value before `|` has type `Int`, but a `Point` update must start from
             another `Point` value.

             at bad_base.cure:5:35
             5 |   fn bad(p: Int) -> Point = Point{p | x: 1}
               |                             ----- ^ this update constructs `Point`; this value has type `Int`

             Hint: Use a `Point` value before `|`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 34, 35)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(4, 28, 33)

    assert lsp["data"]["payload"] == %{
             "actual" => "Std.Int#Int",
             "actual_surface" => "Int",
             "checking" => "Point",
             "kind" => "record_update_base_mismatch",
             "record" => "M#Point",
             "record_surface" => "Point"
           }

    fixed = String.replace(source, "p: Int", "p: Point")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "bad_base_fixed.cure")
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
