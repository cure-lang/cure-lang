defmodule Cure.Elab.RecordProjectionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "projecting from a non-record labels the receiver and requested field separately" do
    source = "mod M\n  fn f(x: Int) -> Int = x.foo\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "non_record.cure")

    assert {:projection_not_a_record, :"Std.Int#Int"} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CANNOT PROJECT `FOO` FROM `INT` [E093] ---------------------- non_record.cure

             This value has type `Int`, which is not a record and therefore has no field
             named `foo`.

             at non_record.cure:2:25
             2 |   fn f(x: Int) -> Int = x.foo
               |                         ^ --- this value has type `Int`, not a record; this projection asks for field `foo`

             Hint: Use a record value before `.foo`, or remove the projection
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 24, 25)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(1, 26, 29)
    assert related["message"] == "this projection asks for field `foo`"

    assert lsp["data"]["payload"] == %{
             "actual_type" => "Int",
             "actual_type_id" => "Std.Int#Int",
             "checking" => "f",
             "field" => "foo",
             "kind" => "projection_not_a_record"
           }

    fixed =
      "mod M\n  rec Box\n    foo: Int\n  fn f(x: Box) -> Int = x.foo\nend\n"

    assert {:ok, _environment} = Program.elaborate(fixed, file: "non_record_fixed.cure")
  end

  test "an unknown record field uses the actual shape for suggestions and labels" do
    source =
      "mod M\n  rec Point\n    x: Int\n    y: Int\n  fn f(p: Point) -> Int = p.z\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "unknown_field.cure")

    assert {:unknown_field, :"M#Point", "z", [:x, :y]} = Program.semantic_error(error)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- `POINT` HAS NO FIELD `Z` [E091] -------------------------- unknown_field.cure

             The record `Point` does not declare a field named `z`.

             at unknown_field.cure:5:29
             5 |   fn f(p: Point) -> Int = p.z
               |                           - ^ this value has record type `Point`; `Point` has no field named `z`

             Hint: Did you mean `x`, `y`?
             """)

    refute rendered =~ "M#Point"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 28, 29)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(4, 26, 27)
    assert related["message"] == "this value has record type `Point`"

    payload = lsp["data"]["payload"]
    assert payload["owner"] == "M#Point"
    assert payload["record"] == "M#Point"
    assert payload["candidates"] == ["x", "y"]

    assert Enum.map(payload["candidate_details"], &Map.take(&1, ["name", "origin", "owner"])) == [
             %{"name" => "x", "origin" => "record_shape", "owner" => "M#Point"},
             %{"name" => "y", "origin" => "record_shape", "owner" => "M#Point"}
           ]

    fixed = String.replace(source, "p.z", "p.x")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "unknown_field_fixed.cure")
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
