defmodule Cure.Compiler.DependentRecordProjectionDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @preamble """
  mod DepRecord
    type Flag = On | Off
    fn Payload(f: Flag) -> Type = match f
      On() -> Int
      Off() -> String
    rec Box
      flag: Flag
      value: Payload(flag)
  """

  test "a dependent field projection labels the use, receiver, declaration, and prerequisite field" do
    source = @preamble <> "  fn bad(box: Box) = box.value\nend\n"
    {diagnostic, registry, error} = diagnostic(source)

    assert {:dependent_record_projection, :"DepRecord#Box", "value"} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `VALUE` CANNOT BE PROJECTED WITHOUT ITS DEPENDENCY [E093] --- dep_record.cure

             The type of `Box.value` depends on the earlier field `flag`. Projecting only
             `value` would discard the value needed to state its result type. Destructure the
             record so the dependent fields remain in scope together.

             at dep_record.cure:9:26
             7 |     flag: Flag
               |         ------ `flag` supplies part of `value`'s type
             8 |     value: Payload(flag)
               |          --------------- `value` is declared with a type that depends on the earlier field `flag`
             9 |   fn bad(box: Box) = box.value
               |                      --- ^^^^^ this value has dependent record type `Box`; this projection separates `value` from the earlier field `flag`

             Hint: Pattern-match `Box` and bind flag, value together
             """)

    assert diagnostic.payload == %{
             kind: :dependent_record_projection,
             record: "Box",
             field: "value",
             dependencies: ["flag"],
             checking: :bad
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(8, 25, 8, 30)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(8, 21, 8, 24),
             range(7, 9, 7, 24),
             range(6, 8, 6, 14)
           ]

    assert lsp["data"]["payload"]["dependencies"] == ["flag"]
  end

  test "destructuring keeps the prerequisite and dependent field in scope" do
    repaired =
      @preamble <>
        """
          fn good(box: Box) -> Flag = match box
            Box(flag, value) -> flag
        end
        """

    assert {:ok, _env} = Program.elaborate(repaired, file: "dep_record.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "dep_record.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "dep_record.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
