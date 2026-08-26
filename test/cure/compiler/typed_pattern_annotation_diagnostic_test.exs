defmodule Cure.Compiler.TypedPatternAnnotationDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a constructor pattern annotation labels the binder, annotation, and constructor" do
    source = """
    mod TypedPattern
      type Box = Box(Int)
      fn bad(box: Box) -> Int = match box
        Box(value: Bool) -> 1
    end
    """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:typed_pattern_type_mismatch, {:variable, _, "Bool"}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `VALUE` IS ANNOTATED AS `BOOL`, BUT `BOX` STORES `INT` [E093] -- typed_pattern.cure

             Visible field 1 of `Box` has type `Int`. This pattern annotates `value` as
             `Bool`, so the annotation cannot describe the value selected by the constructor.

             at typed_pattern.cure:4:16
             4 |     Box(value: Bool) -> 1
               |     ---------------- `Box` provides this field as `Int`
               |         -----  ^^^^ `value` is the field being annotated; this says `Bool`, but the constructor field is `Int`

             Hint: Change the annotation to `Int`, or remove it and let `Box` determine the field type
             """)

    assert diagnostic.payload == %{
             kind: :typed_pattern_type_mismatch,
             constructor: "Box",
             binder: "value",
             argument_index: 0,
             annotated: "Bool",
             field_type: "Int",
             checking: :pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 15, 3, 19)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(3, 8, 3, 13),
             range(3, 4, 3, 20)
           ]

    assert lsp["data"]["suggestions"] == [
             %{
               "message" => "Change the annotation to `Int`, or remove it and let `Box` determine the field type",
               "applicability" => "manual",
               "edits" => []
             }
           ]
  end

  test "a mismatch on a later field retains its authored field position" do
    source = """
    mod TypedPair
      type Pair = Pair(Int, String)
      fn bad(pair: Pair) -> Int = match pair
        Pair(number: Int, text: Bool) -> number
    end
    """

    {diagnostic, registry, _error} = diagnostic(source)

    assert diagnostic.title == "`text` is annotated as `Bool`, but `Pair` stores `String`"

    assert diagnostic.payload == %{
             kind: :typed_pattern_type_mismatch,
             constructor: "Pair",
             binder: "text",
             argument_index: 1,
             annotated: "Bool",
             field_type: "String",
             checking: :pattern
           }

    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 28, 3, 32)
  end

  test "matching annotation and inferred constructor field both elaborate" do
    annotated = """
    mod TypedPattern
      type Box = Box(Int)
      fn good(box: Box) -> Int = match box
        Box(value: Int) -> value
    end
    """

    inferred = String.replace(annotated, "value: Int", "value")

    assert {:ok, _env} = Program.elaborate(annotated, file: "typed_pattern.cure")
    assert {:ok, _env} = Program.elaborate(inferred, file: "typed_pattern.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "typed_pattern.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "typed_pattern.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
