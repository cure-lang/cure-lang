defmodule Cure.Compiler.UnknownConstructorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer

  test "a non-typo pattern constructor lists constructors from the matched type" do
    source =
      "mod DiagnosticCtor\n  type Nat = Z | S(Nat)\n  fn bad(x: Nat) -> Nat = match x\n    Missing() -> Z\n    _ -> Z\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "constructor.cure", emit_events: false)

    assert {:source_context, {:unknown_pattern_constructor, :Missing}, context} = reason
    assert Enum.map(context.name_candidates, & &1.name) == ["Z", "S"]

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "constructor.cure", source)

    assert diagnostic.code == "E091"
    assert diagnostic.payload.candidates == []
    assert Enum.map(diagnostic.payload.available_candidates, & &1.name) == ["Z", "S"]
    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN CONSTRUCTOR [E091] --------------------------------- constructor.cure

             `Missing` is not available in this constructor namespace.

             The matched type provides `Z`, `S`.

             at constructor.cure:4:5
             4 |     Missing() -> Z
               |     ^^^^^^^ `Missing` was not found

             Hint: Use one of the matched type's constructors: `Z`, `S`
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 11}
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]
  end
end
