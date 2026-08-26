defmodule Cure.Elab.SuperinterfaceDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a missing superinterface points at the dependent implementation" do
    source =
      "mod M\n  interface Small(t)\n    fn small(a: t) -> Bool\n  interface Big(t) requires Small(t)\n    fn big(a: t) -> Bool\n\n  type Color = Red | Green | Blue\n  implementation Big for Color\n    fn big(a: Color) -> Bool = True()\nend\n"

    assert {:error, error} = Program.elaborate(source, file: "missing_super.cure")

    assert {:missing_superinterface,
            %{
              interface: :Big,
              superinterface: :Small,
              head: :"M#Color",
              for: "Color",
              span: %Cure.Diagnostic.Span{}
            }} = Program.semantic_error(error)

    {diagnostic, registry} = Errors.to_diagnostic(error, "missing_super.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REQUIRED IMPLEMENTATION IS MISSING [E105] ---------------- missing_super.cure

             `Big` requires `Small`, so implementing `Big` for `Color` also requires an
             implementation of `Small` for `Color`.

             at missing_super.cure:8:3
             8 |   implementation Big for Color
               |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this implementation also needs `Small` for `Color`

             Hint: Add `implementation Small for Color`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(7, 2, 30)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "head" => "Color",
             "head_id" => "M#Color",
             "interface" => "Big",
             "kind" => "missing_superinterface",
             "superinterface" => "Small"
           }

    fixed =
      String.replace(
        source,
        "  implementation Big for Color\n",
        "  implementation Small for Color\n    fn small(a: Color) -> Bool = True()\n  implementation Big for Color\n"
      )

    assert {:ok, _environment} = Program.elaborate(fixed, file: "missing_super_fixed.cure")
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
