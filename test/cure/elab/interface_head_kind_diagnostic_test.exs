defmodule Cure.Elab.InterfaceHeadKindDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "inconsistent interface-head uses label the bare and applied type occurrences" do
    source =
      "mod M\n  interface Bad(a)\n    fn m1(x: a) -> Bool\n    fn m2(y: a(a)) -> Bool\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "head_kind.cure")

    assert {:inconsistent_head_kind, :Bad} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `BAD` USES `A` AT TWO DIFFERENT KINDS [E105] ----------------- head_kind.cure

             The interface head `a` is used both as a complete type and as a type constructor
             such as `a(a)`. One interface parameter must have one consistent kind in every
             method signature.

             at head_kind.cure:4:14
             3 |     fn m1(x: a) -> Bool
               |              - `a` is used as a complete type here
             4 |     fn m2(y: a(a)) -> Bool
               |              ^^^^ `a` is used as a type constructor here

             Hint: Use `a` consistently as either a type or a type constructor
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 13, 17)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(2, 13, 14)
    assert related["message"] == "`a` is used as a complete type here"

    assert lsp["data"]["payload"] == %{
             "head_parameter" => "a",
             "interface" => "Bad",
             "kind" => "inconsistent_head_kind",
             "uses" => [
               %{"kind" => "bare", "method" => "m1"},
               %{"kind" => "applied", "method" => "m2"}
             ]
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "a(a)", "a")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "head_kind_fixed.cure")
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
