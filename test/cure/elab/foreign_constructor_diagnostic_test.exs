defmodule Cure.Elab.ForeignConstructorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a constructor from another family labels the pattern and expected type" do
    source =
      "mod WrongFamily\n  type Left = L\n  type Right = R\n  fn bad(value: Left) -> Left = match value\n    R() -> L\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "wrong_family.cure")

    assert {:foreign_ctor, :"WrongFamily#R"} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `R` DOES NOT BELONG TO `LEFT` [E091] ---------------------- wrong_family.cure

             `R` is a constructor of `Right`, but this match scrutinizes `Left`. Every
             constructor pattern must come from the scrutinee's type.

             at wrong_family.cure:5:5
             4 |   fn bad(value: Left) -> Left = match value
               |                          ---- this match expects constructors from `Left`
             5 |     R() -> L
               |     ^^^ this constructor belongs to `Right`, not `Left`

             Hint: Replace `R` with `L`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 4, 7)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(3, 25, 29)
    assert related["message"] == "this match expects constructors from `Left`"

    assert lsp["data"]["payload"] == %{
             "actual_family" => "Right",
             "actual_family_id" => "WrongFamily#Right",
             "constructor" => "R",
             "constructor_id" => "WrongFamily#R",
             "expected_constructor_ids" => ["WrongFamily#L"],
             "expected_constructors" => ["L"],
             "expected_family" => "Left",
             "expected_family_id" => "WrongFamily#Left",
             "kind" => "foreign_ctor"
           }

    assert [suggestion] = lsp["data"]["suggestions"]
    assert suggestion["applicability"] == "machine_applicable"
    assert [%{"newText" => "L()", "range" => edit_range}] = suggestion["edits"]
    assert edit_range == range(4, 4, 7)

    fixed = String.replace(source, "R() ->", "L() ->")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "wrong_family_fixed.cure")
  end

  test "multiple valid constructors produce choices but no speculative edit" do
    source =
      "mod WrongFamily\n  type Left = L1 | L2\n  type Right = R\n  fn bad(value: Left) -> Left = match value\n    R() -> L1\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "wrong_family_many.cure")
    assert {:foreign_ctor, :"WrongFamily#R"} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `R` DOES NOT BELONG TO `LEFT` [E091] ----------------- wrong_family_many.cure

             `R` is a constructor of `Right`, but this match scrutinizes `Left`. Every
             constructor pattern must come from the scrutinee's type.

             at wrong_family_many.cure:5:5
             4 |   fn bad(value: Left) -> Left = match value
               |                          ---- this match expects constructors from `Left`
             5 |     R() -> L1
               |     ^^^ this constructor belongs to `Right`, not `Left`

             Hint: Use one of `L1`, `L2`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["data"]["payload"]["expected_constructors"] == ["L1", "L2"]
    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "    R() -> L1", "    L1() -> L1\n    L2() -> L1")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "wrong_family_many_fixed.cure")
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
