defmodule Cure.Elab.PatternCoverageDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a missing constructor points to the branch insertion position" do
    src = "mod M\n  type N = Z | S(N)\n  fn f(x: N) -> N = match x\n    Z() -> Z()\nend\n"
    {diagnostic, registry} = diagnostic(src, "missing.cure", :missing_branch)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN MATCH IS MISSING `S` [E118] ---------------------------- missing.cure

             This match can receive `S`, but no branch handles that constructor.

             at missing.cure:4:15
             4 |     Z() -> Z()
               |               ^ add a `S` branch here

             Hint: Add a `S(...) -> ...` branch, or a catch-all branch
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 14, 14)
  end

  test "a duplicate constructor labels both pattern regions" do
    src =
      "mod M\n  type N = Z | S(N)\n  fn f(x: N) -> N = match x\n    Z() -> Z()\n    Z() -> Z()\n    S(n) -> S(n)\nend\n"

    {diagnostic, registry} = diagnostic(src, "duplicate.cure", :duplicate_branch)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `Z` HAS MORE THAN ONE BRANCH [E118] -------------------------- duplicate.cure

             Only one branch may handle each constructor. The later `Z` branch can never be
             selected independently.

             at duplicate.cure:5:5
             4 |     Z() -> Z()
               |     --- `Z` is first handled here
             5 |     Z() -> Z()
               |     ^^^ this repeats the earlier `Z` branch

             Hint: Combine these `Z` cases or remove the duplicate branch
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 4, 7)
    assert [related] = lsp["relatedInformation"]
    assert related["message"] == "`Z` is first handled here"
    assert related["location"]["range"] == range(3, 4, 7)
  end

  test "a reachable impossible branch points to its constructor pattern" do
    src =
      "mod M\n  type N = Z | S(N)\n  fn f(x: N) -> N = match x\n    Z() -> impossible\n    S(n) -> S(n)\nend\n"

    {diagnostic, registry} = diagnostic(src, "impossible.cure", :reachable_impossible)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `Z` IS REACHABLE HERE [E118] -------------------------------- impossible.cure

             This branch is marked `impossible`, but `Z` can occur for the matched type and
             indices.

             at impossible.cure:4:5
             4 |     Z() -> impossible
               |     ^^^ this constructor is reachable

             Hint: Replace `impossible` with a result for the `Z` case
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 4, 7)
  end

  defp diagnostic(src, file, kind) do
    assert {:error, error} = Program.elaborate(src, file: file)
    assert {^kind, _branch} = Program.semantic_error(error)
    Cure.Compiler.Errors.to_diagnostic(error, file, src)
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
