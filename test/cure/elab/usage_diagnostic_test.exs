defmodule Cure.Elab.UsageDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a dropped linear parameter points to its authored binding" do
    src = "mod M\n  fn f(@linear c : Int) -> Int = 0\nend\n"
    {diagnostic, registry} = diagnostic(src, "unused.cure", :linear, :erased)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LINEAR VALUE IS NOT USED [E117] --------------------------------- unused.cure

             `c` is linear, so every path through this function must use it exactly once.
             This function does not use it.

             at unused.cure:2:16
             2 |   fn f(@linear c : Int) -> Int = 0
               |                ^ this linear parameter must be used exactly once

             Hint: Use `c` once on every path, or declare it `@affine` if it may be dropped
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 15, 16)
  end

  test "passing a linear parameter to an unrestricted callee points to that use" do
    src =
      "mod M\n  fn use2(x: Int) -> Int = x\n  fn f(@linear c : Int) -> Int = use2(c)\nend\n"

    {diagnostic, registry} = diagnostic(src, "scaled.cure", :linear, :unrestricted)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LINEAR VALUE MAY BE USED MORE THAN ONCE [E117] ------------------ scaled.cure

             `c` is linear, but this use passes it to a context that may consume it any
             number of times.

             at scaled.cure:3:39
             3 |   fn f(@linear c : Int) -> Int = use2(c)
               |                -                      ^ this parameter is declared `linear` here; this use does not preserve linear ownership

             Hint: Pass `c` only to linear parameters, and consume it exactly once on every path
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 38, 39)
    assert [related] = lsp["relatedInformation"]
    assert related["message"] == "this parameter is declared `linear` here"
    assert related["location"]["range"] == range(2, 15, 16)
  end

  test "duplicating an affine parameter labels both authored uses" do
    src = "mod M\n  fn f(@affine h : Int) -> Int = h + h\nend\n"
    {diagnostic, registry} = diagnostic(src, "duplicate.cure", :affine, :unrestricted)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- AFFINE VALUE MAY BE USED MORE THAN ONCE [E117] --------------- duplicate.cure

             `h` is affine, but this path can use it more than once. An affine value may be
             used once or not at all.

             at duplicate.cure:2:38
             2 |   fn f(@affine h : Int) -> Int = h + h
               |                -                 -   ^ this parameter is declared `affine` here; another use on this path is here; this use does not preserve affine ownership

             Hint: Pass `h` only to affine or linear parameters, and use it at most once
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 37, 38)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(1, 15, 16),
             range(1, 33, 34)
           ]
  end

  defp diagnostic(src, file, declared, used) do
    assert {:error, error} = Program.elaborate(src, file: file)

    assert {:usage_violation, %{declared: ^declared, used: ^used}} =
             Program.semantic_error(error)

    Cure.Compiler.Errors.to_diagnostic(error, file, src)
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
