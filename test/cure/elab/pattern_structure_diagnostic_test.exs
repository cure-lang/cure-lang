defmodule Cure.Elab.PatternStructureDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a nonlinear pattern labels the first and repeated binder" do
    src = "mod M\n  type P = C(Int, Int)\n  fn f(p: P) -> Int = match p\n    C(x, x) -> x\nend\n"
    {diagnostic, registry} = diagnostic(src, "nonlinear.cure", :nonlinear_pattern)

    assert diagnostic.code == "E119"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {4, 10}
    assert [first] = diagnostic.secondary
    assert {first.span.start_line, first.span.start_column} == {4, 7}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN BINDS `X` MORE THAN ONCE [E119] ---------------------- nonlinear.cure

             Each name may bind only one field in a pattern. Repeating `x` would imply an
             equality check that the pattern has not proved.

             at nonlinear.cure:4:10
             4 |     C(x, x) -> x
               |       -  ^ `x` is first bound here; this repeats the earlier `x` binding

             Hint: Use a fresh name here, then compare the two values explicitly if they must be equal
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 9, 10)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(3, 6, 7)
  end

  test "a duplicate catch-all labels both catch-all patterns" do
    src =
      "mod M\n  type C = R | G\n  fn f(c: C) -> C = match c\n    R -> R\n    x -> x\n    y -> y\nend\n"

    {diagnostic, registry} = diagnostic(src, "duplicate_default.cure", :duplicate_default_pattern)

    assert diagnostic.code == "E119"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {6, 5}
    assert [first] = diagnostic.secondary
    assert {first.span.start_line, first.span.start_column} == {5, 5}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN MATCH HAS MORE THAN ONE CATCH-ALL [E119] ----- duplicate_default.cure

             A variable or `_` pattern matches every value not handled above it, so a later
             catch-all can never be reached.

             at duplicate_default.cure:6:5
             5 |     x -> x
               |     - this earlier pattern already matches every remaining value
             6 |     y -> y
               |     ^ this catch-all is unreachable

             Hint: Keep one final catch-all branch and remove or narrow the others
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(5, 4, 5)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(4, 4, 5)
  end

  test "an impossible catch-all points at the always-reachable pattern" do
    src =
      "mod M\n  type C = R | G\n  fn f(c: C) -> C = match c\n    x -> impossible\nend\n"

    {diagnostic, registry} =
      diagnostic(src, "impossible_default.cure", :impossible_default_pattern)

    assert diagnostic.code == "E119"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {4, 5}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CATCH-ALL BRANCH CANNOT BE IMPOSSIBLE [E119] -------- impossible_default.cure

             A variable or `_` pattern accepts every remaining value, so it cannot justify an
             `impossible` branch.

             at impossible_default.cure:4:5
             4 |     x -> impossible
               |     ^ this pattern is always reachable

             Hint: Use constructor patterns whose indices prove impossibility, or provide a result for this catch-all
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 4, 5)
    assert lsp["relatedInformation"] == []
  end

  test "an open map match points after its last branch" do
    src =
      "mod M\n  use Std.Map\n  fn f(m: Map(Atom, Int)) -> Int = match m\n    %{a: v} -> v\nend\n"

    {diagnostic, registry} = diagnostic(src, "map_default.cure", :map_match_needs_default)

    assert diagnostic.code == "E119"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {4, 17}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MAP MATCH NEEDS A CATCH-ALL [E119] ------------------------- map_default.cure

             Map patterns only constrain the entries written in their branches; maps with
             other key sets can still arrive.

             at map_default.cure:4:17
             4 |     %{a: v} -> v
               |                 ^ add a catch-all branch here

             Hint: Add `_ -> ...` to handle every remaining map value
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 16, 16)
  end

  test "an open binary match points after its last branch" do
    src =
      "mod M\n  use Std.Binary\n  fn f(b: Binary) -> Int = match b\n    <<a, _rest::binary>> -> a\nend\n"

    {diagnostic, registry} = diagnostic(src, "binary_default.cure", :binary_match_needs_default)

    assert diagnostic.code == "E119"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {4, 30}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BINARY MATCH NEEDS A CATCH-ALL [E119] ------------------- binary_default.cure

             Binary patterns only cover the byte and segment shapes written in their
             branches; other binary values can still arrive.

             at binary_default.cure:4:30
             4 |     <<a, _rest::binary>> -> a
               |                              ^ add a catch-all branch here

             Hint: Add `_ -> ...` to handle every remaining binary value
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 29, 29)
  end

  defp diagnostic(src, file, kind) do
    assert {:error, error} = Program.elaborate(src, file: file)
    semantic = Program.semantic_error(error)
    assert is_tuple(semantic) and elem(semantic, 0) == kind
    Cure.Compiler.Errors.to_diagnostic(error, file, src)
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
