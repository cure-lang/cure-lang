defmodule Cure.Elab.SurfaceStructureDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a typed binary segment points at the segment rather than the enclosing function" do
    source = "mod M\n  use Std.Binary\n  fn f(b: Binary) -> Binary = <<b::float>>\nend\n"
    {diagnostic, registry} = diagnostic(source, "binary_segment.cure", :unsupported_binary_segment)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BINARY SEGMENT FORM IS NOT SUPPORTED [E093] ------------- binary_segment.cure

             Binary construction and matching currently support ordinary 8-bit byte
             expressions, plus a final variable `rest::binary` tail in patterns. This sized,
             typed, or otherwise structured segment cannot be lowered faithfully.

             at binary_segment.cure:3:33
             3 |   fn f(b: Binary) -> Binary = <<b::float>>
               |                                 ^^^^^^^^ this binary segment cannot be lowered

             Hint: Use plain byte segments, or move rich bit-syntax encoding and decoding behind an explicit binary helper
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 32, 40)
  end

  test "a nested map value pattern uses ordinary structural matching" do
    source =
      "mod M\n  use Std.Map\n  fn f(m: Map(Atom, List(Int))) -> Int = match m\n    %{a: [x]} -> x\n    _ -> 0\nend\n"

    assert {:ok, _env} = Program.elaborate(source, file: "map.cure")
  end

  test "a destructuring comprehension generator explains the one-variable restriction" do
    source = "mod M\n  fn f(xs: List(Int)) -> List(Int) = [x for [x] <- xs]\nend\n"
    {diagnostic, registry} = diagnostic(source, "comprehension.cure", :unsupported_comprehension_pattern)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LIST GENERATOR NEEDS A VARIABLE PATTERN [E093] ----------- comprehension.cure

             A list-comprehension generator can bind one variable in the dependent pipeline.
             This destructuring pattern cannot be translated without changing its matching
             behavior.

             at comprehension.cure:2:45
             2 |   fn f(xs: List(Int)) -> List(Int) = [x for [x] <- xs]
               |                                             ^^^ bind one variable in this generator

             Hint: Bind one name here, then destructure it with `match` inside the comprehension body
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 44, 47)
  end

  test "a non-let block assignment retains a source range assembled from its children" do
    source = "mod M\n  fn f() -> Int =\n    x = 1\n    x\nend\n"
    {diagnostic, registry} = diagnostic(source, "block.cure", :unsupported_block_statement)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BLOCK STATEMENT MUST BE A `LET` BINDING [E093] ------------------- block.cure

             Every non-final statement in an expression block must be a `let` binding. A
             plain assignment or expression before the final result has no sequencing meaning
             here.

             at block.cure:3:5
             3 |     x = 1
               |     ^^^^^ make this a `let` binding or the final expression

             Hint: Prefix this binding with `let`, or move the expression to the final line of the block
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 4, 9)
  end

  defp diagnostic(source, file, kind) do
    assert {:error, {:source_context, {^kind, _detail}, _context} = reason} =
             Program.elaborate(source, file: file)

    {diagnostic, registry} = Errors.to_diagnostic(reason, file, source)
    assert diagnostic.code == "E093"
    assert diagnostic.payload.kind == kind
    assert diagnostic.primary
    assert diagnostic.suggestions != []
    {diagnostic, registry}
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
