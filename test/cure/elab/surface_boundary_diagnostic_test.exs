defmodule Cure.Elab.SurfaceBoundaryDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "spawn reports the dependent-runtime boundary at the complete operation" do
    source = "mod M\n  fn bad() -> Int = spawn 1\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "spawn.cure")

    assert {:unsupported_async, %{primitive: :spawn, stage: :dependent_runtime}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `SPAWN` IS UNAVAILABLE IN DEPENDENT CODE [E107] ------------------ spawn.cure

             The dependent runtime cannot lower `spawn` while preserving Cure's checked
             process and message types. This is a runtime capability boundary, not a type
             error in the spawned expression.

             at spawn.cure:2:21
             2 |   fn bad() -> Int = spawn 1
               |                     ^^^^^^^ this asynchronous operation has no dependent-runtime lowering

             Hint: Use an actor, FSM, or supervisor declaration for managed concurrency
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 20, 27)
    refute inspect(diagnostic.payload) =~ "source_info"
  end

  test "a scalar splice outside quote points only at its authored splice" do
    source = "mod M\n  use Std.Syntax\n  fn bad(x: Syntax) -> Syntax = g($(x))\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "splice.cure")

    assert {:splice_outside_quote, %{form: :splice}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SPLICE HAS NO ENCLOSING QUOTE [E108] ---------------------------- splice.cure

             `$(expression)` inserts syntax into a surrounding `quote`, but this splice is in
             ordinary expression code. There is no quoted syntax tree here to receive its
             value.

             at splice.cure:3:35
             3 |   fn bad(x: Syntax) -> Syntax = g($(x))
               |                                   ^^^^ this splice is outside every `quote`

             Hint: Move this splice inside `quote ...`, or remove `$()` to evaluate an ordinary expression
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 34, 38)
    assert diagnostic.payload == %{form: :splice, stage: :elaboration}
  end

  test "a group splice outside quote includes its ellipsis and closer" do
    source =
      "mod M\n  use Std.Syntax\n  fn bad(xs: List(Syntax)) -> Syntax = g($(xs ...))\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "splice_group.cure")

    assert {:splice_outside_quote, %{form: :splice_group}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SPLICE HAS NO ENCLOSING QUOTE [E108] ---------------------- splice_group.cure

             `$(expressions ...)` inserts syntax into a surrounding `quote`, but this splice
             is in ordinary expression code. There is no quoted syntax tree here to receive
             its value.

             at splice_group.cure:3:42
             3 |   fn bad(xs: List(Syntax)) -> Syntax = g($(xs ...))
               |                                          ^^^^^^^^^ this splice is outside every `quote`

             Hint: Move this splice inside `quote ...`, or remove `$()` to evaluate an ordinary expression
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 41, 50)
    assert diagnostic.payload == %{form: :splice_group, stage: :elaboration}
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
