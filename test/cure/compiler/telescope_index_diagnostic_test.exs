defmodule Cure.Compiler.TelescopeIndexDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "element points at the authored index, receiver, and complete projection" do
    source = source("element(t3(), 9)")
    {diagnostic, registry, error} = diagnostic(source, "element_oob.cure")

    assert {:telescope_index_out_of_bounds, 9, 3} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE POSITION 9 IS OUT OF RANGE [E093] -------------------- element_oob.cure

             This tuple has 3 positions, numbered from 1 through 3, but this projection asks
             for position 9. Tuple projection is checked at compile time, so an out-of-range
             position can never produce a value.

             at element_oob.cure:3:35
             3 |   fn bad() -> Int = element(t3(), 9)
               |                     ---------------- this complete projection cannot succeed
               |                             ----  ^ this expression has a tuple type with 3 positions; index 9 is outside this 3-element tuple

             Hint: Use a tuple position from 1 through 3
             """)

    assert diagnostic.payload == %{
             kind: :telescope_index_out_of_bounds,
             index: 9,
             arity: 3,
             syntax: :element,
             checking: :bad
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 34, 2, 35)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(2, 28, 2, 32),
             range(2, 20, 2, 36)
           ]
  end

  test "dot projection points at the authored numeric field" do
    source = source("t3().9")
    {diagnostic, registry, error} = diagnostic(source, "dot_oob.cure")

    assert {:telescope_index_out_of_bounds, 9, 3} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE POSITION 9 IS OUT OF RANGE [E093] ------------------------ dot_oob.cure

             This tuple has 3 positions, numbered from 1 through 3, but this projection asks
             for position 9. Tuple projection is checked at compile time, so an out-of-range
             position can never produce a value.

             at dot_oob.cure:3:26
             3 |   fn bad() -> Int = t3().9
               |                     ---- ^ this expression has a tuple type with 3 positions; position .9 does not exist on this 3-element tuple
               |                     ------ this complete projection cannot succeed

             Hint: Use a tuple position from 1 through 3
             """)

    assert diagnostic.payload.syntax == :dot
    assert diagnostic.primary.span.start_column == 26
    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 25, 2, 26)
  end

  test "an out-of-range projection directly on a pair literal keeps the index and receiver spans" do
    source = """
    mod PairLiteralOob
      fn bad() -> Int = %[10, 20].3
    end
    """

    {diagnostic, registry, error} = diagnostic(source, "pair_literal_oob.cure")

    assert {:telescope_index_out_of_bounds, 3, 2} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE POSITION 3 IS OUT OF RANGE [E093] --------------- pair_literal_oob.cure

             This tuple has 2 positions, numbered from 1 through 2, but this projection asks
             for position 3. Tuple projection is checked at compile time, so an out-of-range
             position can never produce a value.

             at pair_literal_oob.cure:2:31
             2 |   fn bad() -> Int = %[10, 20].3
               |                     --------- ^ this expression has a tuple type with 2 positions; position .3 does not exist on this 2-element tuple
               |                     ----------- this complete projection cannot succeed

             Hint: Use a tuple position from 1 through 2
             """)

    assert diagnostic.payload == %{
             kind: :telescope_index_out_of_bounds,
             index: 3,
             arity: 2,
             syntax: :dot,
             checking: :bad
           }

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 30, 1, 31)
  end

  test "in-range element and dot projections still elaborate" do
    assert {:ok, _env} = Program.elaborate(source("element(t3(), 3)"), file: "element_ok.cure")
    assert {:ok, _env} = Program.elaborate(source("t3().3"), file: "dot_ok.cure")
  end

  defp source(projection) do
    """
    mod Oob
      fn t3() -> Tuple(Int, Int, Int) = %[10, 20, 30]
      fn bad() -> Int = #{projection}
    end
    """
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
