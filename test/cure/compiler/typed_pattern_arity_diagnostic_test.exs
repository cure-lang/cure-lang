defmodule Cure.Compiler.TypedPatternArityDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an extra typed constructor field labels that field and the constructor" do
    source = """
    mod TypedArity
      type Box = Box(Int)
      fn bad(box: Box) -> Int = match box
        Box(a: Int, b: Int) -> a
    end
    """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:typed_pattern_arity, 1} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `BOX` PATTERN HAS 2 FIELDS, BUT THE CONSTRUCTOR HAS 1 [E003] -- typed_arity.cure

             `b` is field 2 in this pattern, but `Box` exposes only 1 field to match. The
             pattern cannot bind a field that the constructor does not contain.

             at typed_arity.cure:4:17
             4 |     Box(a: Int, b: Int) -> a
               |     ---         ^^^^^^ `Box` accepts 1 visible field; this extra field has no matching position in `Box`

             Hint: Remove the extra field, or use a constructor with 2 visible fields
             """)

    assert diagnostic.payload == %{
             kind: :typed_pattern_arity,
             constructor: "Box",
             binder: "b",
             argument_index: 1,
             supplied_arity: 2,
             visible_arity: 1,
             checking: :pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 16, 3, 22)

    assert [%{"message" => "`Box` accepts 1 visible field", "location" => location}] =
             lsp["relatedInformation"]

    assert location["range"] == range(3, 4, 3, 7)
  end

  test "the first field of a nullary constructor is identified as extra" do
    source = """
    mod TypedEmpty
      type Empty = None
      fn bad(empty: Empty) -> Int = match empty
        None(value: Int) -> value
    end
    """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:typed_pattern_arity, 0} = Program.semantic_error(error)
    assert diagnostic.title == "`None` pattern has 1 field, but the constructor has 0"
    assert diagnostic.payload.argument_index == 0
    assert diagnostic.payload.visible_arity == 0
    assert Renderer.lsp(diagnostic, registry)["range"] == range(3, 9, 3, 19)
  end

  test "a pattern with exactly the visible fields still elaborates" do
    source = """
    mod TypedArity
      type Box = Box(Int)
      fn good(box: Box) -> Int = match box
        Box(value: Int) -> value
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "typed_arity.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "typed_arity.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "typed_arity.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
