defmodule Cure.Elab.TotalityWiringTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @types """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  """

  @gadt """
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  test "a total type-level function is certified; the whole program elaborates" do
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = x\n" <> @gadt
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a non-total function used in a type is rejected (totality required)" do
    # andd is self-recursive (non-total) yet appears in SF's computed index,
    # so it is type-level and MUST be total — §6 negative #3.
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)\n" <> @gadt
    assert {:error, error} = Program.elaborate(src, file: "totality.cure")
    assert {:totality_required, :"Main#andd"} = Program.semantic_error(error)

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "totality.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.code == "E013"
    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.span.start_column == 34

    assert %{
             reason: :not_decreasing,
             members: [:"Main#andd"],
             offending_edge: %{
               source: :"Main#andd",
               target: :"Main#andd",
               diagonal: [:equal, :equal],
               source_call_path: [{:"Main#andd", :"Main#andd"}]
             }
           } = diagnostic.payload.reason

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION MUST BE TOTAL [E013] --------------------------------- totality.cure

             `Main#andd` is evaluated while checking types, but the compiler cannot prove
             that every call to it terminates.

             at totality.cure:4:34
             4 | fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)
               | ------------------------------------------- this type-level function must terminate on every input
               |                                  ^^^^ this recursive call participates in an unproven termination cycle

             Note: Runtime-only functions may remain partial; only compile-time computation
                   requires a total definition.

             Note: Totality SCC: Main#andd

             Note: Offending idempotent loop: Main#andd -> Main#andd; diagonal [:equal,
                   :equal]

             Note: Source-call path: Main#andd -> Main#andd

             Hint: Make each recursive call use a structurally smaller argument, or keep this function out of types
             """)

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 33},
             "end" => %{"line" => 3, "character" => 37}
           }

    assert [definition] = lsp["relatedInformation"]
    assert definition["message"] == "this type-level function must terminate on every input"

    assert definition["location"]["range"] == %{
             "start" => %{"line" => 3, "character" => 0},
             "end" => %{"line" => 3, "character" => 43}
           }
  end

  test "a non-total function used only at runtime is NOT required to be total" do
    # loop is self-recursive but referenced in no type ⇒ stays partial, allowed.
    src =
      @types <>
        "fn andd(x: Dec, y: Dec) -> Dec = x\n" <>
        @gadt <>
        "fn loop(x: Dec) -> Dec = loop(x)\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "every authored self-call in an unproven termination cycle is labeled" do
    src =
      @types <>
        """
        fn andd(x: Dec, y: Dec) -> Dec = match x
          Dcoupled() -> andd(x, y)
          Causal() -> andd(x, y)
        """ <>
        @gadt

    assert {:error, error} = Program.elaborate(src, file: "totality_calls.cure")
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "totality_calls.cure", src)

    assert diagnostic.primary.span.start_line == 5
    assert diagnostic.primary.span.start_column == 17
    assert diagnostic.primary.span.end_column == 21

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.span.start_column, &1.message}) == [
             {6, 15, "another recursive call in this cycle is here"},
             {4, 1, "this type-level function must terminate on every input"}
           ]

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 4, "character" => 16},
             "end" => %{"line" => 4, "character" => 20}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["message"]) == [
             "another recursive call in this cycle is here",
             "this type-level function must terminate on every input"
           ]
  end
end
