defmodule Cure.Elab.DerivingDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a parameter constraint refusal labels the exact derived interface and type name" do
    source =
      "mod DvTwo\n  interface Equatable(a)\n    fn eq(x: a, y: a) -> Bool\n  type Lst(a) = Nil | Cons(a, Lst(a)) deriving Equatable\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "derive_constraints.cure")

    assert {:deriving_needs_constraints, :Equatable, :Lst} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CANNOT DERIVE `EQUATABLE` FOR `LST` [E105] ---------- derive_constraints.cure

             A field of `Lst` uses one of the type's parameters directly. Deriving
             `Equatable` would need an interface dictionary for that parameter, which
             automatic derivation cannot thread yet.

             at derive_constraints.cure:4:48
             4 |   type Lst(a) = Nil | Cons(a, Lst(a)) deriving Equatable
               |        ---                                     ^^^^^^^^^ this declares `Lst`; this derived interface needs a constraint on the type parameter

             Hint: Implement `Equatable` for `Lst` manually, or remove the parameter-typed field
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 47, 56)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(3, 7, 10)
    assert related["message"] == "this declares `Lst`"

    assert lsp["data"]["payload"] == %{
             "interface" => "Equatable",
             "kind" => "deriving_needs_constraints",
             "type" => "Lst"
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, " deriving Equatable", "")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "derive_constraints_fixed.cure")
  end

  test "each interface in a deriving list owns its token span" do
    source =
      "mod DeriveSpans\n  type Color = Red | Green deriving Equatable, Missing\nend\n"

    assert {:ok, tokens} =
             Cure.Compiler.Lexer.tokenize(source, file: "derive_spans.cure", emit_events: false)

    assert {:ok, ast} =
             Cure.Compiler.Parser.parse(tokens,
               file: "derive_spans.cure",
               emit_events: false,
               prelude_macros: false
             )

    {:block, _block_meta, [{:container, _module_meta, [{:container, meta, _variants}]} | _]} = ast
    info = Cure.MetaAST.Metadata.source_info(meta)

    assert info.fields[{:deriving_interface, "Equatable"}].start_column == 37
    assert info.fields[{:deriving_interface, "Equatable"}].end_column == 46
    assert info.fields[{:deriving_interface, "Missing"}].start_column == 48
    assert info.fields[{:deriving_interface, "Missing"}].end_column == 55
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
