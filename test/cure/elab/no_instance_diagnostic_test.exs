defmodule Cure.Elab.NoInstanceDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a concrete missing implementation names the surface type and labels the call" do
    source =
      "mod C3\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n  type Foo = MkFoo\n  fn test(x: Foo, y: Foo) -> Bool = eqs(x, y)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "missing_eqs.cure")

    assert {:no_instance, :Eqs, :"C3#Foo"} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NO `EQS` IMPLEMENTATION FOUND [E093] ----------------------- missing_eqs.cure

             No implementation of `Eqs` is available for `Foo`. Cure needs one here to choose
             the behavior of this operation.

             at missing_eqs.cure:5:37
             5 |   fn test(x: Foo, y: Foo) -> Bool = eqs(x, y)
               |                                     ^^^^^^^^^ this operation requires `Eqs` for `Foo`

             Hint: Add or import `implementation Eqs for Foo`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 36, 45)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "checking" => "eqs",
             "expectation_origin" => "implicit",
             "head_id" => "C3#Foo",
             "head_kind" => "concrete",
             "head_surface" => "Foo",
             "interface" => "Eqs",
             "kind" => "no_instance"
           }

    fixed =
      String.replace(
        source,
        "  fn test",
        "  implementation Eqs for Foo\n    fn eqs(x: Foo, y: Foo) -> Bool = true\n  fn test"
      )

    assert {:ok, _environment} = Program.elaborate(fixed, file: "missing_eqs_fixed.cure")
  end

  test "a polymorphic missing implementation asks for a function constraint without leaking Core" do
    source =
      "mod P\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n  fn same(a: t, b: t) -> Bool = eqs(a, b)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "missing_constraint.cure")

    assert {:no_instance, :Eqs, {:rigid, 0}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NO `EQS` IMPLEMENTATION FOUND [E093] ---------------- missing_constraint.cure

             This expression uses `Eqs` operations on a type variable, but the surrounding
             function does not require `Eqs` for that type.

             at missing_constraint.cure:4:33
             4 |   fn same(a: t, b: t) -> Bool = eqs(a, b)
               |                                 ^^^^^^^^^ this operation requires `Eqs` for its type variable

             Hint: Add a `where Eqs(...)` constraint using this parameter's type variable
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 32, 41)
    assert lsp["data"]["payload"]["head_kind"] == "type_variable"
    assert lsp["data"]["payload"]["head_surface"] == "a type variable"
    refute inspect(lsp["data"]["payload"]) =~ "{:rigid"

    fixed = String.replace(source, "-> Bool = eqs", "-> Bool where Eqs(t) = eqs")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "missing_constraint_fixed.cure")
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
