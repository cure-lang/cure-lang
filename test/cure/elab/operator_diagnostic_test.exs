defmodule Cure.Elab.OperatorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an unsupported operand pair labels the operator and both operands" do
    source = "mod M\n  fn bad() = true - false\nend\n"
    {diagnostic, registry} = diagnostic(source, "operator_types.cure", :unsupported_operand_type)

    assert diagnostic.code == "E093"
    assert diagnostic.key == :operator_type_mismatch

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `-` DOES NOT SUPPORT THESE OPERANDS [E093] -------------- operator_types.cure

             The `-` operator does not accept `Bool` on the left and `Bool` on the right.

             at operator_types.cure:2:19
             2 |   fn bad() = true - false
               |              ---- ^ ----- the left operand has type `Bool`; this operator is not defined for these operand types; the right operand has type `Bool`

             Hint: Change the operand types, or use an operator or interface implementation defined for them
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 18, 19)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(1, 13, 17),
             range(1, 20, 25)
           ]
  end

  test "a fixity without a callable definition points at the operator use" do
    source =
      "mod M\n  use Std.Operators\n  infix `<@>` : Additive\n  fn bad() -> Int = 1 <@> 2\nend\n"

    {diagnostic, registry} = diagnostic(source, "operator_meaning.cure", :no_operator_meaning)

    assert diagnostic.code == "E093"
    assert diagnostic.key == :operator_resolution

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `<@>` HAS NO DEFINITION [E093] ------------------------ operator_meaning.cure

             A fixity declaration tells Cure how to parse `<@>`, but no function,
             constructor, or interface method with that name is available here.

             at operator_meaning.cure:4:23
             4 |   fn bad() -> Int = 1 <@> 2
               |                       ^^^ this operator has precedence, but no callable definition

             Hint: Define `<@>` with two parameters, import its definition, or use an operator that is in scope
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 22, 25)
    assert lsp["relatedInformation"] == []
  end

  defp diagnostic(source, file, kind) do
    assert {:error, error} = Program.elaborate(source, file: file)
    semantic = Program.semantic_error(error)
    assert is_tuple(semantic) and elem(semantic, 0) == kind
    Cure.Compiler.Errors.to_diagnostic(error, file, source)
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
