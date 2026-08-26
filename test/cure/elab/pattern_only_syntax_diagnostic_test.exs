defmodule Cure.Elab.PatternOnlySyntaxDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a forced value outside a pattern labels the dot and forced expression separately" do
    source = "mod M\n  type Nat = Z | S(Nat)\n  fn f() -> Nat = .x\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "forced_value.cure")

    assert {:forced_pattern_not_in_pattern, _meta} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FORCED VALUE APPEARS OUTSIDE A PATTERN [E093] ------------- forced_value.cure

             A leading dot marks a value that a constructor pattern must equal; it does not
             evaluate or access that value as an ordinary expression. This dot appears in
             expression position, where there is no surrounding pattern to force.

             at forced_value.cure:3:19
             3 |   fn f() -> Nat = .x
               |                   ^- this dot introduces pattern-only syntax; this is the value the pattern would be forced to equal

             Hint: Remove the leading dot to use an ordinary expression, or move the forced value into a constructor pattern
             """)

    assert diagnostic.payload == %{
             kind: :forced_pattern,
             checking: :f,
             expression_category: :forced_pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 18, 2, 19)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(2, 19, 2, 20)

    repaired = String.replace(source, ".x", "Z()")
    assert {:ok, _env} = Program.elaborate(repaired, file: "forced_value.cure")
  end

  test "a named implicit outside a constructor pattern labels its binder and constraint" do
    source = "mod M\n  type Nat = Z | S(Nat)\n  fn f() -> Nat = {k = .x}\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "named_implicit.cure")

    assert {:named_implicit_not_in_pattern, _meta} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NAMED IMPLICIT APPEARS OUTSIDE A PATTERN [E093] --------- named_implicit.cure

             `{name = pattern}` selects an implicit constructor field while matching a value.
             It cannot stand alone as an expression because no constructor pattern owns this
             implicit field.

             at named_implicit.cure:3:19
             3 |   fn f() -> Nat = {k = .x}
               |                   ^^^^^^^^ this named implicit has no surrounding constructor pattern
               |                    -   -- this names the constructor's implicit field; this pattern would constrain that field

             Hint: Move this named implicit inside a constructor pattern, or replace it with an ordinary expression
             """)

    assert diagnostic.payload == %{
             kind: :named_implicit_pattern,
             checking: :f,
             expression_category: :named_implicit_pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 18, 2, 26)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(2, 19, 2, 20),
             range(2, 23, 2, 25)
           ]

    repaired = String.replace(source, "{k = .x}", "Z()")
    assert {:ok, _env} = Program.elaborate(repaired, file: "named_implicit.cure")
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
