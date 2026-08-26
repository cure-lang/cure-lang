defmodule Cure.Compiler.NamedImplicitUnforcedDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @preamble """
  mod Unforced
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
    type Pack(a: Type) indices ()
      pk : Vec(a, m) -> Pack(a)
  """

  test "a dot on an unforced named implicit labels the check, field, and constructor" do
    source =
      @preamble <>
        """
          fn bad({a: Type}, pack: Pack(a)) -> Nat = match pack
            pk({m = .(S(Z()))}, value) -> Z()
        end
        """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:named_implicit_unforced, "m"} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `M` IS NOT FIXED BY MATCHING `PK` [E011] ---------------------- unforced.cure

             The result type of `pk` does not determine its hidden `m` field. A dot pattern
             can only check a value already fixed by the scrutinee, so this field must be
             bound to a variable instead.

             at unforced.cure:9:13
             9 |     pk({m = .(S(Z()))}, value) -> Z()
               |     -- --------------- `pk` does not expose `m` in its result index; this pattern refers to hidden field `m`
               |             ^^^^^^^^ this dot expression has no forced value to check

             Hint: Replace the dot expression with a variable binding, for example `{m = value}`
             """)

    assert diagnostic.payload == %{
             kind: :named_implicit_unforced,
             constructor: "pk",
             implicit_name: "m",
             expectation_origin: :pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(8, 12, 8, 20)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(8, 7, 8, 22),
             range(8, 4, 8, 6)
           ]
  end

  test "binding an unforced named implicit to a variable elaborates" do
    source =
      @preamble <>
        """
          fn good({a: Type}, pack: Pack(a)) -> Nat = match pack
            pk({m = hidden}, value) -> Z()
        end
        """

    assert {:ok, _env} = Program.elaborate(source, file: "unforced.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "unforced.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "unforced.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
