defmodule Cure.Elab.WithDefaultDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a catch-all in a refining with points at that branch and the constructor branch" do
    source = """
    mod WithDefault
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      fn to_singleton(n: Nat) -> SNat(n) = match n
        Z() -> szero()
        S(k) -> ssuc(to_singleton(k))
      fn choose(n: Nat) -> SNat(n) =
        with n proof pf
          Z() -> szero()
          rest -> to_singleton(rest)
    end
    """

    assert {:error, error} = Program.elaborate(source, file: "with_default.cure")

    assert {:unsupported_pattern, %{reason: :default_in_with, name: "rest"}} =
             Program.semantic_error(error)

    {diagnostic, registry} = Errors.to_diagnostic(error, "with_default.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- `WITH` NEEDS CONSTRUCTOR BRANCHES [E090] ------------------ with_default.cure

             The catch-all pattern `rest` does not identify a constructor, so it cannot
             refine the matched value or any dependent types. A `with` branch must restate
             one concrete constructor.

             at with_default.cure:12:7
             11 |       Z() -> szero()
                |       --- this branch refines a constructor
             12 |       rest -> to_singleton(rest)
                |       ^^^^ replace this catch-all with a constructor pattern

             Hint: Add the remaining constructor branches explicitly, or use `match` when no refinement is needed
             """)

    assert diagnostic.payload == %{
             kind: :unsupported_pattern,
             reason: :default_in_with,
             name: "rest",
             checking: :choose
           }

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 11, "character" => 6},
             "end" => %{"line" => 11, "character" => 10}
           }
  end
end
