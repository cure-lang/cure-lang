defmodule Cure.Elab.EffectErasureTest do
  # §5.3 of the effect-type-former design: an `Effect`-typed binder may not be
  # `:erased`. Erasure deletes erased binders from the runtime term, so an erased
  # `Effect(T)` binder would silently drop a computation the type says must run —
  # unsound. The check walks the def's final Pi spine and rejects an erased binder
  # whose domain is `Effect`-headed. A PRESENT (ω) effect binder is fine (an
  # un-run effect value, like an unused `IO` action in Haskell); an erased
  # NON-effect binder is fine (the ordinary erased-implicit case).
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an erased implicit Effect binder is rejected" do
    src = """
    mod M
      fn f({e: Effect(Int)}) -> Int = 3
    end
    """

    assert {:error, error} = Program.elaborate(src, file: "effect_binder.cure")
    assert {:effect_binder_erased, %{def: :f, binder: 0}} = Program.semantic_error(error)

    {diagnostic, registry} = Errors.to_diagnostic(error, "effect_binder.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- EFFECT PARAMETER CANNOT BE ERASED [E093] ----------------- effect_binder.cure

             The parameter `e` carries an `Effect` value, but implicit braces mark it for
             erasure. Removing that parameter at runtime could discard a computation the type
             says must remain available.

             at effect_binder.cure:2:10
             2 |   fn f({e: Effect(Int)}) -> Int = 3
               |         -^^^^^^^^^^^^^ this parameter is declared inside erased implicit braces; this `Effect` type requires a runtime-present parameter

             Hint: Make `e` a present parameter by removing the implicit braces
             """)

    assert diagnostic.payload == %{
             kind: :effect_binder_erased,
             definition: :f,
             expression_category: :effect_binder,
             binder: "e",
             binder_index: 0
           }

    assert [suggestion] = diagnostic.suggestions
    assert suggestion.applicability == :machine_applicable
    assert Enum.map(suggestion.edits, & &1.replacement) == ["", ""]

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 1, "character" => 9},
             "end" => %{"line" => 1, "character" => 22}
           }

    assert Enum.map(lsp["data"]["suggestions"] |> hd() |> Map.fetch!("edits"), & &1["range"]) == [
             %{
               "start" => %{"line" => 1, "character" => 7},
               "end" => %{"line" => 1, "character" => 8}
             },
             %{
               "start" => %{"line" => 1, "character" => 22},
               "end" => %{"line" => 1, "character" => 23}
             }
           ]

    repaired = String.replace(src, "{e: Effect(Int)}", "e: Effect(Int)")
    assert {:ok, _env} = Program.elaborate(repaired, file: "effect_binder.cure")
  end

  test "a PRESENT (omega) Effect binder is accepted (un-run effect value)" do
    src = """
    mod M
      fn g(e: Effect(Int)) -> Int = 3
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an erased NON-effect implicit binder is still accepted (ordinary case)" do
    src = """
    mod M
      fn h({x: Int}) -> Int = 3
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
