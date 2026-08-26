defmodule Cure.Compiler.ConstructorResultFamilyDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a constructor returning another family labels its result, constructor, and declaring family" do
    source = """
    mod BadResult
      type Nat = Z | S(Nat)
      type Vec(a: Type) indices (n: Nat)
        Bad : Nat
    end
    """

    {diagnostic, registry, error} = diagnostic(source, "bad_result.cure")

    assert {:result_type_not_family, :Vec} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `BAD` RETURNS `NAT` INSTEAD OF `VEC` [E093] ----------------- bad_result.cure

             Every constructor must produce a value of the type family that declares it.
             `Bad` is declared under `Vec`, but the final type in its signature is `Nat`.

             at bad_result.cure:4:11
             3 |   type Vec(a: Type) indices (n: Nat)
               |        --- `Vec` is the family being declared
             4 |     Bad : Nat
               |     ---   ^^^ this constructor belongs to `Vec`; this result names `Nat`, not constructor family `Vec`

             Hint: End this constructor signature with `Vec` applied to its 1 parameter and 1 index
             """)

    assert diagnostic.payload == %{
             kind: :result_type_not_family,
             family: "Vec",
             observed_family: "Nat",
             constructor: "Bad",
             parameter_count: 1,
             index_count: 1
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 10, 3, 13)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(3, 4, 3, 7),
             range(2, 7, 2, 10)
           ]
  end

  test "a nullary family gets the concise repair shape" do
    source = """
    mod NullaryResult
      type Other = OtherValue
      type Wanted indices ()
        Wrong : Other
    end
    """

    {diagnostic, _registry, _error} = diagnostic(source, "nullary_result.cure")

    assert [%{message: "End this constructor signature with `Wanted`"}] =
             diagnostic.suggestions
  end

  test "returning the declaring family with its parameter and index still elaborates" do
    repaired = """
    mod GoodResult
      type Nat = Z | S(Nat)
      type Vec(a: Type) indices (n: Nat)
        Good : Vec(a, Z)
    end
    """

    assert {:ok, _env} = Program.elaborate(repaired, file: "good_result.cure")
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
