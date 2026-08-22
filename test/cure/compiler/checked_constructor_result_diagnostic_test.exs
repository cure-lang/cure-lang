defmodule Cure.Compiler.CheckedConstructorResultDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an underdetermined field does not hide an incompatible constructor result" do
    source = """
    mod CtorMismatch
      type List(a: Type) = Nil | Cons(a, List(a))
      type Weird indices (a: Type)
        Bad : {b: Type} -> List(b) -> Weird(String)
      fn bad() -> Weird(Int) = Bad(Nil())
    end
    """

    {diagnostic, registry, error} = diagnostic(source, "ctor_mismatch.cure")

    assert {:unsolved_metavariables, :"CtorMismatch#Nil"} = Program.semantic_error(error)
    assert diagnostic.code == "E011"

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `BAD` CANNOT PRODUCE THE EXPECTED INDEXED TYPE [E011] ---- ctor_mismatch.cure

             This constructor produces `Weird(String)`, but this position requires
             `Weird(Int)`.

             Cure also could not infer the hidden arguments of `Nil` while checking the
             constructor fields. Supplying those arguments cannot make incompatible result
             indices agree.

             at ctor_mismatch.cure:5:28
             5 |   fn bad() -> Weird(Int) = Bad(Nil())
               |               ----------   ^^^^^^^^^^ the surrounding annotation requires `Weird(Int)`; this `Bad` result cannot satisfy `Weird(Int)`
               |                                ----- this argument did not provide enough information to recover from the incompatible result

             Hint: Use a constructor whose result matches `Weird(Int)`, or change the surrounding result type
             """)

    assert diagnostic.payload == %{
             kind: :constructor_result_mismatch,
             semantic_reason: :unsolved_metavariables,
             unsolved_name: "Nil",
             constructor: "Bad",
             expected: "Weird(Int)",
             actual: "Weird(String)",
             checking: "Bad"
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 27, 4, 37)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(4, 14, 4, 24),
             range(4, 31, 4, 36)
           ]
  end

  test "an incompatible constructor head with an unresolved index stays readable" do
    source = """
    mod FinMismatch
      type Nat = Z | S(Nat)
      type Fin indices (n: Nat)
        FZ : Fin(S(n))
      fn bad() -> Fin(Z) = FZ()
    end
    """

    {diagnostic, _registry, error} = diagnostic(source, "fin_mismatch.cure")

    assert {:unsolved_metavariables, :"FinMismatch#FZ"} = Program.semantic_error(error)
    assert diagnostic.payload.actual == "Fin(S(?))"
    refute inspect(diagnostic.payload) =~ "{:data"
    refute inspect(diagnostic.body) =~ "{:data"
  end

  test "a result-compatible constructor lets the expected index determine a nested constructor" do
    repaired = """
    mod CtorRepair
      type List(a: Type) = Nil | Cons(a, List(a))
      type Weird indices (a: Type)
        Good : {b: Type} -> List(b) -> Weird(b)
      fn good() -> Weird(Int) = Good(Nil())
    end
    """

    assert {:ok, _env} = Program.elaborate(repaired, file: "ctor_repair.cure")
  end

  test "a constructor declaration type error retains the failing constructor site" do
    source = """
    mod ConstructorDeclarationMismatch
      type Bound indices (n: Nat)
        First : Bound(S(m))
      type ThreadState indices (n: Nat)
        Active : Bound(n) -> ThreadState(n)
      type Equivalent(a: Type) indices (left: a, right: a)
        reflexive : (value: a) -> Equivalent(a, value, value)
      type Failure(n: Nat) indices (source: Bound(n))
        Failed : (source: Bound(n)) -> Equivalent(ThreadState(n), Active(source), source) -> Failure(n, source)
    end
    """

    assert {:error,
            {:source_context, {:conversion_failure, _found, _expected},
             %{
               constructor: :Failed,
               family: :Failure,
               expression_category: :constructor_signature,
               span: %Cure.Diagnostic.Span{start_line: 9},
               constructor_name_span: %Cure.Diagnostic.Span{start_line: 9}
             }}} = Program.elaborate(source, file: "constructor_declaration_mismatch.cure")
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
