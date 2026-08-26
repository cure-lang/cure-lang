defmodule Cure.Compiler.IndexedWithDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  test "an indexed with proof points to the proof, scrutinee, and every branch" do
    source = """
    mod IndexedWith
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      fn f(n: Nat, s: SNat(n)) -> Nat = with s proof pf
        szero() -> Z()
        ssuc(k) -> S(Z())
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "indexed_with.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- INDEXED WITH CANNOT BIND A VALUE PROOF [E093] ------------- indexed_with.cure

             The `proof pf` clause asks Cure to bind a value equation in every branch.

             `SNat` is indexed, so its branch constructors can refine type indices. Cure
             cannot also synthesize the whole-value equation requested by this form.

             at indexed_with.cure:6:44
             6 |   fn f(n: Nat, s: SNat(n)) -> Nat = with s proof pf
               |                                          - ^^^^^^^^ this value belongs to indexed family `SNat`; this proof binding is unsupported for an indexed `with`
             7 |     szero() -> Z()
               |     -------------- this branch would need an indexed value equation
             8 |     ssuc(k) -> S(Z())
               |     ----------------- this branch would need an indexed value equation

             Hint: Remove `proof pf` when the equation is unused, or rewrite every branch in the indexed LHS-rematch form
             """)

    assert diagnostic.payload == %{
             kind: :with_indexed_scrutinee_unsupported,
             checking: :f,
             family: "SNat",
             proof_name: "pf",
             branch_count: 2
           }

    assert diagnostic.primary.span.start_column == 44
    assert diagnostic.primary.span.end_column == 52
    assert diagnostic.primary.message == "this proof binding is unsupported for an indexed `with`"

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.message}) == [
             {6, "this value belongs to indexed family `SNat`"},
             {7, "this branch would need an indexed value equation"},
             {8, "this branch would need an indexed value equation"}
           ]

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 43},
             "end" => %{"line" => 5, "character" => 51}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]["start"]) == [
             %{"line" => 5, "character" => 41},
             %{"line" => 6, "character" => 4},
             %{"line" => 7, "character" => 4}
           ]

    assert lsp["data"]["payload"]["family"] == "SNat"
    assert lsp["data"]["payload"]["proof_name"] == "pf"
  end

  test "removing an unused proof and using indexed LHS rematching both compile" do
    removed_proof = """
    mod RemovedIndexedProof
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      fn f(n: Nat, s: SNat(n)) -> Nat = with s
        szero() -> Z()
        ssuc(k) -> S(Z())
    end
    """

    lhs_rematch = """
    mod RematchedIndexedProof
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      fn f(n: Nat, s: SNat(n)) -> Nat = with s
        n, szero() | szero() -> Z()
        n, ssuc(k) | ssuc(k) -> S(Z())
    end
    """

    assert {:ok, :"Cure.RemovedIndexedProof", []} =
             Cure.Compiler.compile_string(removed_proof,
               file: "removed_indexed_proof.cure",
               emit_events: false
             )

    assert {:ok, :"Cure.RematchedIndexedProof", []} =
             Cure.Compiler.compile_string(lhs_rematch,
               file: "rematched_indexed_proof.cure",
               emit_events: false
             )
  end

  defp compile_diagnostic(source, file) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: file, emit_events: false)

    Errors.to_diagnostic(reason, file, source)
  end
end
