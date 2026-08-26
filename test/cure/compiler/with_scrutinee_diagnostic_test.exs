defmodule Cure.Compiler.WithScrutineeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  test "ordinary with reports the primitive scrutinee and labels every authored region" do
    source = """
    mod OrdinaryNonData
      fn f() -> Int = with 1.0
        _ -> 1
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "ordinary_non_data.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH REQUIRES A DATA VALUE [E093] -------------------- ordinary_non_data.cure

             This `with` scrutinee has type `Float`, which does not provide data constructors
             to refine.

             A `with` block refines its surrounding goal through the constructors of the
             value after `with`; it is not a general conditional.

             at ordinary_non_data.cure:2:24
             2 |   fn f() -> Int = with 1.0
               |                   ---- ^^^ this `with` tries to refine the value by constructors; `Float` cannot be split into constructor branches
             3 |     _ -> 1
               |     ------ this branch cannot refine a value without constructors

             Hint: Use `pickup` for conditions on primitive values, or remove `with` when no constructor refinement is needed
             """)

    assert diagnostic.payload == %{
             kind: :with_scrutinee_not_data,
             checking: :f,
             actual_type: "Float",
             with_form: :ordinary,
             branch_count: 1
           }

    assert diagnostic.primary.span.start_column == 24
    assert diagnostic.primary.span.end_column == 27

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.message}) == [
             {2, "this `with` tries to refine the value by constructors"},
             {3, "this branch cannot refine a value without constructors"}
           ]

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 1, "character" => 23},
             "end" => %{"line" => 1, "character" => 26}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]["start"]) == [
             %{"line" => 1, "character" => 18},
             %{"line" => 2, "character" => 4}
           ]

    assert lsp["data"]["payload"]["actual_type"] == "Float"
    assert lsp["data"]["payload"]["with_form"] == "ordinary"
  end

  test "rematch form explains why restating parent patterns requires data" do
    source = """
    mod RematchNonData
      fn f(x: Int) -> Int = with 1.0
        x | _ -> x
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "rematch_non_data.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH REQUIRES A DATA VALUE [E093] --------------------- rematch_non_data.cure

             This `with` scrutinee has type `Float`, which does not provide data constructors
             to refine.

             A rematch branch can restate the parent patterns only when the value after
             `with` belongs to a constructor-defined data type.

             at rematch_non_data.cure:2:30
             2 |   fn f(x: Int) -> Int = with 1.0
               |                         ---- ^^^ this `with` tries to refine the value by constructors; `Float` cannot be split into constructor branches
             3 |     x | _ -> x
               |     ---------- this rematch branch needs a constructor-defined `with` value

             Hint: Use `pickup` for conditions on primitive values, or remove `with` when no constructor refinement is needed
             """)

    assert diagnostic.payload.with_form == :rematch
    assert diagnostic.payload.actual_type == "Float"
    assert diagnostic.primary.span.start_column == 30

    assert Enum.at(diagnostic.secondary, 1).message ==
             "this rematch branch needs a constructor-defined `with` value"
  end

  test "constructor-defined with and removal of an unnecessary with both compile" do
    data_repair = """
    mod DataWithRepair
      type Nat = Z | S(Nat)
      fn f(n: Nat) -> Nat = with n
        Z() -> Z()
        S(k) -> S(k)
    end
    """

    removal_repair = """
    mod RemovedWithRepair
      fn f() -> Int = 1
    end
    """

    assert {:ok, :"Cure.DataWithRepair", []} =
             Cure.Compiler.compile_string(data_repair, file: "data_with_repair.cure", emit_events: false)

    assert {:ok, :"Cure.RemovedWithRepair", []} =
             Cure.Compiler.compile_string(removal_repair,
               file: "removed_with_repair.cure",
               emit_events: false
             )
  end

  defp compile_diagnostic(source, file) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: file, emit_events: false)

    Errors.to_diagnostic(reason, file, source)
  end
end
