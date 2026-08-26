defmodule Cure.Compiler.WithMixedArmDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  test "one ordinary and one rematch branch each receive an exact source label" do
    source = """
    mod MixedWith
      type Nat = Z | S(Nat)
      fn f(n: Nat) -> Nat = with n
        Z() -> Z()
        S(k) | S(k) -> k
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "mixed_with.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH BRANCHES USE INCOMPATIBLE FORMS [E093] ----------------- mixed_with.cure

             These branches mix the two forms accepted by a `with` block.

             Use either `Pattern -> body` in every branch, or `ParentPattern | WithPattern ->
             body` in every branch.

             at mixed_with.cure:4:5
             4 |     Z() -> Z()
               |     ^^^^^^^^^^ ordinary branch: `Pattern -> body`
             5 |     S(k) | S(k) -> k
               |     ---------------- rematch branch: `ParentPattern | WithPattern -> body`

             Hint: Make every branch use the same `with` form; changing forms may change which values are refined
             """)

    assert diagnostic.payload == %{
             kind: :with_mixed_rematch_arms,
             checking: :f,
             branch_forms: [:ordinary, :rematch],
             outlier_branch: nil
           }

    assert [%{message: "rematch branch: `ParentPattern | WithPattern -> body`"}] = diagnostic.secondary
    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 14}
           }

    assert [related] = lsp["relatedInformation"]
    assert related["message"] == "rematch branch: `ParentPattern | WithPattern -> body`"
    assert related["location"]["range"]["start"] == %{"line" => 4, "character" => 4}
    assert lsp["data"]["payload"]["branch_forms"] == ["ordinary", "rematch"]
    assert lsp["data"]["suggestions"] |> hd() |> Map.fetch!("applicability") == "manual"
  end

  test "a unique branch form is singled out as a possible outlier" do
    source = """
    mod WithOutlier
      type Tri = A | B | C
      fn f(n: Tri) -> Tri = with n
        A() -> A()
        B() -> B()
        C() | C() -> C()
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "with_outlier.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH BRANCHES USE INCOMPATIBLE FORMS [E093] --------------- with_outlier.cure

             Possible outlier: only one branch uses the rematch `ParentPattern | WithPattern
             -> body` form; the other branches use the other form.

             A `with` block must use one shape throughout: either `Pattern -> body` in every
             branch, or `ParentPattern | WithPattern -> body` in every branch.

             at with_outlier.cure:6:5
             4 |     A() -> A()
               |     ---------- ordinary branch: `Pattern -> body`
             5 |     B() -> B()
               |     ---------- ordinary branch: `Pattern -> body`
             6 |     C() | C() -> C()
               |     ^^^^^^^^^^^^^^^^ possible outlier: this is the only rematch `ParentPattern | WithPattern -> body` branch

             Hint: Make every branch use the same `with` form; changing forms may change which values are refined
             """)

    assert diagnostic.payload.branch_forms == [:ordinary, :ordinary, :rematch]
    assert diagnostic.payload.outlier_branch == 2
    assert diagnostic.primary.span.start_line == 6
    assert diagnostic.primary.message =~ "possible outlier"
    assert Enum.map(diagnostic.secondary, & &1.span.start_line) == [4, 5]
  end

  test "a unique ordinary branch is also singled out when rematch branches agree" do
    source = """
    mod WithOrdinaryOutlier
      type Tri = A | B | C
      fn f(n: Tri) -> Tri = with n
        A() -> A()
        B() | B() -> B()
        C() | C() -> C()
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "ordinary_outlier.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH BRANCHES USE INCOMPATIBLE FORMS [E093] ----------- ordinary_outlier.cure

             Possible outlier: only one branch uses the ordinary `Pattern -> body` form; the
             other branches use the other form.

             A `with` block must use one shape throughout: either `Pattern -> body` in every
             branch, or `ParentPattern | WithPattern -> body` in every branch.

             at ordinary_outlier.cure:4:5
             4 |     A() -> A()
               |     ^^^^^^^^^^ possible outlier: this is the only ordinary `Pattern -> body` branch
             5 |     B() | B() -> B()
               |     ---------------- rematch branch: `ParentPattern | WithPattern -> body`
             6 |     C() | C() -> C()
               |     ---------------- rematch branch: `ParentPattern | WithPattern -> body`

             Hint: Make every branch use the same `with` form; changing forms may change which values are refined
             """)

    assert diagnostic.payload.branch_forms == [:ordinary, :rematch, :rematch]
    assert diagnostic.payload.outlier_branch == 0
    assert diagnostic.primary.span.start_line == 4
  end

  test "both consistent repairs remain accepted and no unsafe machine edit is offered" do
    ordinary = """
    mod OrdinaryWith
      type Nat = Z | S(Nat)
      fn f(n: Nat) -> Nat = with n
        Z() -> Z()
        S(k) -> S(k)
    end
    """

    rematch = """
    mod RematchWith
      type Nat = Z | S(Nat)
      fn f(n: Nat) -> Nat = with n
        Z() | Z() -> Z()
        S(k) | S(k) -> S(k)
    end
    """

    assert {:ok, :"Cure.OrdinaryWith", []} =
             Cure.Compiler.compile_string(ordinary, file: "ordinary_with.cure", emit_events: false)

    assert {:ok, :"Cure.RematchWith", []} =
             Cure.Compiler.compile_string(rematch, file: "rematch_with.cure", emit_events: false)
  end

  defp compile_diagnostic(source, file) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: file, emit_events: false)

    Errors.to_diagnostic(reason, file, source)
  end
end
