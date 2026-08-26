defmodule Cure.Compiler.MatchScrutineeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  test "constructor branches point to every incompatible pattern and the actual scrutinee" do
    source = """
    mod MatchNonData
      type Nat = Z | S(Nat)
      fn f() -> Int = match 1.0
        Z() -> 1
        S(n) -> 2
    end
    """

    {diagnostic, registry} = compile_diagnostic(source, "match_non_data.cure")

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CONSTRUCTOR PATTERNS CANNOT MATCH FLOAT [E093] ---------- match_non_data.cure

             The value being matched has type `Float`, but these branches try to deconstruct
             it with data constructors.

             Constructor patterns work only when the scrutinee belongs to the same
             constructor-defined data type.

             at match_non_data.cure:4:5
             3 |   fn f() -> Int = match 1.0
               |                         --- this expression has type `Float`
             4 |     Z() -> 1
               |     ^^^ this constructor pattern cannot match `Float`
             5 |     S(n) -> 2
               |     ---- `S` expects a data constructor

             Hint: Use a variable or wildcard for the whole `Float` value, a supported literal pattern for a primitive, or match constructor-defined data
             """)

    assert diagnostic.payload == %{
             kind: :match_scrutinee_not_data,
             checking: :f,
             actual_type: "Float",
             constructor_patterns: ["Z", "S"]
           }

    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.span.start_column == 5
    assert diagnostic.primary.message == "this constructor pattern cannot match `Float`"

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.message}) == [
             {3, "this expression has type `Float`"},
             {5, "`S` expects a data constructor"}
           ]

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 7}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]["start"]) == [
             %{"line" => 2, "character" => 24},
             %{"line" => 4, "character" => 4}
           ]

    assert lsp["data"]["payload"]["actual_type"] == "Float"
    assert lsp["data"]["payload"]["constructor_patterns"] == ["Z", "S"]
  end

  test "literal and constructor-defined repairs both compile" do
    literal_repair = """
    mod LiteralMatchRepair
      fn f(value: Float) -> Int = match value
        1.0 -> 1
        _ -> 2
    end
    """

    data_repair = """
    mod DataMatchRepair
      type Nat = Z | S(Nat)
      fn f(value: Nat) -> Int = match value
        Z() -> 1
        S(_) -> 2
    end
    """

    assert {:ok, :"Cure.LiteralMatchRepair", []} =
             Cure.Compiler.compile_string(literal_repair,
               file: "literal_match_repair.cure",
               emit_events: false
             )

    assert {:ok, :"Cure.DataMatchRepair", []} =
             Cure.Compiler.compile_string(data_repair, file: "data_match_repair.cure", emit_events: false)
  end

  defp compile_diagnostic(source, file) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: file, emit_events: false)

    Errors.to_diagnostic(reason, file, source)
  end
end
