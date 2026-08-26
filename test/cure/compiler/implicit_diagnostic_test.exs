defmodule Cure.Compiler.ImplicitDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer

  test "an unconstrained implicit labels the call and insufficient result annotation" do
    source = "mod DiagnosticImplicit\n  fn bad() -> Int = reflexive()\n"

    assert {:error,
            {:codegen_error,
             {:source_context, {:unsolved_metavariables, :"Std.Equivalent#reflexive"}, context} = reason}} =
             Cure.Compiler.compile_string(source, file: "implicit.cure", emit_events: false)

    assert context.span.start_column == 21
    assert context.span.end_column == 32
    assert context.expectation_span.start_column == 15
    assert context.expectation_span.end_column == 18

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "implicit.cure", source)

    assert diagnostic.code == "E011"
    assert diagnostic.payload.name == :"Std.Equivalent#reflexive"
    assert diagnostic.payload.expectation_origin == :implicit
    assert diagnostic.payload.expression_category == :function_call
    assert length(diagnostic.secondary) == 1
    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MISSING IMPLICIT ARGUMENT [E011] ------------------------------ implicit.cure

             Cure could not infer every implicit argument for `Std.Equivalent#reflexive` at
             this call site.

             The call leaves hidden type or index values unconstrained. Provide arguments
             that determine them, or use the result where its dependent type is known.

             at implicit.cure:2:21
             2 |   fn bad() -> Int = reflexive()
               |               ---   ^^^^^^^^^^^ this result annotation still leaves them unknown; these hidden arguments cannot be inferred

             Hint: Provide arguments or a result type that determines the hidden values
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 1, "character" => 20},
             "end" => %{"line" => 1, "character" => 31}
           }

    assert [%{"message" => "this result annotation still leaves them unknown", "location" => location}] =
             lsp["relatedInformation"]

    assert location["range"] == %{
             "start" => %{"line" => 1, "character" => 14},
             "end" => %{"line" => 1, "character" => 17}
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]
  end
end
