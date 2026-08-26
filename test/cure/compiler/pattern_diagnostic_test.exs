defmodule Cure.Compiler.PatternDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Renderer

  test "a range pattern explains the guard-based repair at the range operator" do
    source =
      "mod DiagnosticPattern\n  fn bad(x: Int) -> Int = match x\n    1..10 -> 1\n    _ -> 0\n"

    assert {:error, reason} =
             Cure.Compiler.compile_string(source, file: "pattern.cure", emit_events: false)

    assert {:codegen_error, {:source_context, {:unsupported_pattern, :range}, context}} = reason
    assert context.span.start_line == 3
    assert context.span.start_column == 6
    assert context.span.end_column == 8

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "pattern.cure", source)
    assert diagnostic.code == "E090"
    refute Map.has_key?(diagnostic.payload.context, :code)
    assert Enum.map(diagnostic.payload.context.branch_patterns, & &1.name) == ["pattern", "_"]

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN IS NOT SUPPORTED [E090] -------------------------------- pattern.cure

             A range describes many values, but a pattern must describe a shape Cure can
             deconstruct. Bind the value and test the range in a guard instead.

             at pattern.cure:3:6
             3 |     1..10 -> 1
               |      ^^ a range operator cannot be used in a pattern

             Hint: Bind the value, then test its bounds with `when`
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 2, "character" => 5},
             "end" => %{"line" => 2, "character" => 7}
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]
  end
end
