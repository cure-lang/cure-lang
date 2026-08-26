defmodule Cure.Elab.LocalBindingAnnotationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a graded non-inferable initializer labels the grade and initializer" do
    source =
      "mod L\n  fn ap(@linear g : (Int) -> Int, n: Int) -> Int = g(n)\n  fn f(n: Int) -> Int =\n    let @linear h = fn(x) -> x + 1\n    ap(h, n)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "graded_let.cure")

    assert {:graded_let_needs_annotation,
            %{name: "h", grade: :linear, use_count: 1, reason: :initializer_not_inferable}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- GRADED BINDING NEEDS A TYPE [E093] -------------------------- graded_let.cure

             `h` is declared `linear`, but its initializer has no type Cure can synthesize
             without an expectation. Preserving the grade requires a real local binder, and
             Cure cannot construct that binder until its type is written.

             at graded_let.cure:4:9
             4 |     let @linear h = fn(x) -> x + 1
               |         ^^^^^^^     -------------- this grade cannot be preserved without a binding type; this initializer needs an expected type

             Hint: Write the initializer's type after `h :`, before `=`
             """)

    assert_ranges(diagnostic, registry, range(3, 8, 15), [range(3, 20, 34)])

    assert Renderer.lsp(diagnostic, registry)["data"]["payload"] == %{
             "grade" => "linear",
             "kind" => "graded_let_needs_annotation",
             "name" => "h",
             "reason" => "initializer_not_inferable",
             "use_count" => 1
           }

    fixed = String.replace(source, "let @linear h =", "let @linear h : (Int) -> Int =")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "graded_fixed.cure")
  end

  test "a repeated non-inferable initializer explains that substitution would duplicate it" do
    source =
      "mod L\n  fn ap(g: (Int) -> Int, n: Int) -> Int = g(n)\n  fn f(n: Int) -> Int =\n    let h = fn(x) -> x + 1\n    ap(h, n) + ap(h, n)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "repeated_let.cure")

    assert {:let_needs_annotation, %{name: "h", use_count: 2}} = Program.semantic_error(error)
    assert diagnostic.title == "Repeated binding needs a type"
    assert Renderer.plain(diagnostic, registry, width: 80) =~ "duplicate the expression"
    assert hd(diagnostic.suggestions).message =~ "bound once"
    assert_ranges(diagnostic, registry, range(3, 8, 9), [range(3, 12, 26)])
  end

  test "an unused non-inferable initializer explains that substitution would discard it" do
    source = "mod L\n  fn f(n: Int) -> Int =\n    let h = fn(x) -> x + 1\n    n\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "unused_let.cure")

    assert {:let_needs_annotation, %{name: "h", use_count: 0}} = Program.semantic_error(error)
    assert diagnostic.title == "Unused binding needs a type"
    assert Renderer.plain(diagnostic, registry, width: 80) =~ "discard the initializer"
    assert hd(diagnostic.suggestions).message =~ "checked exactly once"
    assert_ranges(diagnostic, registry, range(2, 8, 9), [range(2, 12, 26)])
  end

  test "a non-inferable initializer labels the inner binder that shadows it" do
    source =
      "mod L\n  fn f(n: Int) -> Int =\n    let h = fn(x) -> x + 1\n    match n\n      h -> h\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "shadowed_let.cure")

    assert {:let_needs_annotation, %{name: "h", reason: :shadowed_before_use, shadow_span: shadow_span}} =
             Program.semantic_error(error)

    assert shadow_span.start_line == 5
    assert shadow_span.start_column == 7

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- SHADOWED BINDING NEEDS A TYPE [E093] ---------------------- shadowed_let.cure

             Cure cannot synthesize a type for `h`'s initializer. A later binder also uses
             the name `h`, so substituting this initializer would cross that binding boundary
             and could capture the wrong value.

             at shadowed_let.cure:3:9
             3 |     let h = fn(x) -> x + 1
               |         ^   -------------- this binding needs a type before it can cross a shadowing scope; this initializer needs an expected type
             4 |     match n
             5 |       h -> h
               |       - this inner binder shadows `h`

             Hint: Add a type between `h` and `=` so this value is bound once before the inner `h`
             """)

    assert_ranges(
      diagnostic,
      registry,
      range(2, 8, 9),
      [range(2, 12, 26), range(4, 6, 7)]
    )

    assert Renderer.lsp(diagnostic, registry)["data"]["payload"] == %{
             "grade" => nil,
             "kind" => "let_needs_annotation",
             "name" => "h",
             "reason" => "shadowed_before_use",
             "use_count" => 1
           }

    fixed = String.replace(source, "let h =", "let h : (Int) -> Int =")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "shadowed_fixed.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp assert_ranges(diagnostic, registry, primary, related) do
    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == primary
    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == related
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
