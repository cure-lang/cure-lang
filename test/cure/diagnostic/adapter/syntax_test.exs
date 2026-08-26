defmodule Cure.Diagnostic.Adapter.SyntaxTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter
  alias Cure.Diagnostic.Adapter.Syntax, as: SyntaxAdapter
  alias Cure.Diagnostic.Renderer
  alias Cure.Diagnostic.SourceRegistry

  test "grade syntax producers are owned directly and retain token repairs" do
    # A bag of decorator-spelled tokens, present only to give the spans below
    # something to point at.
    source = "[h | t] @linear @liner @affine c :\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:grades, source, "grades.cure")

    {:ok, pattern} = SourceRegistry.span(registry, :grades, 0, 7)
    {:ok, binding_grade} = SourceRegistry.span(registry, :grades, 8, 15)
    {:ok, typo} = SourceRegistry.span(registry, :grades, 16, 22)
    {:ok, missing_type} = SourceRegistry.span(registry, :grades, 23, 30)

    errors = [
      {:graded_let_requires_variable, %{grade: :linear, pattern_span: pattern, grade_span: binding_grade}},
      {:unknown_grade,
       %{
         grade: "liner",
         supported: [:erased, :linear, :affine],
         span: typo
       }},
      {:grade_requires_type, %{name: "c", grade: :affine, span: missing_type}}
    ]

    for error <- errors do
      direct = SyntaxAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.suggestions != []
    end

    typo_diagnostic = SyntaxAdapter.from_error(Enum.at(errors, 1))

    assert [
             %{
               applicability: :machine_applicable,
               edits: [%{span: ^typo, replacement: "@linear"}]
             }
           ] = typo_diagnostic.suggestions

    rendered = Renderer.plain(typo_diagnostic, registry, width: 80)
    assert rendered =~ "UNKNOWN RELEVANCE GRADE [E093]"
    assert rendered =~ "^^^^^^ this grade is not defined"
    assert rendered =~ "Hint: Replace it with `@linear`"
  end

  test "unowned errors are rejected by the family boundary" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      SyntaxAdapter.from_error({:unknown_syntax_producer, %{}})
    end
  end

  test "pattern-only forms retain their authored punctuation and body" do
    source = ".value {field = pattern}\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:patterns, source, "patterns.cure")

    {:ok, dot} = SourceRegistry.span(registry, :patterns, 0, 1)
    {:ok, value} = SourceRegistry.span(registry, :patterns, 1, 6)
    {:ok, implicit} = SourceRegistry.span(registry, :patterns, 7, 24)
    {:ok, field} = SourceRegistry.span(registry, :patterns, 8, 13)
    {:ok, pattern} = SourceRegistry.span(registry, :patterns, 16, 23)

    forced =
      {:source_context, {:forced_pattern_not_in_pattern, []},
       %{span: value, opener_span: dot, body_span: value, checking: :run}}

    named =
      {:source_context, {:named_implicit_not_in_pattern, []},
       %{
         span: implicit,
         name_span: field,
         body_span: pattern,
         checking: :run
       }}

    for error <- [forced, named] do
      direct = SyntaxAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.secondary != []
      assert direct.suggestions != []
    end

    forced_diagnostic = SyntaxAdapter.from_error(forced)
    assert forced_diagnostic.primary.span == dot
    assert hd(forced_diagnostic.secondary).span == value

    rendered = Renderer.plain(forced_diagnostic, registry, width: 80)
    assert rendered =~ "FORCED VALUE APPEARS OUTSIDE A PATTERN"
    assert rendered =~ "Hint: Remove the leading dot"

    for error <- [
          {:forced_pattern_not_in_pattern, :value},
          {:named_implicit_not_in_pattern, :field}
        ] do
      assert Adapter.from_error(error) == SyntaxAdapter.from_error(error)
    end
  end

  test "dependent-index lowering failures retain the complete authored form" do
    source = "Z + Z\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:index, source, "index.cure")

    {:ok, span} = SourceRegistry.span(registry, :index, 0, 5)

    errors = [
      {:bad_result_type, %{family: :Vector, shape: :tuple_type, span: span}},
      {:non_integer_index, %{value: "1.5", span: span}},
      {:unsupported_index_literal, %{subtype: :symbol, span: span}},
      {:unsupported_index_expr, %{shape: :list, span: span}},
      {:unsupported_index_operator, %{operator: :+, span: span}},
      {:sigma_projection_needs_ctx, %{projection: 1, span: span}}
    ]

    for error <- errors do
      direct = SyntaxAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary.span == span
      assert direct.suggestions != []
    end

    rendered =
      SyntaxAdapter.from_error({:unsupported_index_operator, %{operator: :+, span: span}})
      |> Renderer.plain(registry, width: 80)

    assert rendered =~ "`+` IS NOT SUPPORTED DIRECTLY IN AN INDEX"
    assert rendered =~ "^^^^^ this operator has no direct index lowering"
    assert rendered =~ "Hint: Define the computation as a total function"
  end

  test "unsupported surface structures retain nested AST source ownership" do
    source = "[head | tail]\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:surface, source, "surface.cure")

    {:ok, span} = SourceRegistry.span(registry, :surface, 0, 13)

    detail =
      {:list_pattern, [source_info: %Cure.MetaAST.SourceInfo{whole: span}], []}

    error =
      {:source_context, {:unsupported_comprehension_pattern, detail}, %{span: nil}}

    direct = SyntaxAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.primary.span == span
    assert direct.payload.observed_shape == :list_pattern
    assert direct.suggestions != []

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "LIST GENERATOR NEEDS A VARIABLE PATTERN"
    assert rendered =~ "^^^^^^^^^^^^^ bind one variable in this generator"
    assert rendered =~ "Hint: Bind one name here"

    for kind <- [
          :unsupported_binary_generator_pattern,
          :unsupported_binary_segment,
          :unsupported_binary_match_arm,
          :unsupported_map_match_arm,
          :unsupported_map_value_pattern,
          :unsupported_map_key_pattern,
          :unsupported_block_statement,
          :unsupported_block
        ] do
      error = {kind, detail}

      assert Adapter.from_error(error, span: span) ==
               SyntaxAdapter.from_error(error, span: span)
    end
  end
end
