defmodule Cure.Diagnostic.Adapter.StaticAnalysisTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.StaticAnalysis

  test "relevance rejection labels the erased binder and its runtime use" do
    source = "n n\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:relevance, source, "relevance.cure")
    {:ok, binder_span} = SourceRegistry.span(registry, :relevance, 0, 1)
    {:ok, use_span} = SourceRegistry.span(registry, :relevance, 2, 3)

    error =
      {:source_context, {:erased_used_relevantly, %{binder: 2, site: :returned}},
       %{span: use_span, binder_span: binder_span, binder_name: :n}}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- ERASED VALUE USED RELEVANTLY [E104] -------------------------- relevance.cure

             The erased parameter `n` is used as the function's runtime result, but erased
             parameters do not exist at runtime.

             at relevance.cure:1:3
             1 | n n
               | - ^ `n` is erased here; this returns an erased value at runtime

             Hint: Declare `n` as a runtime parameter, or keep it out of runtime expressions
             """
             |> String.trim_trailing()
  end

  test "the static-analysis family rejects unrelated failures" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      StaticAnalysis.from_error({:conversion_failure, :actual, :expected})
    end
  end

  test "totality labels every recursive call and the owning declaration" do
    source = "fn loop() = loop() + loop()\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:totality, source, "totality.cure")

    {:ok, definition} = SourceRegistry.span(registry, :totality, 0, 27)
    {:ok, first_call} = SourceRegistry.span(registry, :totality, 12, 16)
    {:ok, second_call} = SourceRegistry.span(registry, :totality, 21, 25)

    error =
      {:source_context, {:compile_time_totality, :"Main#loop", :not_total},
       %{
         definition_span: definition,
         recursive_call_spans: [first_call, second_call],
         checking: :"Main#loop"
       }}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E013"
    assert direct.payload.reason == :not_total
    assert direct.primary.span == first_call
    assert Enum.map(direct.secondary, & &1.span) == [second_call, definition]

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- FUNCTION MUST BE TOTAL [E013] --------------------------------- totality.cure

             `Main#loop` is evaluated while checking types, but the compiler cannot prove
             that every call to it terminates.

             at totality.cure:1:13
             1 | fn loop() = loop() + loop()
               | --------------------------- this type-level function must terminate on every input
               |             ^^^^     ---- this recursive call participates in an unproven termination cycle; another recursive call in this cycle is here

             Note: Runtime-only functions may remain partial; only compile-time computation
                   requires a total definition.

             Hint: Make each recursive call use a structurally smaller argument, or keep this function out of types
             """
             |> String.trim_trailing()
  end

  test "an unresolved totality dependency preserves the exact closure path" do
    diagnostic =
      Adapter.from_error(
        {:totality_closure_unresolved,
         %{
           definition: :"Proof.Missing#lemma",
           root: :"Proof.Owner#theorem",
           closure_path: [:"Proof.Owner#theorem", :"Proof.Helper#step", :"Proof.Missing#lemma"]
         }}
      )

    assert diagnostic.code == "E013"
    assert diagnostic.key == :totality_closure_unresolved
    assert diagnostic.payload.definition == :"Proof.Missing#lemma"

    assert diagnostic.payload.closure_path == [
             :"Proof.Owner#theorem",
             :"Proof.Helper#step",
             :"Proof.Missing#lemma"
           ]

    rendered = Renderer.plain(diagnostic, nil, width: 80)
    assert rendered =~ "TOTALITY DEPENDENCY DOES NOT RESOLVE"
    assert rendered =~ "Closure path: Proof.Owner#theorem -> Proof.Helper#step ->"
    assert rendered =~ "Proof.Missing#lemma"
  end

  test "a failed size-change proof reports the exact SCC, loop, diagonal, and call path" do
    reason = %{
      reason: :not_decreasing,
      members: [:f, :g],
      offending_edge: %{
        source: :f,
        target: :f,
        diagonal: [:equal],
        source_call_path: [{:f, :g}, {:g, :f}]
      }
    }

    diagnostic =
      Adapter.from_error({:source_context, {:totality_required, :f}, %{totality_reason: reason}})

    rendered = Renderer.plain(diagnostic, nil, width: 100)
    assert rendered =~ "Totality SCC: f, g"
    assert rendered =~ "Offending idempotent loop: f -> f; diagonal [:equal]"
    assert rendered =~ "Source-call path: f -> g; g -> f"
    assert diagnostic.payload.reason == reason
  end

  test "invalid proof certificates render structured diagnostic details" do
    diagnostic =
      Adapter.from_error(
        {:totality_derivation_invalid, %{reason: :composition_mismatch, edge: <<1, 2>>, left: <<3>>, right: <<4>>}}
      )

    assert diagnostic.code == "E013"
    assert diagnostic.key == :totality_derivation_invalid
    assert diagnostic.payload.reason == :composition_mismatch
    assert Renderer.plain(diagnostic, nil) =~ "TOTALITY DERIVATION IS INVALID"
  end

  test "resource usage preserves declaration and earlier-use regions" do
    source = "x x x\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:usage, source, "usage.cure")
    {:ok, binder_span} = SourceRegistry.span(registry, :usage, 0, 1)
    {:ok, first_use} = SourceRegistry.span(registry, :usage, 2, 3)
    {:ok, second_use} = SourceRegistry.span(registry, :usage, 4, 5)

    error =
      {:source_context, {:usage_violation, %{binder: 0, declared: :linear, used: :unrestricted}},
       %{
         span: second_use,
         binder_span: binder_span,
         binder_name: :x,
         use_spans: [first_use, second_use]
       }}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E117"
    assert Enum.map(direct.secondary, & &1.span) == [binder_span, first_use]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "another use on this path is here"
    assert rendered =~ "this parameter is declared `linear` here"
    assert rendered =~ "Hint: Pass `x` only to linear parameters"
  end

  test "pattern coverage owns missing, impossible, duplicate, and tuple gaps" do
    source = "Z() Z()\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:coverage, source, "coverage.cure")
    {:ok, first} = SourceRegistry.span(registry, :coverage, 0, 3)
    {:ok, duplicate} = SourceRegistry.span(registry, :coverage, 4, 7)

    context = %{
      span: duplicate,
      branch_patterns: [
        %{name: "Z", pattern_span: first, span: first},
        %{name: "Z", pattern_span: duplicate, span: duplicate}
      ]
    }

    errors = [
      {:source_context, {:missing_branch, :"Main#S"}, context},
      {:source_context, {:reachable_impossible, :"Main#Z"}, context},
      {:source_context, {:duplicate_branch, :"Main#Z"}, context},
      {:source_context,
       {:tuple_missing_branch, %{branch: :"Main#S", tuple_pattern_position: 1, tuple_pattern_arity: 2}}, context}
    ]

    for error <- errors do
      direct = StaticAnalysis.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E118"
      assert direct.primary.span
      assert direct.suggestions != []
    end
  end

  test "pattern structure owns nonlinear, catch-all, binary, and map failures" do
    source = "x x\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:structure, source, "structure.cure")
    {:ok, first} = SourceRegistry.span(registry, :structure, 0, 1)
    {:ok, second} = SourceRegistry.span(registry, :structure, 2, 3)

    context = %{
      span: second,
      branch_patterns: [
        %{kind: :variable, span: first, variable_spans: %{"x" => [first, second]}},
        %{kind: :variable, span: second}
      ]
    }

    errors = [
      {:source_context, {:nonlinear_pattern, "x"}, context},
      {:source_context, {:duplicate_default_pattern, "x"}, context},
      {:source_context, {:impossible_default_pattern, "x"}, context},
      {:source_context, {:unreachable_after_default_pattern, %{name: "x", span: second, default_span: first}}, context},
      {:source_context, {:binary_match_needs_default}, context},
      {:source_context, {:map_match_needs_default}, context}
    ]

    for error <- errors do
      direct = StaticAnalysis.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E119"
      assert direct.primary.span
      assert direct.suggestions != []
    end
  end

  test "erasure validation labels the decorator argument and owning type" do
    source = "@erases(:banana)\nopaque type Handle\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:erasure, source, "erasure.cure")

    {:ok, decorator} = SourceRegistry.span(registry, :erasure, 0, 16)
    {:ok, argument} = SourceRegistry.span(registry, :erasure, 8, 15)
    {:ok, name} = SourceRegistry.span(registry, :erasure, 29, 35)

    error =
      {:source_context, {:unknown_erasure_class, :Handle, :banana},
       %{decorator_span: decorator, argument_spans: [argument], name_span: name}}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E102"
    assert direct.primary.span == argument
    assert Enum.map(direct.secondary, & &1.span) == [decorator, name]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "^^^^^^^ this runtime class is not supported"
    assert rendered =~ "this is the complete erasure declaration"
    assert rendered =~ "this type receives the erasure declaration"
    assert rendered =~ "Hint: Choose one of pid, reference"
  end
end
