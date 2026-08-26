defmodule Cure.Diagnostic.Adapter.TypeTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, ExpectationOrigin, Renderer, SourceRegistry, TypeProblem}
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter

  test "the canonical type family preserves contextual prose, both source labels, and exact output" do
    source = "fn run() -> Int = true\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:type_test, source, "type.cure")
    {:ok, expected_span} = SourceRegistry.span(registry, :type_test, 12, 15)
    {:ok, actual_span} = SourceRegistry.span(registry, :type_test, 18, 22)

    problem = %TypeProblem{
      kind: :type_mismatch,
      actual: "Bool",
      expected: "Int",
      origin: %ExpectationOrigin{kind: :annotation, span: expected_span},
      expression: :literal,
      span: actual_span
    }

    direct = TypeAdapter.from_error(problem)
    assert Adapter.from_error(problem) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- ANNOTATION DOES NOT MATCH [E093] ---------------------------------- type.cure

             This expression does not match the type written in its annotation.

             Expected: Int
             Found:    Bool

             at type.cure:1:19
             1 | fn run() -> Int = true
               |             ---   ^^^^ the expectation comes from here; this expression has the wrong type
             """
             |> String.trim_trailing()
  end

  test "Core and constraints remain debug-only at the family boundary" do
    problem = %TypeProblem{
      kind: :conversion_failure,
      actual: {:data, :Actual, [], []},
      expected: {:data, :Expected, [], []},
      origin: %ExpectationOrigin{kind: :annotation},
      debug: %{constraints: [{:cannot_unify, :actual, :expected}]}
    }

    regular = TypeAdapter.from_error(problem)
    debug = TypeAdapter.from_error(problem, debug: true)

    refute Map.has_key?(regular.payload, :debug)
    refute Renderer.json(regular) =~ "cannot_unify"
    assert debug.payload.debug.details == problem.debug
    assert Renderer.json(debug) =~ "cannot_unify"
  end

  test "effect arity failures are owned by the type family" do
    error = {:effect_arity, :send, 2, 1}
    direct = TypeAdapter.from_error(error)

    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.key == :type_mismatch
    assert hd(direct.suggestions).message =~ "arguments required"
  end

  test "character literal failures are owned by the type family" do
    error = {:char_literal_needs_bounded, 97}
    direct = TypeAdapter.from_error(error)

    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.key == :type_mismatch
    assert direct.title == "Character literal needs a bound"
    assert hd(direct.suggestions).message == "Add the required bounded character annotation"
    assert direct.payload == %{kind: :char_literal_needs_bounded, value: 97}
  end

  test "legacy dependent-match failures are owned by the type family" do
    error = {:cannot_infer_dependent_match, :Cons}
    direct = TypeAdapter.from_error(error)

    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.title == "Dependent match result needs an annotation"
    assert direct.payload.kind == :cannot_infer_dependent_match
    assert direct.payload.branch == :Cons
  end

  test "ambiguous expected-type instances are owned by the type family" do
    error = {:ambiguous_instance_for_expected_type, :Eq, {:data, :Int, [], []}}
    direct = TypeAdapter.from_error(error)

    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.title == "Instance resolution is ambiguous"

    assert direct.payload == %{
             kind: :ambiguous_instance,
             interface: "Eq",
             expected_surface: "Int"
           }
  end

  test "legacy constructor and projection failures are owned by the type family" do
    for error <- [
          {:projection_not_a_record, :Int},
          {:bad_projection, %{field: :missing}},
          {:typed_pattern_type_error, :incompatible},
          {:unsolved_index, :VCons},
          {:unsolved_field_type, :VCons},
          {:unsolved_parameters, :VCons}
        ] do
      assert Adapter.from_error(error) == TypeAdapter.from_error(error)
      assert TypeAdapter.from_error(error).code == "E093"
      assert TypeAdapter.from_error(error).key == :type_mismatch
    end
  end

  test "legacy contextual failures expose their retained repair as a source-tagged hint" do
    source = "value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:legacy_type, source, "type_context.cure")
    {:ok, span} = SourceRegistry.span(registry, :legacy_type, 0, 5)

    diagnostic = Adapter.from_error(:not_a_function, span: span)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             """
             -- APPLICATION TARGET IS NOT CALLABLE [E093] ----------------- type_context.cure

             This value is used as a function, but its type is not callable.

             at type_context.cure:1:1
             1 | value
               | ^^^^^ apply a function or constructor value

             Hint: Apply a function or constructor value
             """
             |> String.trim_trailing()
  end

  test "raw kernel conversion failures normalize through the type family" do
    raw = {:conversion_failure, {:data, :Bool, [], []}, {:data, :Int, [], []}}
    assert TypeAdapter.from_error(raw) == Adapter.from_error(raw)

    contextual =
      {:source_context, raw,
       %{
         expectation_origin: :call_argument,
         checking: :consume,
         argument_index: 0,
         expression_category: :call
       }}

    direct = TypeAdapter.from_error(contextual)
    assert Adapter.from_error(contextual) == direct
    assert direct.code == "E093"
    assert direct.title == "Argument has the wrong type"
    assert direct.payload.origin.owner == :consume
    assert direct.payload.origin.index == 0

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      TypeAdapter.from_error({:unknown_global, :missing})
    end
  end

  test "lambda expectation failures are identical through the family and root adapter" do
    source = "fn (x) -> x end\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:lambda, source, "lambda.cure")
    {:ok, lambda_span} = SourceRegistry.span(registry, :lambda, 0, 15)
    {:ok, parameter_span} = SourceRegistry.span(registry, :lambda, 4, 5)

    error =
      {:lambda_expected_pi, %{expected: {:data, :Bool, [], []}, parameter_index: 0, parameter_span: parameter_span}}

    direct = TypeAdapter.from_error(error, span: lambda_span)
    assert Adapter.from_error(error, span: lambda_span) == direct
    assert direct.primary.span == lambda_span
    assert hd(direct.secondary).span == parameter_span

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "LAMBDA NEEDS A FUNCTION TYPE [E093]"
    assert rendered =~ "This lambda has parameter 1"
    assert rendered =~ "this parameter needs a function input type"
    assert rendered =~ "Hint: Pass this lambda to a function-valued parameter"
  end

  test "branch failures identify a singleton type outlier through the type family" do
    source = "A -> one\nB -> two\nC -> odd\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:branches, source, "branches.cure")
    {:ok, a_span} = SourceRegistry.span(registry, :branches, 0, 8)
    {:ok, b_span} = SourceRegistry.span(registry, :branches, 9, 17)
    {:ok, c_span} = SourceRegistry.span(registry, :branches, 18, 26)
    common = {:data, :Common, [], []}
    outlier = {:data, :Outlier, [], []}

    error =
      {:source_context,
       {:branch_type,
        %{
          branches: [
            %{constructor: :A, actual: common, expected: common, status: :ok},
            %{constructor: :B, actual: common, expected: common, status: :ok},
            %{constructor: :C, actual: outlier, expected: common, status: {:error, :branch_type}}
          ]
        }},
       %{
         checking: :choose,
         branch_patterns: [
           %{name: "A", span: a_span},
           %{name: "B", span: b_span},
           %{name: "C", span: c_span}
         ]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == c_span
    assert Enum.map(direct.secondary, & &1.span) == [a_span, b_span]
    assert direct.payload.failing_branch == :C

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "only the `C` branch has type `Outlier`"
    assert rendered =~ "possible outlier: this branch has the incompatible type"
    assert rendered =~ "compare this branch with the declared result"
  end

  test "operator failures preserve operator and operand regions through the type family" do
    source = "left + right\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:operator, source, "operator.cure")
    {:ok, left} = SourceRegistry.span(registry, :operator, 0, 4)
    {:ok, operator} = SourceRegistry.span(registry, :operator, 5, 6)
    {:ok, right} = SourceRegistry.span(registry, :operator, 7, 12)

    error =
      {:source_context, {:unsupported_operand_type, :+},
       %{
         operator_span: operator,
         operand_spans: [left, right],
         operand_types: [{:data, :Int, [], []}, {:data, :Bool, [], []}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == operator
    assert Enum.map(direct.secondary, & &1.span) == [left, right]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "The `+` operator does not accept `Int` on the left and `Bool` on the right"
    assert rendered =~ "the left operand has type `Int`"
    assert rendered =~ "the right operand has type `Bool`"
    assert rendered =~ "Hint: Change the operand types"
  end

  test "instance and overload resolution failures are owned by the type family" do
    source = "call(value)\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:resolution, source, "resolution.cure")
    {:ok, span} = SourceRegistry.span(registry, :resolution, 0, 11)

    errors = [
      {:source_context, {:no_instance, :Equatable, {:rigid, 0}},
       %{span: span, checking: :same, expectation_origin: :implicit}},
      {:no_matching_overload,
       %{
         name: :map,
         arguments: [:Int],
         candidates: [%{id: "List.map", owner: "List", parameters: [:List]}]
       }},
      {:ambiguous_overload, :map, ["List", "Sequence"]}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error, span: span)
      assert Adapter.from_error(error, span: span) == direct
      assert direct.code == "E093"
      assert direct.primary.span == span
      assert direct.suggestions != []
    end

    instance = errors |> hd() |> TypeAdapter.from_error(span: span)
    assert instance.payload.head_kind == :type_variable
    assert Renderer.plain(instance, registry, width: 80) =~ "Add a `where Equatable(...)` constraint"

    mismatch = errors |> Enum.at(1) |> TypeAdapter.from_error(span: span)
    assert Renderer.plain(mismatch, registry, width: 80) =~ "`List.map(List)`"

    ambiguity = errors |> Enum.at(2) |> TypeAdapter.from_error(span: span)

    assert Renderer.plain(ambiguity, registry, width: 80) =~
             "Hint: Choose `List.map(...)` or `Sequence.map(...)`"
  end

  test "non-callable applications label the value and stranded argument" do
    source = "value(argument)\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:application, source, "application.cure")
    {:ok, callee} = SourceRegistry.span(registry, :application, 0, 5)
    {:ok, argument} = SourceRegistry.span(registry, :application, 6, 14)

    error =
      {:source_context, {:applied_non_function, %{actual: {:data, :Int, [], []}, argument_index: 0}},
       %{callee_span: callee, argument_span: argument, callee_name: :value}}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == callee
    assert hd(direct.secondary).span == argument

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- `INT` VALUE IS NOT CALLABLE [E093] ------------------------- application.cure

             Parentheses apply a function or constructor, but this expression has type `Int`.
             It cannot accept the argument written after it.

             at application.cure:1:1
             1 | value(argument)
               | ^^^^^ -------- this expression has type `Int`, not a function type; this argument has nowhere to go

             Hint: Remove the parentheses, or replace this expression with a function or constructor
             """
             |> String.trim_trailing()
  end

  test "match inference labels every pattern that fails to identify a constructor" do
    source = "match value\n  _ -> value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:match, source, "match.cure")
    {:ok, whole} = SourceRegistry.span(registry, :match, 0, 25)
    {:ok, pattern} = SourceRegistry.span(registry, :match, 14, 15)

    error =
      {:cannot_infer_match_type,
       %{
         reason: :no_constructor_arm,
         span: whole,
         branch_spans: [pattern],
         expression_category: :pattern_match
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == whole
    assert hd(direct.secondary).span == pattern

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "MATCH RESULT NEEDS AN ANNOTATION [E093]"
    assert rendered =~ "this pattern does not identify a constructor"
    assert rendered =~ "Hint: Add a result annotation"
  end

  test "non-data match and with failures retain scrutinee and branch regions" do
    source = "with value\n  C -> body\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:non_data, source, "non_data.cure")
    {:ok, opener} = SourceRegistry.span(registry, :non_data, 0, 4)
    {:ok, scrutinee} = SourceRegistry.span(registry, :non_data, 5, 10)
    {:ok, branch} = SourceRegistry.span(registry, :non_data, 13, 22)
    {:ok, pattern} = SourceRegistry.span(registry, :non_data, 13, 14)

    errors = [
      {:source_context, :with_scrutinee_not_data,
       %{
         actual_type: {:float_type},
         opener_span: opener,
         scrutinee_span: scrutinee,
         with_arms: [%{span: branch}],
         with_form: :ordinary
       }},
      {:source_context, :match_scrutinee_not_data,
       %{
         actual_type: {:float_type},
         scrutinee_span: scrutinee,
         branch_patterns: [%{kind: :constructor, name: "C", pattern_span: pattern}]
       }}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    with_diagnostic = errors |> hd() |> TypeAdapter.from_error()
    assert with_diagnostic.primary.span == scrutinee
    assert Enum.map(with_diagnostic.secondary, & &1.span) == [opener, branch]

    match_diagnostic = errors |> Enum.at(1) |> TypeAdapter.from_error()
    assert match_diagnostic.primary.span == pattern
    assert hd(match_diagnostic.secondary).span == scrutinee

    rendered = Renderer.plain(match_diagnostic, registry, width: 80)
    assert rendered =~ "CONSTRUCTOR PATTERNS CANNOT MATCH FLOAT [E093]"
    assert rendered =~ "this expression has type `Float`"
    assert rendered =~ "Hint: Use a variable or wildcard"
  end

  test "mixed with branches single out a unique authored form" do
    source = "A -> a\nB -> b\nC | C -> c\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:mixed_with, source, "mixed_with.cure")
    {:ok, first} = SourceRegistry.span(registry, :mixed_with, 0, 6)
    {:ok, second} = SourceRegistry.span(registry, :mixed_with, 7, 13)
    {:ok, outlier} = SourceRegistry.span(registry, :mixed_with, 14, 24)

    error =
      {:source_context, :with_mixed_rematch_arms,
       %{
         with_arms: [
           %{style: :ordinary, span: first},
           %{style: :ordinary, span: second},
           %{style: :rematch, span: outlier}
         ]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == outlier
    assert Enum.map(direct.secondary, & &1.span) == [first, second]
    assert direct.payload.outlier_branch == 2

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "Possible outlier: only one branch uses the rematch"
    assert rendered =~ "possible outlier: this is the only rematch"
    assert rendered =~ "Hint: Make every branch use the same `with` form"
  end

  test "indexed with proof failures label the proof, scrutinee, and every branch" do
    source = "value proof pf\nA -> a\nB -> b\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:indexed_with, source, "indexed_with.cure")
    {:ok, scrutinee} = SourceRegistry.span(registry, :indexed_with, 0, 5)
    {:ok, proof} = SourceRegistry.span(registry, :indexed_with, 6, 14)
    {:ok, first} = SourceRegistry.span(registry, :indexed_with, 15, 21)
    {:ok, second} = SourceRegistry.span(registry, :indexed_with, 22, 28)

    error =
      {:source_context, {:with_indexed_scrutinee_unsupported, :"Main#Vector"},
       %{
         proof_name: "pf",
         proof_span: proof,
         scrutinee_span: scrutinee,
         branch_patterns: [%{span: first}, %{span: second}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == proof
    assert Enum.map(direct.secondary, & &1.span) == [scrutinee, first, second]
    assert direct.payload.family == "Vector"

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "INDEXED WITH CANNOT BIND A VALUE PROOF [E093]"
    assert rendered =~ "this value belongs to indexed family `Vector`"
    assert rendered =~ "this branch would need an indexed value equation"
    assert rendered =~ "Hint: Remove `proof pf`"
  end

  test "dependent match inference points to the responsible branch and enclosing match" do
    source = "match value\nCons(x) -> x\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:dependent_match, source, "dependent.cure")
    {:ok, match_span} = SourceRegistry.span(registry, :dependent_match, 0, 5)
    {:ok, branch_span} = SourceRegistry.span(registry, :dependent_match, 12, 24)

    error =
      {:source_context, {:cannot_infer_dependent_match, {:data, :Result, [], []}},
       %{
         opener_span: match_span,
         checking: :tail,
         branch_patterns: [%{name: "Cons", span: branch_span}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == branch_span
    assert hd(direct.secondary).span == match_span
    refute inspect(direct.payload) =~ "{:data"

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "DEPENDENT MATCH RESULT NEEDS AN ANNOTATION [E093]"
    assert rendered =~ "the `Cons` branch returns a type tied"
    assert rendered =~ "this match has no expected result type"
    assert rendered =~ "Hint: Add a result annotation to `tail`"
  end

  test "record update and projection failures preserve every authored role" do
    source = "Point{base | value: 1}\nbase.value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:records, source, "records.cure")
    {:ok, record_name} = SourceRegistry.span(registry, :records, 0, 5)
    {:ok, base} = SourceRegistry.span(registry, :records, 6, 10)
    {:ok, receiver} = SourceRegistry.span(registry, :records, 23, 27)
    {:ok, field} = SourceRegistry.span(registry, :records, 28, 33)

    update =
      {:source_context, {:record_update_base_mismatch, %{record: :"Main#Point", actual: :"Std.Int#Int"}},
       %{record_name_span: record_name, base_span: base}}

    projection =
      {:source_context, {:projection_not_a_record, :"Std.Int#Int"},
       %{field: "value", receiver_span: receiver, field_span: field}}

    for error <- [update, projection] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    assert TypeAdapter.from_error(update).primary.span == base
    assert hd(TypeAdapter.from_error(update).secondary).span == record_name
    assert TypeAdapter.from_error(projection).primary.span == receiver
    assert hd(TypeAdapter.from_error(projection).secondary).span == field
  end

  test "dependent projection labels the receiver, declaration, and prerequisite fields" do
    source = "flag value box.value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:dependent_record, source, "dependent_record.cure")
    {:ok, flag_decl} = SourceRegistry.span(registry, :dependent_record, 0, 4)
    {:ok, value_decl} = SourceRegistry.span(registry, :dependent_record, 5, 10)
    {:ok, receiver} = SourceRegistry.span(registry, :dependent_record, 11, 14)
    {:ok, field} = SourceRegistry.span(registry, :dependent_record, 15, 20)

    error =
      {:source_context, {:dependent_record_projection, :"Main#Box", "value"},
       %{
         field_span: field,
         receiver_span: receiver,
         dependent_fields: ["flag"],
         projected_field_declaration: %{type_span: value_decl},
         dependent_field_declarations: %{"flag" => %{type_span: flag_decl}}
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == field
    assert Enum.map(direct.secondary, & &1.span) == [receiver, value_decl, flag_decl]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "`VALUE` CANNOT BE PROJECTED WITHOUT ITS DEPENDENCY [E093]"
    assert rendered =~ "`flag` supplies part of `value`'s type"
    assert rendered =~ "Hint: Pattern-match `Box` and bind flag, value together"
  end

  test "typed and forced pattern failures retain annotation, binder, and constructor roles" do
    source = "Ctor(value: Bool) .index\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:patterns, source, "patterns.cure")
    {:ok, constructor} = SourceRegistry.span(registry, :patterns, 0, 17)
    {:ok, binder} = SourceRegistry.span(registry, :patterns, 5, 10)
    {:ok, annotation} = SourceRegistry.span(registry, :patterns, 12, 16)
    {:ok, forced} = SourceRegistry.span(registry, :patterns, 18, 24)

    typed =
      {:source_context, {:typed_pattern_type_mismatch, {:variable, [], "Bool"}},
       %{
         constructor: :"Main#Ctor",
         binder: "value",
         annotated_type: {:data, :Bool, [], []},
         field_type: {:data, :Int, [], []},
         annotation_span: annotation,
         binder_span: binder,
         constructor_pattern_span: constructor
       }}

    mismatch =
      {:source_context, {:forced_pattern_mismatch, {:ctor, :Wrong, []}, {:ctor, :Expected, []}},
       %{
         constructor: :"Main#Ctor",
         implicit_name: "index",
         forced_pattern_span: forced,
         named_implicit_span: forced,
         constructor_name_span: constructor
       }}

    for error <- [typed, mismatch] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    assert TypeAdapter.from_error(typed).primary.span == annotation
    assert Enum.map(TypeAdapter.from_error(typed).secondary, & &1.span) == [binder, constructor]
    assert TypeAdapter.from_error(mismatch).primary.span == forced

    rendered = Renderer.plain(TypeAdapter.from_error(typed), registry, width: 80)
    assert rendered =~ "`VALUE` IS ANNOTATED AS `BOOL`, BUT `CTOR` STORES `INT`"
    assert rendered =~ "Hint: Change the annotation to `Int`"
  end

  test "dependent sibling and telescope failures are owned by the type adapter" do
    source = "r c1 c2 with r t.9\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:dependent, source, "dependent.cure")
    {:ok, c1} = SourceRegistry.span(registry, :dependent, 2, 4)
    {:ok, c2} = SourceRegistry.span(registry, :dependent, 5, 7)
    {:ok, with_expression} = SourceRegistry.span(registry, :dependent, 8, 14)
    {:ok, scrutinee} = SourceRegistry.span(registry, :dependent, 13, 14)
    {:ok, receiver} = SourceRegistry.span(registry, :dependent, 15, 16)
    {:ok, index} = SourceRegistry.span(registry, :dependent, 17, 18)
    {:ok, projection} = SourceRegistry.span(registry, :dependent, 15, 18)

    sibling =
      {:source_context, {:with_sibling_dependency_unsupported, :sibling_references_sibling},
       %{
         dependent: "c2",
         dependency: "c1",
         checking: :handle,
         parameter_sites: [
           %{name: "c1", type_span: c1},
           %{name: "c2", type_span: c2}
         ],
         scrutinee_span: scrutinee,
         span: with_expression
       }}

    telescope =
      {:source_context, {:telescope_index_out_of_bounds, 9, 3},
       %{
         checking: :bad,
         projection_syntax: :dot,
         receiver_span: receiver,
         index_span: index,
         span: projection
       }}

    for error <- [sibling, telescope] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.secondary != []
      assert direct.suggestions != []
    end

    sibling_rendered = Renderer.plain(TypeAdapter.from_error(sibling), registry, width: 80)
    assert sibling_rendered =~ "WITH CANNOT REFINE DEPENDENT SIBLINGS"
    assert sibling_rendered =~ "Hint: Nest a second match after refining `c1`"

    telescope_rendered = Renderer.plain(TypeAdapter.from_error(telescope), registry, width: 80)
    assert telescope_rendered =~ "TUPLE POSITION 9 IS OUT OF RANGE"
    assert telescope_rendered =~ "Hint: Use a tuple position from 1 through 3"
  end

  test "annotation-boundary failures are owned by the type adapter" do
    source = "x h = value typealias Bad = 1\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:annotations, source, "annotations.cure")
    {:ok, parameter} = SourceRegistry.span(registry, :annotations, 0, 1)
    {:ok, binding} = SourceRegistry.span(registry, :annotations, 2, 3)
    {:ok, initializer} = SourceRegistry.span(registry, :annotations, 6, 11)
    {:ok, alias_name} = SourceRegistry.span(registry, :annotations, 22, 25)
    {:ok, alias_value} = SourceRegistry.span(registry, :annotations, 28, 29)

    errors = [
      {:untyped_parameter, %{name: "x", span: parameter}},
      {:let_needs_annotation, %{name: "h", name_span: binding, initializer_span: initializer, use_count: 2}},
      {:graded_let_needs_annotation, %{name: "h", grade: :linear, grade_span: binding, initializer_span: initializer}},
      {:typealias_not_a_type,
       %{
         name: :Bad,
         actual_type: {:data, :Int, [], []},
         name_span: alias_name,
         span: alias_value
       }}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.suggestions != []
    end

    alias_rendered = Renderer.plain(TypeAdapter.from_error(List.last(errors)), registry, width: 80)
    assert alias_rendered =~ "`BAD` ALIASES A VALUE, NOT A TYPE"
    assert alias_rendered =~ "Hint: If `Bad` should alias the value's type"

    for error <- [
          {:untyped_parameter, :x},
          {:let_needs_annotation, :h},
          {:graded_let_needs_annotation, :h},
          {:typealias_not_a_type, :Bad}
        ] do
      assert Adapter.from_error(error) == TypeAdapter.from_error(error)
    end
  end

  test "guard failures retain the pattern, condition, and repair site" do
    source = "0 when true -> value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:guard, source, "guard.cure")
    {:ok, pattern} = SourceRegistry.span(registry, :guard, 0, 1)
    {:ok, condition} = SourceRegistry.span(registry, :guard, 7, 11)
    {:ok, branch} = SourceRegistry.span(registry, :guard, 0, 20)

    refutable =
      {:source_context, {:unsupported_guard, %{reason: :refutable_pattern, shape: :literal, span: pattern}},
       %{checking: :run, branch_patterns: [%{pattern_span: pattern, guard_span: condition}]}}

    non_exhaustive =
      {:source_context, {:unsupported_guard, :non_exhaustive},
       %{checking: :run, branch_patterns: [%{span: branch, guard_span: condition}]}}

    complex =
      {:source_context, {:unsupported_guard, %{reason: :complex_scrutinee, span: pattern}},
       %{checking: :run, scrutinee_span: pattern}}

    for error <- [refutable, non_exhaustive, complex] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.suggestions != []
    end

    refutable_rendered = Renderer.plain(TypeAdapter.from_error(refutable), registry, width: 80)
    assert refutable_rendered =~ "LITERAL PATTERN CANNOT CARRY THIS GUARD"
    assert refutable_rendered =~ "Hint: Match this pattern first"

    gap = TypeAdapter.from_error(non_exhaustive)
    assert gap.primary.span.start_byte == branch.end_byte
    assert gap.primary.span.start_byte == gap.primary.span.end_byte
    assert hd(gap.secondary).span == condition
  end

  test "with rematch failures retain paired authored patterns" do
    source = "original restated | with_pattern\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:rematch, source, "rematch.cure")
    {:ok, original} = SourceRegistry.span(registry, :rematch, 0, 8)
    {:ok, restated} = SourceRegistry.span(registry, :rematch, 9, 17)
    {:ok, separator} = SourceRegistry.span(registry, :rematch, 18, 19)
    {:ok, with_pattern} = SourceRegistry.span(registry, :rematch, 20, 32)

    enriched =
      {:source_context, {:with_rematch_non_constructor_pattern, :binary_op},
       %{
         checking: :run,
         span: restated,
         original_pattern_spans: [original],
         restated_pattern_spans: [restated],
         original_pattern_count: 1,
         restated_pattern_count: 1,
         rematch_separator_span: separator,
         with_pattern_span: with_pattern
       }}

    bare =
      {:source_context, {:with_rematch_ctor_mismatch, :Some, :None}, %{checking: :run, span: restated}}

    for error <- [enriched, bare] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
    end

    direct = TypeAdapter.from_error(enriched)
    assert direct.primary.span == restated

    assert Enum.map(direct.secondary, & &1.span) == [
             original,
             separator,
             with_pattern
           ]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "REMATCH PATTERN MUST DESCRIBE A SHAPE"
    assert rendered =~ "Hint: Replace this expression with a variable or constructor pattern"
  end

  test "generated OTP family failures retain authored type origins" do
    source = "actor Bad\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:actor, source, "actor.cure")
    {:ok, invocation} = SourceRegistry.span(registry, :actor, 0, 9)

    details = %{
      module: "Cure.Generated.Bad",
      behaviour: :gen_server,
      source_provenance: %{macro: "actor"},
      expansion_provenance: []
    }

    cause =
      {:source_context, {:cannot_unify, :bool, :int},
       %{checking: :handle_cast, expression_category: :literal, span: invocation}}

    assert {:ok, direct} =
             TypeAdapter.from_family_error(cause, details, span: invocation)

    public =
      Adapter.from_error(
        {:lift_module_error, Map.put(details, :cause, cause)},
        span: invocation
      )

    assert public == direct
    assert direct.code == "E093"
    assert direct.payload.origin.kind == :actor
    assert direct.payload.origin.owner == "Cure.Generated.Bad"
    assert direct.primary.span == invocation
    assert [%{name: "actor", invocation: ^invocation}] = direct.provenance

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "ACTOR MESSAGE HAS THE WRONG TYPE"
    assert rendered =~ "this actor message has the wrong type"

    assert :error =
             TypeAdapter.from_family_error(
               cause,
               %{details | behaviour: :unknown},
               span: invocation
             )
  end

  test "bounded, constructor-family, and erased-effect boundaries are type-owned" do
    source = "5 Mk : Other {effect}\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:boundaries, source, "boundaries.cure")
    {:ok, literal} = SourceRegistry.span(registry, :boundaries, 0, 1)
    {:ok, constructor} = SourceRegistry.span(registry, :boundaries, 2, 4)
    {:ok, result} = SourceRegistry.span(registry, :boundaries, 7, 12)
    {:ok, opener} = SourceRegistry.span(registry, :boundaries, 13, 14)
    {:ok, effect} = SourceRegistry.span(registry, :boundaries, 14, 20)
    {:ok, closer} = SourceRegistry.span(registry, :boundaries, 20, 21)

    errors = [
      {:source_context, {:bounded_lit_out_of_range, 5, 3}, %{span: literal}},
      {:source_context, {:result_type_not_family, :Vec},
       %{
         expected_family: :Vec,
         observed_family: :Other,
         constructor: :Mk,
         constructor_name_span: constructor,
         result_span: result,
         parameter_count: 1,
         index_count: 1
       }},
      {:source_context, {:effect_binder_erased, %{def: :run, binder: 0}},
       %{
         binder_name: "effect",
         binder_span: effect,
         span: effect,
         opener_span: opener,
         closer_span: closer
       }}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.suggestions != []
    end

    effect_diagnostic = TypeAdapter.from_error(List.last(errors))

    assert [%{applicability: :machine_applicable, edits: [_, _]}] =
             effect_diagnostic.suggestions

    rendered = Renderer.plain(effect_diagnostic, registry, width: 80)
    assert rendered =~ "EFFECT PARAMETER CANNOT BE ERASED"
    assert rendered =~ "Hint: Make `effect` a present parameter"
  end

  test "FFI union failures retain the return type and declaration boundary" do
    source = "extern raw() -> Int | Nat\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:ffi, source, "ffi.cure")
    {:ok, declaration} = SourceRegistry.span(registry, :ffi, 0, 10)
    {:ok, return_type} = SourceRegistry.span(registry, :ffi, 16, 25)

    error =
      {:source_context,
       {:extern_union_indistinct, :raw, {:same_runtime_shape, [{"Std.Int#Int", "Std.Nat#Nat", :integer}]}},
       %{
         extern_span: declaration,
         return_span: return_type,
         union_members: ["Std.Int#Int", "Std.Nat#Nat"]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E093"
    assert direct.primary.span == return_type
    assert hd(direct.secondary).span == declaration
    assert direct.payload.conflict.kind == :same_runtime_shape
    assert direct.suggestions != []

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "EXTERN `RAW` RETURNS AN INDISTINGUISHABLE UNION"
    assert rendered =~ "`Int` and `Nat` both arrive as BEAM integer values"
    assert rendered =~ "Hint: Return a tagged record or data type"

    bare = {:extern_returns_union, :raw, {:union, []}}
    assert Adapter.from_error(bare) == TypeAdapter.from_error(bare)
  end

  test "rewrite failures retain proof, body, and expected-type roles" do
    source = "rewrite proof in body\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:rewrite, source, "rewrite.cure")
    {:ok, expression} = SourceRegistry.span(registry, :rewrite, 0, 21)
    {:ok, proof} = SourceRegistry.span(registry, :rewrite, 8, 13)
    {:ok, body} = SourceRegistry.span(registry, :rewrite, 17, 21)

    errors = [
      {:source_context, :rewrite_requires_expected_type,
       %{span: expression, proof_span: proof, body_span: body, checking: :run}},
      {:source_context, :rewrite_proof_not_equality,
       %{span: expression, proof_span: proof, body_span: body, checking: :run}},
      {:source_context, {:rewrite_no_match, :left, :right, :goal},
       %{span: expression, proof_span: proof, body_span: body, checking: :run}}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.secondary != []
      assert direct.suggestions != []
    end

    proof_error = TypeAdapter.from_error(Enum.at(errors, 1))
    assert proof_error.primary.span == proof
    assert hd(proof_error.secondary).span == body

    rendered = Renderer.plain(proof_error, registry, width: 80)
    assert rendered =~ "REWRITE PROOF IS NOT AN EQUALITY"
    assert rendered =~ "Hint: Pass an `Equivalent` proof after `rewrite`"

    for error <- [
          :rewrite_requires_expected_type,
          :rewrite_proof_not_equality,
          {:rewrite_no_match, :left, :right},
          {:rewrite_no_match, :left, :right, :goal}
        ] do
      assert Adapter.from_error(error) == TypeAdapter.from_error(error)
    end
  end
end
