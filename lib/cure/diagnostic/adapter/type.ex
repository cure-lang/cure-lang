defmodule Cure.Diagnostic.Adapter.Type do
  @moduledoc """
  Converts canonical contextual type failures into E093 diagnostics.

  This module owns the user-facing expected/found comparison. Core remains
  available only in an explicitly requested debug payload.
  """

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    ExpectationOrigin,
    Label,
    ProvenanceFrame,
    Span,
    Suggestion,
    TextEdit,
    TypeProblem
  }

  # The six literal protocols, each with the spelling a reader would use for the
  # literal that selects it. `elaborate_literal_protocol/7` reports a missing
  # implementation for exactly these; nothing else routes through them.
  @literal_spellings %{
    ExpressibleByNaturalLiteral: "a natural-number literal",
    ExpressibleByIntegerLiteral: "an integer literal",
    ExpressibleByDecimalLiteral: "a decimal literal",
    ExpressibleByStringLiteral: "a string literal",
    ExpressibleByCharacterLiteral: "a character literal",
    ExpressibleByAtomLiteral: "an atom literal"
  }

  @doc false
  def empty_type_failure(opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Type mismatch",
      body: Doc.paragraph("The type checker reported an unsatisfied constraint without further detail."),
      primary: primary_label(opts, "this expression does not satisfy its type constraints"),
      payload: %{errors: []}
    )
  end

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}
      nil -> nil
    end
  end

  @spec from_family_error(term(), map(), keyword()) :: {:ok, Diagnostic.t()} | :error
  def from_family_error(cause, details, opts \\ [])

  def from_family_error({:source_context, reason, context}, details, opts)
      when is_map(context) do
    with origin when not is_nil(origin) <- family_origin(details) do
      context =
        context
        |> Map.put(:expectation_origin, origin)
        |> Map.put(:checking, Map.get(details, :module))

      case reason do
        {:index_mismatch, {:cannot_unify, actual, expected}} ->
          {:ok,
           family_type_problem(
             :index_mismatch,
             actual,
             expected,
             origin,
             context,
             details,
             opts
           )}

        {:cannot_unify, actual, expected} ->
          {:ok,
           family_type_problem(
             :cannot_unify,
             actual,
             expected,
             origin,
             context,
             details,
             opts
           )}

        {:conversion_failure, actual, expected} ->
          {:ok,
           family_type_problem(
             :conversion_failure,
             actual,
             expected,
             origin,
             context,
             details,
             opts
           )}

        reason when is_tuple(reason) ->
          if family_boundary_reason?(reason) do
            {:ok, family_boundary_failure(origin, details, reason, opts)}
          else
            :error
          end

        _ ->
          :error
      end
    else
      _ -> :error
    end
  end

  def from_family_error(_cause, _details, _opts), do: :error

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:type_mismatch, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Type mismatch",
      body: Doc.paragraph(message),
      primary: primary(opts, "this expression has the wrong type"),
      payload: %{message: message, meta: meta}
    )
  end

  def from_error(%TypeProblem{} = problem, opts) do
    actual_surface = surface_type(problem.actual)
    expected_surface = surface_type(problem.expected)
    primary_span = problem.span || Keyword.get(opts, :span)

    primary =
      if primary_span do
        %Label{span: primary_span, style: :primary, message: label(problem.origin)}
      end

    payload =
      %{
        expected_surface: expected_surface,
        actual_surface: actual_surface,
        origin: Map.from_struct(problem.origin),
        expression_category: problem.expression
      }
      |> maybe_put_dependent_mismatch(problem.debug)
      |> maybe_put_debug(problem.expected, problem.actual, problem.debug, opts)

    body =
      [
        Doc.paragraph(context(problem.origin)),
        comparison_doc(problem.expected, problem.actual)
      ]
      |> append_dependent_mismatch(problem.debug)

    Diagnostic.new(
      code: "E093",
      key: problem.kind,
      severity: :error,
      title: title(problem.origin),
      body: Doc.stack(body),
      primary: primary,
      secondary: expectation_labels(problem.origin, primary_span, problem.related),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  def from_error({:conversion_failure, actual, expected}, opts) do
    payload =
      %{
        expected_surface: surface_type(expected),
        actual_surface: surface_type(actual)
      }
      |> maybe_put_debug(expected, actual, %{}, opts)

    Diagnostic.new(
      code: "E093",
      key: :conversion_failure,
      severity: :error,
      title: "Type mismatch",
      body: comparison_doc(expected, actual),
      primary: primary(opts, "this expression has the wrong type"),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  def from_error(
        {:source_context, {:conversion_failure, actual, expected} = reason, context},
        opts
      )
      when is_map(context) do
    case Map.get(context, :expectation_origin) do
      nil ->
        raise Cure.Diagnostic.UnhandledError,
          error: {:source_context, reason, context}

      origin ->
        from_error(
          %TypeProblem{
            kind: :conversion_failure,
            actual: actual,
            expected: expected,
            origin: %ExpectationOrigin{
              kind: origin,
              span: Map.get(context, :expectation_span),
              owner: Map.get(context, :checking),
              index: Map.get(context, :argument_index)
            },
            expression: Map.get(context, :expression_category, :expression),
            span: Keyword.get(opts, :span, Map.get(context, :span)),
            debug: %{cause: reason, checking: Map.get(context, :checking)}
          },
          opts
        )
    end
  end

  def from_error({:lambda_expected_pi, %{expected: expected} = details}, opts) do
    expected_surface = surface_type(expected)
    parameter_index = Map.get(details, :parameter_index, 0)

    secondary =
      case Map.get(details, :parameter_span) do
        %Span{} = span ->
          [%Label{span: span, style: :secondary, message: "this parameter needs a function input type"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Lambda needs a function type",
      body:
        Doc.paragraph(
          "This lambda has parameter #{parameter_index + 1}, but its surrounding context expects `#{expected_surface}` at that point. An untyped lambda parameter can only be checked when the expected type provides a corresponding function input."
        ),
      primary: primary(opts, "this lambda is used where a non-function value is required"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Pass this lambda to a function-valued parameter, or replace it with a `#{expected_surface}` value",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :lambda_expected_pi,
        expected_surface: expected_surface,
        parameter_index: parameter_index
      }
    )
  end

  def from_error({:lambda_expected_pi, expected}, opts),
    do: from_error({:lambda_expected_pi, %{expected: expected, parameter_index: 0}}, opts)

  def from_error(
        {:source_context, {:named_implicit_unforced, name}, %{named_implicit_status: :unforced} = context},
        opts
      ),
      do: named_implicit_unforced_failure(name, context, opts)

  def from_error({:source_context, {:named_implicit_unforced, name}, context}, opts) when is_map(context),
    do: named_implicit_unforced_failure(name, context, opts)

  def from_error({:source_context, {:unsolved_metavariables, name}, context}, opts) when is_map(context) do
    cond do
      Map.get(context, :constructor_result_mismatch) ->
        checked_constructor_result_failure(name, context, opts)

      Map.get(context, :expectation_origin) == :constructor_argument ->
        nested_constructor_implicit_failure(name, context, opts)

      true ->
        unsolved_metavariable_failure(name, context, opts)
    end
  end

  def from_error({:effect_arity, name, expected, actual}, opts),
    do:
      contextual_failure(
        :effect_arity,
        %{name: name, expected: expected, actual: actual},
        opts,
        {"Effect operation arity mismatch", "This effect operation was given the wrong number of arguments.",
         "provide the arguments required by the effect operation"}
      )

  def from_error({:char_literal_needs_bounded, value}, opts),
    do: character_literal_failure(:char_literal_needs_bounded, value, opts)

  def from_error({:char_literal_out_of_range, value}, opts),
    do: character_literal_failure(:char_literal_out_of_range, value, opts)

  def from_error(:branch_type, opts), do: branch_failure(%{}, opts)

  def from_error({:source_context, :branch_type, context}, opts) when is_map(context),
    do: branch_failure(context, opts)

  def from_error({:source_context, {:branch_type, details}, context}, opts) when is_map(context),
    do: branch_failure(Map.put(context, :branch_details, details), opts)

  def from_error({:source_context, {:branch_type, constructor, reason}, context}, opts)
      when is_map(context) do
    detail =
      case reason do
        {:conversion_failure, actual, expected} ->
          %{constructor: constructor, status: {:error, reason}, actual: actual, expected: expected}

        _ ->
          %{constructor: constructor, status: {:error, reason}, actual: nil, expected: nil}
      end

    branch_failure(Map.put(context, :branch_details, %{branches: [detail]}), opts)
  end

  def from_error({kind, operator}, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning],
      do: operator_failure(kind, operator, %{}, opts)

  def from_error({:source_context, {kind, operator}, context}, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning] and is_map(context),
      do: operator_failure(kind, operator, context, opts)

  def from_error({:no_instance, interface, head}, opts),
    do: instance_failure(interface, head, %{}, opts)

  def from_error({:ambiguous_instance_for_expected_type, interface, expected}, opts),
    do: ambiguous_instance_failure(interface, expected, opts)

  def from_error({:union_member_not_ground, member}, opts),
    do: union_declaration_failure(:union_member_not_ground, %{member: member}, opts)

  def from_error({:unsupported_member_shape, members}, opts),
    do: union_declaration_failure(:unsupported_member_shape, %{members: members}, opts)

  def from_error({:same_runtime_shape, members}, opts),
    do: union_declaration_failure(:same_runtime_shape, %{members: members}, opts)

  def from_error({:same_erased_literal, members}, opts),
    do: union_declaration_failure(:same_erased_literal, %{members: members}, opts)

  # A literal is written, not built: it takes its value from whichever literal
  # protocol the EXPECTED type implements. So `1.0` where `Int` is expected is
  # not an implementation the author forgot to write — it is the ordinary
  # mismatch between what they wrote and what the surrounding context demands,
  # and it belongs in that context's own words ("Annotation does not match",
  # "Local fact does not match") with the annotation labelled as the source of
  # the expectation. The protocol is the reason, not the headline. Away from a
  # literal — a `requires` that cannot be discharged, say — the same interface
  # really is a missing implementation, so that case still falls through.
  def from_error({:source_context, {:no_instance, interface, expected}, context}, opts)
      when is_map(context) and is_map_key(@literal_spellings, interface) do
    case {Map.get(context, :expectation_origin), Map.get(context, :expression_category)} do
      {nil, _category} ->
        instance_failure(interface, expected, context, Keyword.put_new(opts, :span, Map.get(context, :span)))

      {origin, :literal} ->
        literal_protocol_mismatch(origin, interface, expected, context, opts)

      {_origin, _category} ->
        instance_failure(interface, expected, context, Keyword.put_new(opts, :span, Map.get(context, :span)))
    end
  end

  def from_error({:source_context, {:no_instance, interface, head}, context}, opts)
      when is_map(context),
      do: instance_failure(interface, head, context, Keyword.put_new(opts, :span, Map.get(context, :span)))

  def from_error({:constraint_head_not_determined, details}, opts) when is_map(details),
    do: undetermined_constraint_head(details, %{}, opts)

  def from_error({:source_context, {:constraint_head_not_determined, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: undetermined_constraint_head(details, context, Keyword.put_new(opts, :span, Map.get(context, :span)))

  def from_error({:no_matching_overload, name, arguments}, opts),
    do: overload_mismatch(%{name: name, arguments: arguments, candidates: []}, opts)

  def from_error({:no_matching_overload, %{name: _name} = details}, opts),
    do: overload_mismatch(details, opts)

  def from_error({:ambiguous_overload, name, owners}, opts),
    do: overload_ambiguity(name, owners, opts)

  def from_error({:applied_non_function, details}, opts) when is_map(details),
    do: non_callable(details, %{}, opts)

  def from_error({:source_context, {:applied_non_function, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: non_callable(details, context, opts)

  def from_error({:cannot_infer_match_type, %{reason: reason} = details}, opts)
      when reason in [:no_constructor_arm, :scrutinee_not_data],
      do: match_inference(reason, details, opts)

  def from_error({:cannot_infer_match_type, _legacy_expression}, opts),
    do: match_inference(:unknown, %{}, opts)

  def from_error({:source_context, :with_scrutinee_not_data, context}, opts)
      when is_map(context),
      do: non_data_with(context, opts)

  def from_error({:source_context, :match_scrutinee_not_data, context}, opts)
      when is_map(context),
      do: non_data_match(context, opts)

  def from_error({:source_context, :with_mixed_rematch_arms, context}, opts)
      when is_map(context),
      do: mixed_with_arms(context, opts)

  def from_error(
        {:source_context, {:with_indexed_scrutinee_unsupported, family}, context},
        opts
      )
      when is_map(context),
      do: indexed_with_proof(family, context, opts)

  def from_error(
        {:source_context, {:cannot_infer_dependent_match, _inferred_type}, context},
        opts
      )
      when is_map(context),
      do: dependent_match_inference(context, opts)

  def from_error({:cannot_infer_dependent_match, branch}, opts),
    do: dependent_match_inference(%{branch_patterns: [%{name: branch}]}, opts)

  def from_error({:source_context, {:record_update_base_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: record_update_base(details, context, opts)

  def from_error({:source_context, {:projection_not_a_record, record}, context}, opts)
      when is_map(context),
      do: projection_receiver(record, context, opts)

  def from_error({:projection_not_a_record, record}, opts),
    do: legacy_contextual_failure(:projection_not_a_record, %{record: record}, opts)

  def from_error({:bad_projection, details}, opts),
    do: legacy_contextual_failure(:bad_projection, %{details: details}, opts)

  def from_error({:source_context, {:projection_non_record, field}, context}, opts)
      when is_map(context),
      do: projection_receiver(nil, Map.put_new(context, :field, field), opts)

  def from_error({:source_context, {:dependent_record_projection, record, field}, context}, opts)
      when is_map(context),
      do: dependent_projection(record, field, context, opts)

  def from_error({:typed_pattern_type_mismatch, type_ast}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Pattern annotation does not match",
      body: Doc.paragraph("This pattern's annotation is incompatible with the value it matches."),
      primary: primary(opts, "change the pattern or its type annotation"),
      payload: %{kind: :typed_pattern, annotation: pattern_annotation(type_ast)}
    )
  end

  def from_error({:typed_pattern_type_error, reason}, opts),
    do: legacy_contextual_failure(:typed_pattern_type_error, %{reason: reason}, opts)

  def from_error({:unsolved_index, constructor}, opts),
    do: legacy_contextual_failure(:unsolved_index, %{constructor: constructor}, opts)

  def from_error({:unsolved_field_type, constructor}, opts),
    do: legacy_contextual_failure(:unsolved_field_type, %{constructor: constructor}, opts)

  def from_error({:unsolved_parameters, constructor}, opts),
    do: legacy_contextual_failure(:unsolved_parameters, %{constructor: constructor}, opts)

  def from_error(
        {:source_context, {:typed_pattern_type_mismatch, _type_ast}, %{field_type: field_type} = context},
        opts
      )
      when not is_nil(field_type),
      do: typed_pattern_annotation(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_not_in_pattern, _meta},
         %{forced_pattern_position: :positional_constructor_argument} = context},
        opts
      ),
      do: positional_forced_pattern(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_mismatch, actual, expected}, %{forced_pattern_span: _} = context},
        opts
      ),
      do: forced_pattern_mismatch(actual, expected, context, opts)

  def from_error({:source_context, {:forced_pattern_mismatch, actual, expected}, context}, opts)
      when is_map(context) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Forced pattern does not match",
      body: Doc.paragraph("This forced pattern does not match the value's expected type."),
      primary:
        primary(Keyword.put_new(opts, :span, Map.get(context, :span)), "change the forced pattern or its expected type"),
      payload: %{kind: :forced_pattern_mismatch, actual: actual, expected: expected}
    )
  end

  def from_error(
        {:source_context, {:telescope_index_out_of_bounds, index, arity}, context},
        opts
      )
      when is_integer(index) and is_integer(arity) and is_map(context),
      do: telescope_index_failure(index, arity, context, opts)

  def from_error(
        {:source_context, {:with_sibling_dependency_unsupported, reason}, context},
        opts
      )
      when reason in [:sibling_references_sibling, :kept_references_sibling] and
             is_map(context) do
    case context do
      %{dependent: dependent} ->
        with_sibling_dependency_failure(
          %{
            reason: reason,
            dependent: dependent,
            dependency: Map.get(context, :dependency)
          },
          context,
          opts
        )

      _ ->
        contextual_type_failure(:with_sibling_dependency_unsupported, %{detail: reason}, opts)
    end
  end

  def from_error({:untyped_parameter, %{name: _name} = details}, opts),
    do: untyped_parameter_failure(details, opts)

  def from_error({:graded_let_needs_annotation, %{name: _name} = details}, opts),
    do: local_binding_annotation_failure(:graded, details, opts)

  def from_error({:let_needs_annotation, %{name: _name} = details}, opts),
    do: local_binding_annotation_failure(:ungraded, details, opts)

  def from_error({:typealias_not_a_type, %{name: _name, actual_type: _actual} = details}, opts),
    do: typealias_value_failure(details, opts)

  def from_error({:typealias_not_a_type, alias_name, actual_type}, opts),
    do: typealias_value_failure(%{name: alias_name, actual_type: actual_type}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :untyped_parameter,
             :let_needs_annotation,
             :graded_let_needs_annotation,
             :typealias_not_a_type
           ],
      do: generic_annotation_failure(kind, detail, opts)

  def from_error({:source_context, {:unsupported_guard, :non_exhaustive}, context}, opts)
      when is_map(context),
      do: non_exhaustive_guard_failure(context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :refutable_pattern} = details}, context},
        opts
      )
      when is_map(context),
      do: refutable_guard_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :complex_scrutinee} = details}, context},
        opts
      )
      when is_map(context),
      do: complex_guard_scrutinee_failure(details, context, opts)

  def from_error({:source_context, {kind, first, second}, context}, opts)
      when kind == :with_rematch_ctor_mismatch and is_map(context) do
    if rematch_context_enriched?(context) do
      rematch_pattern_failure(
        kind,
        %{original: first, restated: second},
        context,
        opts
      )
    else
      rematch_pattern_problem(kind, %{actual: first, expected: second}, context, opts)
    end
  end

  def from_error({:source_context, {kind, details}, context}, opts)
      when kind in [
             :with_rematch_ctor_mismatch,
             :with_rematch_non_constructor_pattern,
             :with_rematch_inconsistent_binding,
             :with_rematch_unsupported_parent_pattern
           ] and is_map(context) do
    if rematch_context_enriched?(context) do
      rematch_pattern_failure(kind, %{details: details}, context, opts)
    else
      if kind == :with_rematch_unsupported_parent_pattern do
        generic_rematch_parent_failure(details, opts)
      else
        rematch_pattern_problem(kind, %{details: details}, context, opts)
      end
    end
  end

  def from_error(
        {:source_context, {:with_rematch_arity_mismatch, expected, actual}, context},
        opts
      )
      when is_map(context),
      do:
        rematch_pattern_failure(
          :with_rematch_arity_mismatch,
          %{expected: expected, actual: actual},
          context,
          opts
        )

  def from_error(
        {:source_context, {:bounded_lit_out_of_range, value, bound}, context},
        opts
      )
      when is_map(context),
      do: bounded_literal_failure(value, bound, context, opts)

  def from_error({:bounded_lit_out_of_range, value, bound}, opts),
    do: bounded_literal_failure(value, bound, %{}, opts)

  def from_error(
        {:source_context, {:result_type_not_family, family}, context},
        opts
      )
      when is_map(context),
      do: constructor_result_family_failure(family, context, opts)

  def from_error({:result_type_not_family, detail}, opts),
    do: generic_result_family_failure(detail, opts)

  def from_error(
        {:source_context, {:effect_binder_erased, details}, context},
        opts
      )
      when is_map(details) and is_map(context),
      do: erased_effect_binder_failure(details, context, opts)

  def from_error({:effect_binder_erased, details}, opts) when is_map(details),
    do: erased_effect_binder_failure(details, %{}, opts)

  def from_error(
        {:source_context, {:extern_returns_union, name, codomain}, context},
        opts
      )
      when is_map(context),
      do: extern_union_failure(:nested, name, codomain, context, opts)

  def from_error(
        {:source_context, {:extern_union_indistinct, name, reason}, context},
        opts
      )
      when is_map(context),
      do: extern_union_failure(:indistinct, name, reason, context, opts)

  def from_error({:extern_returns_union, name, codomain}, opts),
    do:
      generic_ffi_failure(
        :extern_returns_union,
        %{name: name, codomain: codomain},
        opts
      )

  def from_error({:extern_union_indistinct, name, reason}, opts),
    do:
      generic_ffi_failure(
        :extern_union_indistinct,
        %{name: name, reason: reason},
        opts
      )

  def from_error({:source_context, kind, context}, opts)
      when kind in [
             :rewrite_requires_expected_type,
             :rewrite_proof_not_equality
           ] and is_map(context),
      do: rewrite_failure(kind, context, opts)

  def from_error(
        {:source_context, {:rewrite_no_match, _left, _right}, context},
        opts
      )
      when is_map(context),
      do: rewrite_failure(:rewrite_no_match, context, opts)

  def from_error(
        {:source_context, {:rewrite_no_match, _left, _right, _goal}, context},
        opts
      )
      when is_map(context),
      do: rewrite_failure(:rewrite_no_match, context, opts)

  def from_error(kind, opts)
      when kind in [
             :rewrite_requires_expected_type,
             :rewrite_proof_not_equality
           ],
      do: generic_rewrite_failure(kind, %{}, opts)

  def from_error({:rewrite_no_match, left, right}, opts),
    do:
      generic_rewrite_failure(
        :rewrite_no_match,
        %{first: left, second: right},
        opts
      )

  def from_error({:rewrite_no_match, left, right, goal}, opts),
    do:
      generic_rewrite_failure(
        :rewrite_no_match,
        %{first: left, second: right, goal: goal},
        opts
      )

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp typed_pattern_annotation(context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    binder = name(Map.get(context, :binder, "field"))
    annotated = pattern_type(Map.get(context, :annotated_type))
    field_type = pattern_type(Map.get(context, :field_type))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :annotation_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :binder_span) || Map.get(context, :typed_pattern_span),
          primary_span,
          "`#{binder}` is the field being annotated"
        ),
        related_label(
          Map.get(context, :constructor_pattern_span) || Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` provides this field as `#{field_type}`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{binder}` is annotated as `#{annotated}`, but `#{constructor}` stores `#{field_type}`",
      body:
        Doc.paragraph(
          "Visible field #{argument_index + 1} of `#{constructor}` has type `#{field_type}`. This pattern annotates `#{binder}` as `#{annotated}`, so the annotation cannot describe the value selected by the constructor."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this says `#{annotated}`, but the constructor field is `#{field_type}`"
          }
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Change the annotation to `#{field_type}`, or remove it and let `#{constructor}` determine the field type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :typed_pattern_type_mismatch,
        constructor: constructor,
        binder: binder,
        argument_index: argument_index,
        annotated: annotated,
        field_type: field_type,
        checking: Map.get(context, :checking, :pattern)
      }
    )
  end

  defp positional_forced_pattern(context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :constructor_span) do
        %Span{} = span when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this constructor pattern supplies positional fields"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Dot pattern must name an implicit field",
      body:
        Doc.paragraph(
          "Field #{argument_index + 1} of `#{constructor}` is positional. A dot pattern checks a value that constructor-index refinement already determined, so it must be written inside a named implicit pattern such as `{index = .value}`."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{span: primary_span, style: :primary, message: "this forced check is in a positional field"}
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Bind this positional field normally, or move the dot check to the constructor's corresponding named implicit field",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :positional_forced_pattern,
        constructor: constructor,
        argument_index: argument_index,
        expectation_origin: :pattern
      }
    )
  end

  defp forced_pattern_mismatch(actual, expected, context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    implicit_name = name(Map.get(context, :implicit_name, "index"))
    actual_surface = Map.get(context, :written_surface) || pattern_type(actual)
    expected_surface = Map.get(context, :expected_surface) || pattern_type(expected)
    primary_span = Map.get(context, :forced_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :named_implicit_span),
          primary_span,
          "this check targets the hidden `#{implicit_name}` field"
        ),
        related_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` fixes the value of `#{implicit_name}` from the matched index"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Forced `#{implicit_name}` does not match `#{constructor}`",
      body:
        Doc.paragraph(
          "The dot expression denotes `#{actual_surface}`, but matching `#{constructor}` fixes `#{implicit_name}` as `#{expected_surface}`. A forced pattern checks an index already determined by the scrutinee; it cannot choose a different value."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this forced value disagrees with the index fixed here"
          }
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Change the dot expression to the value fixed by `#{constructor}`, or bind `#{implicit_name}` without a dot when it is not forced",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :forced_pattern_mismatch,
        constructor: constructor,
        implicit_name: implicit_name,
        actual: actual_surface,
        expected: expected_surface,
        expectation_origin: :pattern
      }
    )
  end

  defp pattern_type({:data, family, parameters, indices}) do
    arguments = Enum.map(parameters ++ indices, &pattern_type/1)
    application(short_name(family), arguments)
  end

  defp pattern_type({:ctor, constructor, arguments}),
    do: application(short_name(constructor), Enum.map(arguments, &pattern_type/1))

  defp pattern_type({:global, global}), do: short_name(global)
  defp pattern_type({:meta, _id}), do: "?"
  defp pattern_type(other), do: surface_type(other)

  defp application(head, []), do: head
  defp application(head, arguments), do: "#{head}(#{Enum.join(arguments, ", ")})"

  defp pattern_annotation({:variable, _meta, variable}), do: name(variable)
  defp pattern_annotation(type), do: surface_type(type)

  defp with_sibling_dependency_failure(details, context, opts) do
    dependent = name(Map.get(details, :dependent))
    dependency = name(Map.get(details, :dependency))
    reason = Map.get(details, :reason)
    dependent_site = parameter_site(context, dependent)
    dependency_site = parameter_site(context, dependency)
    expression_span = Map.get(context, :span) || Keyword.get(opts, :span)
    scrutinee_span = Map.get(context, :scrutinee_span)

    {body, primary_message, dependency_message, hint} =
      case reason do
        :sibling_references_sibling ->
          {
            "`#{dependent}` must be refined when this `with` chooses a constructor, but its type also depends on `#{dependency}`, which must be refined by the same match. Cure cannot currently generalize one refined sibling over another without changing their dependency order.",
            "the type of `#{dependent}` depends on another value refined by this `with`",
            "`#{dependency}` must also be refined by this match",
            "Nest a second match after refining `#{dependency}`, or change `#{dependent}` so its type does not depend on `#{dependency}`"
          }

        :kept_references_sibling ->
          {
            "`#{dependent}` is not itself refined by this `with`, but its type depends on `#{dependency}`, which is. Keeping `#{dependent}` while changing the type of `#{dependency}` would leave the context ill-formed.",
            "this parameter would keep a type tied to a refined sibling",
            "`#{dependency}` changes type across these branches",
            "Move `#{dependent}` inside the refined branch, or change its type so it does not depend on `#{dependency}`"
          }
      end

    primary_span = parameter_site_span(dependent_site) || expression_span

    secondary =
      [
        related_label(parameter_site_span(dependency_site), primary_span, dependency_message),
        related_label(
          scrutinee_span,
          primary_span,
          "this is the value whose constructor would refine those sibling types"
        ),
        related_label(
          expression_span,
          primary_span,
          "this `with` requires the unsupported dependent refinement"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With cannot refine dependent siblings in this order",
      body: Doc.paragraph(body),
      primary: label_at(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :with_sibling_dependency_unsupported,
        reason: reason,
        checking: Map.get(context, :checking),
        dependent: dependent,
        dependency: dependency
      }
    )
  end

  defp telescope_index_failure(index, arity, context, opts) do
    syntax = Map.get(context, :projection_syntax, :dot)

    primary_span =
      Map.get(context, :index_span) || Map.get(context, :field_span) || Map.get(context, :span) ||
        Keyword.get(opts, :span)

    receiver_span = Map.get(context, :receiver_span)
    expression_span = Map.get(context, :span)
    position_word = if arity == 1, do: "position", else: "positions"

    body =
      "This tuple has #{arity} #{position_word}, numbered from 1 through #{arity}, but this projection asks for position #{index}. Tuple projection is checked at compile time, so an out-of-range position can never produce a value."

    primary_message =
      case syntax do
        :element -> "index #{index} is outside this #{arity}-element tuple"
        _ -> "position .#{index} does not exist on this #{arity}-element tuple"
      end

    secondary =
      [
        related_label(
          receiver_span,
          primary_span,
          "this expression has a tuple type with #{arity} #{position_word}"
        ),
        related_label(
          expression_span,
          primary_span,
          "this complete projection cannot succeed"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Tuple position #{index} is out of range",
      body: Doc.paragraph(body),
      primary: label_at(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use a tuple position from 1 through #{arity}",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :telescope_index_out_of_bounds,
        index: index,
        arity: arity,
        syntax: syntax,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp parameter_site(context, parameter_name) do
    context
    |> Map.get(:parameter_sites, [])
    |> Enum.find(&(name(Map.get(&1, :name)) == parameter_name))
  end

  defp parameter_site_span(%{type_span: %Span{} = span}), do: span
  defp parameter_site_span(%{span: %Span{} = span}), do: span
  defp parameter_site_span(_site), do: nil

  defp label_at(%Span{} = span, style, message),
    do: %Label{span: span, style: style, message: message}

  defp label_at(_span, _style, _message), do: nil

  defp named_implicit_unforced_failure(name, context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    implicit_name = name(name)
    primary_span = Map.get(context, :forced_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        label_at(
          Map.get(context, :named_implicit_span),
          :secondary,
          "this pattern refers to hidden field `#{implicit_name}`"
        ),
        label_at(
          Map.get(context, :constructor_name_span),
          :secondary,
          "`#{constructor}` does not expose `#{implicit_name}` in its result index"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "`#{implicit_name}` is not fixed by matching `#{constructor}`",
      body:
        Doc.paragraph(
          "The result type of `#{constructor}` does not determine its hidden `#{implicit_name}` field. A dot pattern can only check a value already fixed by the scrutinee, so this field must be bound to a variable instead."
        ),
      primary: label_at(primary_span, :primary, "this dot expression has no forced value to check"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Replace the dot expression with a variable binding, for example `{#{implicit_name} = value}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :named_implicit_unforced,
        constructor: constructor,
        implicit_name: implicit_name,
        expectation_origin: :pattern
      }
    )
  end

  defp unsolved_metavariable_failure(name, context, opts) do
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case {Map.get(context, :expectation_span), primary_span} do
        {%Span{} = span, %Span{} = primary} when span != primary ->
          [%Label{span: span, style: :secondary, message: "this result annotation still leaves them unknown"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Missing implicit argument",
      body:
        Doc.stack([
          Doc.paragraph("Cure could not infer every implicit argument for `#{name}` at this call site."),
          Doc.paragraph(
            "The call leaves hidden type or index values unconstrained. Provide arguments that determine them, or use the result where its dependent type is known."
          )
        ]),
      primary: label_at(primary_span, :primary, "these hidden arguments cannot be inferred"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Provide arguments or a result type that determines the hidden values",
          applicability: :manual
        }
      ],
      payload: Map.put(context, :name, name)
    )
  end

  defp checked_constructor_result_failure(unsolved_name, context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    expected = constructor_result_surface_type(Map.get(context, :constructor_expected_type))
    actual = constructor_result_surface_type(Map.get(context, :constructor_actual_type))
    primary_span = Map.get(context, :application_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :expectation_span),
          primary_span,
          "the surrounding annotation requires `#{expected}`"
        )
      ] ++
        Enum.map(
          Map.get(context, :argument_spans, []),
          &related_label(
            &1,
            primary_span,
            "this argument did not provide enough information to recover from the incompatible result"
          )
        )

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "`#{constructor}` cannot produce the expected indexed type",
      body:
        Doc.stack([
          Doc.paragraph("This constructor produces `#{actual}`, but this position requires `#{expected}`."),
          Doc.paragraph(
            "Cure also could not infer the hidden arguments of `#{surface_declaration_name(unsolved_name)}` while checking the constructor fields. Supplying those arguments cannot make incompatible result indices agree."
          )
        ]),
      primary: label_at(primary_span, :primary, "this `#{constructor}` result cannot satisfy `#{expected}`"),
      secondary: Enum.reject(secondary, &is_nil/1),
      suggestions: [
        %Suggestion{
          message: "Use a constructor whose result matches `#{expected}`, or change the surrounding result type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :constructor_result_mismatch,
        semantic_reason: :unsolved_metavariables,
        unsolved_name: surface_declaration_name(unsolved_name),
        constructor: constructor,
        expected: expected,
        actual: actual,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp nested_constructor_implicit_failure(name, context, opts) do
    constructor = surface_declaration_name(name)
    owner = context |> Map.get(:checking, :constructor) |> surface_declaration_name()
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :expectation_span) do
        %Span{} = span when span != primary_span ->
          [related_label(span, primary_span, "the surrounding result still does not determine these indices")]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Cannot infer `#{constructor}` inside `#{owner}`",
      body:
        Doc.paragraph(
          "Argument #{argument_index + 1} of `#{owner}` uses `#{constructor}`, but its hidden type or index values are still unknown. The surrounding result and the other constructor fields do not determine them."
        ),
      primary: label_at(primary_span, :primary, "this nested constructor needs an expected indexed type"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Use `#{constructor}` where its expected field type is known, or change the sibling arguments or result annotation so its indices are determined",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :nested_constructor_implicit,
        name: name,
        constructor: constructor,
        owner: Map.get(context, :checking),
        argument_index: argument_index,
        expectation_origin: :constructor_argument
      }
    )
  end

  defp constructor_result_surface_type({:data, family, parameters, indices}) do
    arguments = Enum.map(parameters ++ indices, &constructor_result_surface_type/1)
    name = surface_declaration_name(family)
    if arguments == [], do: name, else: "#{name}(#{Enum.join(arguments, ", ")})"
  end

  defp constructor_result_surface_type({:ctor, constructor, arguments}) do
    arguments = Enum.map(arguments, &constructor_result_surface_type/1)
    name = surface_declaration_name(constructor)
    if arguments == [], do: name, else: "#{name}(#{Enum.join(arguments, ", ")})"
  end

  defp constructor_result_surface_type({:global, name}), do: surface_declaration_name(name)
  defp constructor_result_surface_type({:meta, _id}), do: "?"
  defp constructor_result_surface_type(other), do: surface_type(other)

  defp surface_declaration_name(name) do
    name(name)
    |> String.split("#")
    |> List.last()
  end

  defp contextual_type_failure(:with_sibling_dependency_unsupported, _details, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With sibling dependency is unsupported",
      body: Doc.paragraph("This rematch depends on a sibling binding that is not available here."),
      primary: primary(opts, "restructure the dependent bindings"),
      payload: %{kind: :with_sibling_dependency_unsupported}
    )
  end

  defp local_binding_annotation_failure(kind, details, opts) do
    binding_name = name(details.name)
    use_count = Map.get(details, :use_count)

    {title, body, primary_message, hint} =
      case {kind, use_count, Map.get(details, :reason)} do
        {:graded, _, _} ->
          grade = name(Map.get(details, :grade, :graded))

          {
            "Graded binding needs a type",
            "`#{binding_name}` is declared `#{grade}`, but its initializer has no type Cure can synthesize without an expectation. Preserving the grade requires a real local binder, and Cure cannot construct that binder until its type is written.",
            "this grade cannot be preserved without a binding type",
            "Write the initializer's type after `#{binding_name} :`, before `=`"
          }

        {:ungraded, _, :shadowed_before_use} ->
          {
            "Shadowed binding needs a type",
            "Cure cannot synthesize a type for `#{binding_name}`'s initializer. A later binder also uses the name `#{binding_name}`, so substituting this initializer would cross that binding boundary and could capture the wrong value.",
            "this binding needs a type before it can cross a shadowing scope",
            "Add a type between `#{binding_name}` and `=` so this value is bound once before the inner `#{binding_name}`"
          }

        {:ungraded, 0, _} ->
          {
            "Unused binding needs a type",
            "Cure cannot synthesize a type for `#{binding_name}`'s initializer. Because the binding is unused, substituting it would discard the initializer without checking or evaluating it.",
            "this unused binding cannot safely discard its initializer",
            "Add a type between `#{binding_name}` and `=` so the initializer is checked exactly once"
          }

        {:ungraded, count, _} when is_integer(count) and count > 1 ->
          {
            "Repeated binding needs a type",
            "Cure cannot synthesize a type for `#{binding_name}`'s initializer. Substituting the initializer at its #{count} uses would duplicate the expression instead of evaluating and binding it once.",
            "this binding would duplicate its initializer #{count} times",
            "Add a type between `#{binding_name}` and `=` so the initializer is bound once"
          }

        _ ->
          {
            "Binding needs a type",
            "Cure cannot synthesize a type for `#{binding_name}`'s initializer, so this local binding needs an explicit type.",
            "this binding needs an explicit type",
            "Add a type between `#{binding_name}` and `=`"
          }
      end

    primary_span =
      case kind do
        :graded -> Map.get(details, :grade_span) || Map.get(details, :span)
        :ungraded -> Map.get(details, :name_span) || Map.get(details, :span)
      end || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(details, :initializer_span),
          primary_span,
          "this initializer needs an expected type"
        ),
        related_label(
          Map.get(details, :shadow_span),
          primary_span,
          "this inner binder shadows `#{binding_name}`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: label_at(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: if(kind == :graded, do: :graded_let_needs_annotation, else: :let_needs_annotation),
        name: binding_name,
        grade: Map.get(details, :grade),
        use_count: use_count,
        reason: Map.get(details, :reason, :initializer_not_inferable)
      }
    )
  end

  defp typealias_value_failure(details, opts) do
    alias_name = name(details.name)
    actual_surface = surface_type(details.actual_type)
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(details, :name_span),
          primary_span,
          "this declaration promises a type alias"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{alias_name}` aliases a value, not a type",
      body:
        Doc.paragraph(
          "The right side of a `typealias` must itself be a type, but this expression is a value whose type is `#{actual_surface}`. Type aliases give another name to a type; they cannot name one particular value."
        ),
      primary: label_at(primary_span, :primary, "this is a value of type `#{actual_surface}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "If `#{alias_name}` should alias the value's type, write `typealias #{alias_name} = #{actual_surface}`",
          applicability: :maybe_incorrect
        }
      ],
      payload: %{
        kind: :typealias_not_a_type,
        name: alias_name,
        actual_surface: actual_surface,
        rhs_shape: Map.get(details, :rhs_shape, :expression)
      }
    )
  end

  defp untyped_parameter_failure(details, opts) do
    parameter_name = name(details.name)
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "I need a type for `#{parameter_name}`",
      body:
        Doc.paragraph(
          "Cure cannot tell what values `#{parameter_name}` may receive from its name alone. Every ordinary function parameter needs a type annotation."
        ),
      primary: label_at(primary_span, :primary, "this parameter needs a type after its name"),
      suggestions: [
        %Suggestion{
          message:
            "Add a type annotation, such as `#{parameter_name}: Int`; write `{#{parameter_name}}` only for an implicit type parameter",
          applicability: :manual
        }
      ],
      payload: %{kind: :untyped_parameter, name: parameter_name}
    )
  end

  defp generic_annotation_failure(kind, detail, opts) do
    {title, body, message} =
      case kind do
        :untyped_parameter ->
          {"Parameter needs a type", "This parameter must have an explicit type annotation here.",
           "add a type annotation to the parameter"}

        :let_needs_annotation ->
          {"Binding needs an annotation", "Cure cannot infer the type of this binding from its initializer.",
           "add a type annotation to this binding"}

        :graded_let_needs_annotation ->
          {"Graded binding needs an annotation",
           "A graded binding must state the type required by its relevance grade.",
           "add a type annotation to this graded binding"}

        :typealias_not_a_type ->
          {"Type alias does not name a type", "The right-hand side of this type alias is not a well-formed type.",
           "define the alias using a type expression"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, message),
      payload: %{kind: kind, detail: detail}
    )
  end

  defp non_exhaustive_guard_failure(context, opts) do
    guard_labels =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.flat_map(fn
        %{guard_span: %Span{} = span} ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "this condition does not cover every remaining value"
            }
          ]

        _ ->
          []
      end)

    primary =
      case missing_branch_insertion_span(context) do
        %Span{} = span ->
          label_at(span, :primary, "add an unguarded fallback branch here")

        _ ->
          label_at(
            Map.get(context, :span) || Keyword.get(opts, :span),
            :primary,
            "this match needs a fallback"
          )
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Guarded branches leave a gap",
      body:
        Doc.paragraph(
          "Cure cannot prove that these guard conditions cover every value accepted by their patterns. If every condition is false, this match has no result."
        ),
      primary: primary,
      secondary: guard_labels,
      suggestions: [
        %Suggestion{
          message: "Add an unguarded `_ -> ...` branch, or make the final guards exact complements",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :non_exhaustive,
        checking: Map.get(context, :checking),
        guard_count: length(guard_labels)
      }
    )
  end

  defp refutable_guard_pattern_failure(details, context, opts) do
    shape = Map.get(details, :shape, :pattern)
    shape_name = guard_pattern_shape_name(shape)
    pattern_span = Map.get(details, :span)

    guard_span =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.find_value(fn branch ->
        if branch_pattern_span(branch) == pattern_span,
          do: Map.get(branch, :guard_span),
          else: nil
      end)

    secondary =
      case label_at(
             guard_span,
             :secondary,
             "this condition is attached to the refutable pattern"
           ) do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{String.capitalize(shape_name)} pattern cannot carry this guard",
      body:
        Doc.paragraph(
          "This #{shape_name} pattern can fail before its `when` condition is considered. The current guard chain only accepts variable, wildcard, or irrefutable tuple patterns."
        ),
      primary:
        label_at(
          pattern_span || Map.get(context, :span) || Keyword.get(opts, :span),
          :primary,
          "this refutable pattern cannot enter the guard chain"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Match this pattern first, then test the condition inside its branch and keep an explicit fallback",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :refutable_pattern,
        shape: shape,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp complex_guard_scrutinee_failure(details, context, opts) do
    span =
      Map.get(details, :span) || Map.get(context, :scrutinee_span) ||
        Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Guarded match needs a stable scrutinee",
      body:
        Doc.paragraph(
          "Guard conditions may inspect the matched value more than once. Bind this expression once before matching so its value is stable and any effects are not repeated."
        ),
      primary: label_at(span, :primary, "bind this expression before the guarded match"),
      suggestions: [
        %Suggestion{
          message: "Introduce a `let` binding for this expression, then match the new name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :complex_scrutinee,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp branch_pattern_span(%{pattern_span: %Span{} = span}), do: span
  defp branch_pattern_span(%{span: %Span{} = span}), do: span
  defp branch_pattern_span(_pattern), do: nil

  defp missing_branch_insertion_span(context) do
    case context |> Map.get(:branch_patterns, []) |> List.last() do
      %{span: %Span{} = span} ->
        %{span | start_byte: span.end_byte, start_line: span.end_line, start_column: span.end_column}

      _ ->
        nil
    end
  end

  defp guard_pattern_shape_name(:literal), do: "literal"
  defp guard_pattern_shape_name(:tuple), do: "tuple"
  defp guard_pattern_shape_name(:function_call), do: "constructor"

  defp guard_pattern_shape_name(shape),
    do: shape |> name() |> String.replace("_", " ")

  defp rematch_pattern_problem(kind, details, context, opts) do
    {title, body, message} =
      case kind do
        :with_rematch_ctor_mismatch ->
          {"With rematch constructor mismatch",
           "The rematched value uses a different constructor than the original `with` pattern.",
           "keep the rematch constructor aligned"}

        :with_rematch_non_constructor_pattern ->
          {"With rematch must use a constructor",
           "This `with` rematch is not a constructor pattern that can be checked against the original value.",
           "rematch with the corresponding constructor"}

        :with_rematch_inconsistent_binding ->
          {"With rematch binding is inconsistent",
           "The rematch binds a name differently from the original `with` pattern.",
           "keep bindings consistent across the rematch"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        primary(
          Keyword.put_new(opts, :span, Map.get(context, :span)),
          message
        ),
      payload:
        Map.merge(
          %{kind: kind, checking: Map.get(context, :checking)},
          details
        )
    )
  end

  defp generic_rematch_parent_failure(details, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With parent pattern is unsupported",
      body: Doc.paragraph("The parent pattern cannot be structurally rematched in this `with` expression."),
      primary: primary(opts, "use a supported parent pattern"),
      payload: %{kind: :with_rematch_unsupported_parent_pattern, detail: details}
    )
  end

  defp rematch_pattern_failure(kind, details, context, opts) do
    primary_span =
      Map.get(context, :span) || Map.get(context, :rematch_arm_span) ||
        Keyword.get(opts, :span)

    original_spans = Map.get(context, :original_pattern_spans, [])
    restated_spans = Map.get(context, :restated_pattern_spans, [])

    paired_original =
      restated_spans
      |> Enum.find_index(&(&1 == primary_span))
      |> then(fn
        nil -> Map.get(context, :original_patterns_span)
        index -> Enum.at(original_spans, index)
      end)

    {title, body, primary_message, hint} =
      rematch_pattern_content(kind, details, context)

    secondary =
      [
        related_label(
          paired_original,
          primary_span,
          "this is the corresponding original function pattern"
        ),
        related_label(
          Map.get(context, :rematch_separator_span),
          primary_span,
          "patterns before this `|` restate the function's left-hand side"
        ),
        related_label(
          Map.get(context, :with_pattern_span),
          primary_span,
          "this pattern matches the value after `with`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: body,
      primary: label_at(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload:
        Map.merge(
          %{
            kind: kind,
            checking: Map.get(context, :checking),
            original_pattern_count: Map.get(context, :original_pattern_count),
            restated_pattern_count: Map.get(context, :restated_pattern_count)
          },
          details
        )
    )
  end

  defp rematch_context_enriched?(context),
    do:
      match?(%Span{}, Map.get(context, :span)) and
        is_list(Map.get(context, :restated_pattern_spans))

  defp rematch_pattern_content(
         :with_rematch_non_constructor_pattern,
         details,
         _context
       ) do
    shape = Map.get(details, :details)

    {
      "Rematch pattern must describe a shape",
      Doc.stack([
        Doc.paragraph(
          "The left side of a `with` rematch restates the function's parameter patterns. It cannot evaluate an expression such as this `#{shape}` node."
        ),
        Doc.paragraph("Use variables and constructor patterns here; perform calculations in a guard or branch body.")
      ]),
      "this expression computes a value instead of matching a shape",
      "Replace this expression with a variable or constructor pattern, then move the calculation into the branch body"
    }
  end

  defp rematch_pattern_content(
         :with_rematch_ctor_mismatch,
         details,
         _context
       ) do
    original = details |> Map.get(:original) |> name()
    restated = details |> Map.get(:restated) |> name()

    {
      "Rematch changes an existing constructor",
      Doc.paragraph(
        "The original function pattern uses `#{original}`, but this branch restates that same position with `#{restated}`. A rematch may refine variables, but it cannot replace an already-written constructor."
      ),
      "this restates `#{original}` as incompatible constructor `#{restated}`",
      "Keep `#{original}` at this position, or move this case into a separate function clause"
    }
  end

  defp rematch_pattern_content(
         :with_rematch_inconsistent_binding,
         details,
         _context
       ) do
    binding_name = details |> Map.get(:details) |> name()

    {
      "Rematch gives `#{binding_name}` two different shapes",
      Doc.paragraph(
        "The original left-hand side binds `#{binding_name}` more than once, but this rematch gives those occurrences different patterns. Every occurrence must describe the same value."
      ),
      "this occurrence disagrees with another restatement of `#{binding_name}`",
      "Use the same variable or constructor pattern for every occurrence of `#{binding_name}`"
    }
  end

  defp rematch_pattern_content(
         :with_rematch_arity_mismatch,
         details,
         context
       ) do
    expected =
      Map.get(details, :expected, Map.get(context, :original_pattern_count))

    actual =
      Map.get(details, :actual, Map.get(context, :restated_pattern_count))

    {
      "Rematch has the wrong number of parent patterns",
      Doc.paragraph(
        "This function has #{expected} parent #{plural(expected, "pattern")}, but the branch restates #{actual}. The patterns before `|` must correspond position-for-position with the function's left-hand side."
      ),
      "these parent patterns do not match the function's arity",
      "Write exactly #{expected} #{plural(expected, "parent pattern")} before `|`"
    }
  end

  defp rematch_pattern_content(
         :with_rematch_unsupported_parent_pattern,
         details,
         _context
       ) do
    shape = Map.get(details, :details)

    {
      "Original function pattern cannot be rematched",
      Doc.paragraph(
        "This function parameter uses a `#{shape}` pattern that the LHS-rematch algorithm cannot structurally refine."
      ),
      "this original pattern cannot participate in a `with` rematch",
      "Bind this parameter to a name first, then refine that name in the `with` branches"
    }
  end

  defp plural(1, singular), do: singular
  defp plural(_count, singular), do: singular <> "s"

  defp family_type_problem(
         kind,
         actual,
         expected,
         origin,
         context,
         details,
         opts
       ) do
    opts =
      Keyword.put_new(
        opts,
        :provenance,
        family_provenance(details, opts)
      )

    from_error(
      %TypeProblem{
        kind: kind,
        actual: actual,
        expected: expected,
        origin: %ExpectationOrigin{
          kind: origin,
          span: Map.get(context, :expectation_span),
          owner: Map.get(context, :checking),
          index: Map.get(context, :argument_index)
        },
        expression: Map.get(context, :expression_category, :expression),
        span: Keyword.get(opts, :span, Map.get(context, :span)),
        debug: %{cause: {kind, actual, expected}, checking: Map.get(context, :checking)}
      },
      opts
    )
  end

  defp family_boundary_reason?({:foreign_ctor, _}), do: true
  defp family_boundary_reason?({:unknown_ctor, _}), do: true
  defp family_boundary_reason?(_reason), do: false

  defp family_boundary_failure(origin, details, reason, opts) do
    family = family_origin_name(origin)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{family} callback has the wrong type",
      body:
        Doc.paragraph(
          "This authored #{String.downcase(family)} callback does not produce the protocol value required by its generated module."
        ),
      primary:
        primary(
          opts,
          "this #{String.downcase(family)} callback has the wrong type"
        ),
      provenance: family_provenance(details, opts),
      payload: %{
        origin: %{kind: origin, owner: Map.get(details, :module)},
        cause: inspect(reason),
        module: Map.get(details, :module),
        behaviour: Map.get(details, :behaviour)
      }
    )
  end

  defp family_origin_name(:actor), do: "Actor"
  defp family_origin_name(:fsm), do: "FSM"
  defp family_origin_name(:supervisor), do: "Supervisor"

  defp family_origin(details) do
    case Map.get(details, :behaviour) do
      :gen_server -> :actor
      :gen_statem -> :fsm
      :supervisor -> :supervisor
      _ -> nil
    end
  end

  defp family_provenance(details, opts) do
    source = Map.get(details, :source_provenance) || %{}
    invocation = Keyword.get(opts, :span)

    chain_frames =
      details
      |> Map.get(:expansion_provenance, [])
      |> Enum.map(fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword) || "macro",
          invocation: invocation
        }
      end)

    source_frames =
      case Map.get(source, :macro) do
        nil ->
          []

        macro ->
          [
            %ProvenanceFrame{
              kind: :macro_expansion,
              name: macro,
              invocation: invocation
            }
          ]
      end

    (chain_frames ++ source_frames)
    |> Enum.uniq_by(& &1.name)
  end

  defp extern_union_failure(kind, extern_name, detail, context, opts) do
    extern_name = short_name(extern_name)
    return_span = Map.get(context, :return_span) || Map.get(context, :span)
    extern_span = Map.get(context, :extern_span)
    member_ids = Map.get(context, :union_members, [])
    members = Enum.map(member_ids, &ffi_member_surface/1)

    {title, body, message, hint} =
      case kind do
        :nested ->
          union =
            if members == [],
              do: "an anonymous union",
              else: Enum.join(members, " | ")

          {
            "Extern `#{extern_name}` nests a union in its return type",
            "The return type contains `#{union}` inside another type. Erlang returns one raw value, and Cure can only identify and tag a union when that union is the outermost return type.",
            "this return type nests a union across the foreign boundary",
            "Return the union directly, or tag the nested value in the foreign function"
          }

        :indistinct ->
          {
            "Extern `#{extern_name}` returns an indistinguishable union",
            ffi_indistinct_union_body(detail, members),
            "these union members have indistinguishable BEAM representations",
            "Return a tagged record or data type, or choose members with distinct BEAM shapes"
          }
      end

    secondary =
      [
        related_label(
          extern_span,
          return_span,
          "this declaration crosses an Erlang boundary"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        label_at(return_span, :primary, message) ||
          primary(opts, message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind:
          if(kind == :nested,
            do: :extern_returns_union,
            else: :extern_union_indistinct
          ),
        name: extern_name,
        union_member_ids: member_ids,
        union_members: members,
        conflict: ffi_union_conflict_payload(detail)
      }
    )
  end

  defp generic_ffi_failure(kind, details, opts) do
    {title, body, message} =
      case kind do
        :extern_returns_union ->
          {"Extern return type is unsupported", "An extern declaration cannot return this union type.",
           "use a representable foreign return type"}

        :extern_union_indistinct ->
          {"Extern union is indistinct", "The extern union members cannot be distinguished at the foreign boundary.",
           "make the foreign union members representationally distinct"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, message),
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def union_declaration_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :union_member_not_ground ->
          {"Union member is not ground", "Every union member must be a concrete, fully-resolved type.",
           "make this union member concrete"}

        :unsupported_member_shape ->
          {"Unsupported union member shape", "This union member has a runtime shape that Cure cannot represent safely.",
           "use a supported union member shape"}

        :same_runtime_shape ->
          {"Union members have the same runtime shape",
           "Two union members erase to the same runtime representation and cannot be distinguished.",
           "change one member's runtime shape"}

        :same_erased_literal ->
          {"Union members have the same erased literal",
           "Two union members erase to the same literal value and would overlap at runtime.",
           "use distinct literal values"}
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary(opts, label),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp ffi_indistinct_union_body(
         {:same_runtime_shape, [{left, right, runtime_class} | _]},
         _members
       ) do
    "`#{ffi_member_surface(left)}` and `#{ffi_member_surface(right)}` both arrive as BEAM #{runtime_shape_name(runtime_class)} values. Cure cannot tell which union alternative the foreign result belongs to."
  end

  defp ffi_indistinct_union_body(
         {:same_erased_literal, [{left, right} | _]},
         _members
       ) do
    "`#{ffi_member_surface(left)}` and `#{ffi_member_surface(right)}` erase to the same BEAM value. Cure cannot tell which union alternative the foreign result belongs to."
  end

  defp ffi_indistinct_union_body(
         {:unsupported_member_shape, unsupported},
         _members
       ) do
    "Cure has no single BEAM guard that can recognize #{Enum.map_join(unsupported, ", ", &"`#{ffi_member_surface(&1)}`")}. The raw foreign result therefore cannot be assigned to a union alternative safely."
  end

  defp ffi_indistinct_union_body(_reason, members) do
    union =
      if members == [],
        do: "These union members",
        else: Enum.map_join(members, " and ", &"`#{&1}`")

    "#{union} cannot be distinguished after crossing the foreign boundary."
  end

  defp ffi_union_conflict_payload({:same_runtime_shape, collisions}) do
    %{
      kind: :same_runtime_shape,
      pairs:
        Enum.map(collisions, fn {left, right, runtime_class} ->
          %{
            left: ffi_member_surface(left),
            right: ffi_member_surface(right),
            runtime_shape: runtime_class
          }
        end)
    }
  end

  defp ffi_union_conflict_payload({:same_erased_literal, collisions}) do
    %{
      kind: :same_erased_literal,
      pairs:
        Enum.map(collisions, fn {left, right} ->
          %{
            left: ffi_member_surface(left),
            right: ffi_member_surface(right)
          }
        end)
    }
  end

  defp ffi_union_conflict_payload({:unsupported_member_shape, members}),
    do: %{
      kind: :unsupported_member_shape,
      members: Enum.map(members, &ffi_member_surface/1)
    }

  defp ffi_union_conflict_payload(_detail), do: nil

  defp ffi_member_surface(member) do
    member = name(member)

    case String.split(member, "#", parts: 2) do
      [type, literal]
      when type in ["Int", "Nat", "Float", "String", "Atom", "Char", "Bool"] ->
        literal

      _ ->
        Regex.replace(
          ~r/[A-Za-z_][A-Za-z0-9_.]*#([A-Za-z_][A-Za-z0-9_]*)/,
          member,
          "\\1"
        )
    end
  end

  defp runtime_shape_name(:integer), do: "integer"
  defp runtime_shape_name(:float), do: "floating-point"
  defp runtime_shape_name(:binary), do: "binary"
  defp runtime_shape_name(:atom), do: "atom"
  defp runtime_shape_name(:boolean), do: "boolean"
  defp runtime_shape_name(:list), do: "list"
  defp runtime_shape_name(shape), do: name(shape)

  defp rewrite_failure(kind, context, opts) do
    rewrite_span = Map.get(context, :span) || Keyword.get(opts, :span)
    proof_span = Map.get(context, :proof_span)
    body_span = Map.get(context, :body_span)

    {title, body, primary_span, primary_message, secondary, hint} =
      case kind do
        :rewrite_requires_expected_type ->
          {
            "Rewrite result needs an annotation",
            "A rewrite changes the type expected by its body, so Cure must know the surrounding result type before it can construct the equality motive. This rewrite appears where that type is still being inferred.",
            rewrite_span,
            "this rewrite has no expected result type",
            rewrite_context_labels(
              [
                {proof_span, "this proof determines what the body rewrites"},
                {body_span, "this body must be checked against the rewritten result"}
              ],
              rewrite_span
            ),
            "Add a result annotation to the enclosing declaration, or place this rewrite where an expected type is already known"
          }

        :rewrite_proof_not_equality ->
          {
            "Rewrite proof is not an equality",
            "The expression after `rewrite` must prove an `Equivalent(T, left, right)` proposition. This expression has another type, so it provides no endpoints that Cure can substitute in the body.",
            proof_span || rewrite_span,
            "this expression does not prove an equality",
            rewrite_context_labels(
              [
                {body_span, "this body would be checked after applying the equality"}
              ],
              proof_span
            ),
            "Pass an `Equivalent` proof after `rewrite`, or remove `rewrite` if no equality is available"
          }

        :rewrite_no_match ->
          {
            "Rewrite does not change the goal",
            "The supplied equality is valid, but its left endpoint does not occur in the type required by this body. Applying it would leave the goal unchanged.",
            proof_span || rewrite_span,
            "this equality has no matching occurrence in the goal",
            rewrite_context_labels(
              [
                {body_span, "this body is checked against the unchanged goal"}
              ],
              proof_span
            ),
            "Use an equality whose left endpoint occurs in the expected result, or remove this rewrite"
          }
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: label_at(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: kind,
        expression_category: Map.get(context, :expression_category, :rewrite_expr),
        checking: Map.get(context, :checking)
      }
    )
  end

  defp rewrite_context_labels(labels, primary_span) do
    labels
    |> Enum.map(fn {span, message} ->
      related_label(span, primary_span, message)
    end)
    |> Enum.reject(&is_nil/1)
  end

  defp generic_rewrite_failure(kind, details, opts) do
    {title, body, message} =
      case kind do
        :rewrite_requires_expected_type ->
          {"Rewrite needs an expected type", "Cure cannot infer the type required by this rewrite.",
           "add an annotation that determines the rewrite target"}

        :rewrite_proof_not_equality ->
          {"Rewrite proof is not equality", "The proof supplied to rewrite does not establish an equality.",
           "provide an equality proof"}

        :rewrite_no_match ->
          {"Rewrite does not match", "The rewrite proof does not match the type being rewritten.",
           "use a proof whose endpoints match the target"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, message),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp bounded_literal_failure(value, bound, context, opts) do
    literal_span = Map.get(context, :span) || Keyword.get(opts, :span)
    expectation_span = Map.get(context, :expectation_span)

    {interval, hint} =
      if is_integer(bound) and bound > 0 do
        {
          "from `0` through `#{bound - 1}`",
          "Use an integer from 0 through #{bound - 1}"
        }
      else
        {
          "in an empty interval because its bound is `#{bound}`",
          "Use a positive bound before constructing this value"
        }
      end

    secondary =
      [
        related_label(
          expectation_span,
          literal_span,
          "this annotation requires `Bounded(#{bound})`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{value} is outside `Bounded(#{bound})`",
      body: Doc.paragraph("`Bounded(#{bound})` contains integer values #{interval}, but this literal is `#{value}`."),
      primary:
        label_at(
          literal_span,
          :primary,
          "this value does not fit the declared bound"
        ) || primary(opts, "this value does not fit the declared bound"),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :bounded_lit_out_of_range,
        value: value,
        bound: bound,
        minimum: 0,
        maximum: if(is_integer(bound) and bound > 0, do: bound - 1, else: nil)
      }
    )
  end

  defp constructor_result_family_failure(family, context, opts) do
    expected = short_name(Map.get(context, :expected_family, family))
    observed = short_name(Map.get(context, :observed_family, :unknown))
    constructor = short_name(Map.get(context, :constructor, :constructor))
    parameter_count = Map.get(context, :parameter_count, 0)
    index_count = Map.get(context, :index_count, 0)

    primary_span =
      Map.get(context, :result_span) || Map.get(context, :span) ||
        Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "this constructor belongs to `#{expected}`"
        ),
        related_label(
          Map.get(context, :family_name_span),
          primary_span,
          "`#{expected}` is the family being declared"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{constructor}` returns `#{observed}` instead of `#{expected}`",
      body:
        Doc.paragraph(
          "Every constructor must produce a value of the type family that declares it. `#{constructor}` is declared under `#{expected}`, but the final type in its signature is `#{observed}`."
        ),
      primary:
        label_at(
          primary_span,
          :primary,
          "this result names `#{observed}`, not constructor family `#{expected}`"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            constructor_result_hint(
              expected,
              parameter_count,
              index_count
            ),
          applicability: :manual
        }
      ],
      payload: %{
        kind: :result_type_not_family,
        family: expected,
        observed_family: observed,
        constructor: constructor,
        parameter_count: parameter_count,
        index_count: index_count
      }
    )
  end

  defp generic_result_family_failure(detail, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Result type is not a type family",
      body: Doc.paragraph("This dependent result must be a type family indexed by the function's result."),
      primary: primary(opts, "return a valid indexed type"),
      payload: %{kind: :result_type_not_family, detail: detail}
    )
  end

  defp constructor_result_hint(family, 0, 0),
    do: "End this constructor signature with `#{family}`"

  defp constructor_result_hint(family, parameter_count, index_count) do
    positions =
      [
        if(parameter_count > 0,
          do: "#{parameter_count} #{plural(parameter_count, "parameter")}"
        ),
        if(index_count > 0,
          do: "#{index_count} #{plural(index_count, "index")}"
        )
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" and ")

    "End this constructor signature with `#{family}` applied to its #{positions}"
  end

  defp erased_effect_binder_failure(details, context, opts) do
    binder_name = Map.get(context, :binder_name)
    type_span = Map.get(context, :span) || Keyword.get(opts, :span)
    binder_span = Map.get(context, :binder_span)
    opener = Map.get(context, :opener_span)
    closer = Map.get(context, :closer_span)
    binder_text = if binder_name, do: " `#{name(binder_name)}`", else: ""

    secondary =
      [
        related_label(
          binder_span,
          type_span,
          "this parameter is declared inside erased implicit braces"
        )
      ]
      |> Enum.reject(&is_nil/1)

    suggestions =
      case {opener, closer} do
        {%Span{} = open, %Span{} = close} ->
          [
            %Suggestion{
              message: "Make#{binder_text} a present parameter by removing the implicit braces",
              applicability: :machine_applicable,
              edits: [
                %TextEdit{span: open, replacement: ""},
                %TextEdit{span: close, replacement: ""}
              ]
            }
          ]

        _ ->
          [
            %Suggestion{
              message: "Make#{binder_text} a present parameter; an effect value cannot be erased",
              applicability: :manual
            }
          ]
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Effect parameter cannot be erased",
      body:
        Doc.paragraph(
          "The parameter#{binder_text} carries an `Effect` value, but implicit braces mark it for erasure. Removing that parameter at runtime could discard a computation the type says must remain available."
        ),
      primary:
        label_at(
          type_span,
          :primary,
          "this `Effect` type requires a runtime-present parameter"
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        kind: :effect_binder_erased,
        definition: Map.get(details, :def),
        binder_index: Map.get(details, :binder),
        binder: binder_name,
        expression_category: Map.get(context, :expression_category, :effect_binder)
      }
    )
  end

  defp record_update_base(details, context, opts) do
    record = Map.fetch!(details, :record)
    actual = Map.fetch!(details, :actual)
    record_surface = short_name(record)
    actual_surface = if is_atom(actual), do: short_name(actual), else: surface_type(actual)
    base_span = Map.get(context, :base_span) || Map.get(context, :span)
    record_span = Map.get(context, :record_name_span)

    secondary =
      case record_span do
        %Span{} = span when span != base_span ->
          [%Label{span: span, style: :secondary, message: "this update constructs `#{record_surface}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{record_surface}` update needs a `#{record_surface}` value",
      body:
        Doc.paragraph(
          "The value before `|` has type `#{actual_surface}`, but a `#{record_surface}` update must start from another `#{record_surface}` value."
        ),
      primary:
        if(match?(%Span{}, base_span),
          do: %Label{span: base_span, style: :primary, message: "this value has type `#{actual_surface}`"},
          else: primary(opts, "use a `#{record_surface}` value here")
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: "Use a `#{record_surface}` value before `|`", applicability: :manual}],
      payload: %{
        kind: :record_update_base_mismatch,
        record: record,
        record_surface: record_surface,
        actual: actual,
        actual_surface: actual_surface,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp projection_receiver(record, context, opts) do
    field = context |> Map.get(:field) |> name()
    receiver_span = Map.get(context, :receiver_span) || Map.get(context, :span)
    field_span = Map.get(context, :field_span)
    actual_type = if record, do: short_name(record)

    {title, body, receiver_message} =
      if actual_type do
        {
          "Cannot project `#{field}` from `#{actual_type}`",
          "This value has type `#{actual_type}`, which is not a record and therefore has no field named `#{field}`.",
          "this value has type `#{actual_type}`, not a record"
        }
      else
        {
          "Record projection requires a record",
          "This value is not a record, so it has no field named `#{field}`.",
          "this value is not a record"
        }
      end

    secondary =
      case field_span do
        %Span{} = span when span != receiver_span ->
          [%Label{span: span, style: :secondary, message: "this projection asks for field `#{field}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, receiver_span),
          do: %Label{span: receiver_span, style: :primary, message: receiver_message},
          else: primary(opts, receiver_message)
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Use a record value before `.#{field}`, or remove the projection", applicability: :manual}
      ],
      payload: %{
        kind: if(record, do: :projection_not_a_record, else: :projection_non_record),
        actual_type: actual_type,
        actual_type_id: record,
        field: field,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp dependent_projection(record, field, context, opts) do
    record_name = short_name(record)
    field = name(field)
    dependencies = Map.get(context, :dependent_fields, [])
    dependency_list = Enum.map_join(dependencies, ", ", &"`#{&1}`")
    primary_span = Map.get(context, :field_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    projected_site = Map.get(context, :projected_field_declaration, %{})
    dependent_sites = Map.get(context, :dependent_field_declarations, %{})

    dependency_phrase =
      case dependencies do
        [dependency] -> "the earlier field `#{dependency}`"
        [] -> "an earlier field"
        _ -> "the earlier fields #{dependency_list}"
      end

    secondary =
      [
        related_label(
          Map.get(context, :receiver_span),
          primary_span,
          "this value has dependent record type `#{record_name}`"
        ),
        related_label(
          site_span(projected_site),
          primary_span,
          "`#{field}` is declared with a type that depends on #{dependency_phrase}"
        )
      ] ++
        Enum.map(dependencies, fn dependency ->
          related_label(
            dependent_sites |> Map.get(dependency) |> site_span(),
            primary_span,
            "`#{dependency}` supplies part of `#{field}`'s type"
          )
        end)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{field}` cannot be projected without its dependency",
      body:
        Doc.paragraph(
          "The type of `#{record_name}.#{field}` depends on #{dependency_phrase}. Projecting only `#{field}` would discard the value needed to state its result type. Destructure the record so the dependent fields remain in scope together."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this projection separates `#{field}` from #{dependency_phrase}"
          }
        ),
      secondary: Enum.reject(secondary, &is_nil/1),
      suggestions: [
        %Suggestion{
          message: "Pattern-match `#{record_name}` and bind #{Enum.join(dependencies ++ [field], ", ")} together",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :dependent_record_projection,
        record: record_name,
        field: field,
        dependencies: dependencies,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp related_label(%Span{} = span, primary_span, message) when span != primary_span,
    do: %Label{span: span, style: :secondary, message: message}

  defp related_label(_span, _primary_span, _message), do: nil

  defp site_span(%{type_span: %Span{} = span}), do: span
  defp site_span(%{span: %Span{} = span}), do: span
  defp site_span(_site), do: nil

  defp short_name(value), do: value |> name() |> String.split("#") |> List.last()

  defp dependent_match_inference(context, opts) do
    branch_patterns = Map.get(context, :branch_patterns, [])
    branch = Enum.find(branch_patterns, &match?(%{span: %Span{}}, &1)) || List.first(branch_patterns)
    match_span = Map.get(context, :opener_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    branch_name = branch && Map.get(branch, :name)

    branch_message =
      if branch_name do
        "the `#{branch_name}` branch returns a type tied to values introduced by its pattern"
      else
        "this branch returns a type tied to values introduced by its pattern"
      end

    {primary, secondary} =
      case branch do
        %{span: %Span{} = branch_span} ->
          related =
            if match?(%Span{}, match_span) and match_span != branch_span do
              [%Label{span: match_span, style: :secondary, message: "this match has no expected result type"}]
            else
              []
            end

          {%Label{span: branch_span, style: :primary, message: branch_message}, related}

        _ ->
          {primary(Keyword.put(opts, :span, match_span), "this match needs an expected result type"), []}
      end

    checking = Map.get(context, :checking)
    owner = if checking, do: " `#{name(checking)}`", else: ""

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Dependent match result needs an annotation",
      body:
        Doc.paragraph(
          "Cure inferred a branch result whose type depends on values introduced by that branch's constructor pattern. Those values do not exist outside the branch, so Cure cannot choose one result type for#{owner} without an annotation."
        ),
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Add a result annotation to `#{name(checking || :the_enclosing_declaration)}` that states the indexed result shared by every branch",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :cannot_infer_dependent_match,
        checking: checking,
        expression_category: Map.get(context, :expression_category, :pattern_match),
        branch: branch_name
      }
    )
  end

  defp indexed_with_proof(family, context, opts) do
    family = family |> name() |> String.split("#") |> List.last()
    proof_name = Map.get(context, :proof_name)
    proof_span = Map.get(context, :proof_span) || Map.get(context, :span)
    scrutinee_span = Map.get(context, :scrutinee_span)

    proof_binding =
      if proof_name,
        do: "The `proof #{proof_name}` clause asks Cure to bind a value equation in every branch.",
        else: "This `with` asks Cure to transport a value equation into every branch."

    branch_labels =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.flat_map(fn
        %{span: %Span{} = span} ->
          [%Label{span: span, style: :secondary, message: "this branch would need an indexed value equation"}]

        _ ->
          []
      end)

    scrutinee_label =
      case scrutinee_span do
        %Span{} = span ->
          [%Label{span: span, style: :secondary, message: "this value belongs to indexed family `#{family}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Indexed with cannot bind a value proof",
      body:
        Doc.stack([
          Doc.paragraph(proof_binding),
          Doc.paragraph(
            "`#{family}` is indexed, so its branch constructors can refine type indices. Cure cannot also synthesize the whole-value equation requested by this form."
          )
        ]),
      primary: %Label{
        span: proof_span || Keyword.get(opts, :span),
        style: :primary,
        message: "this proof binding is unsupported for an indexed `with`"
      },
      secondary: scrutinee_label ++ branch_labels,
      suggestions: [
        %Suggestion{
          message:
            "Remove `proof #{proof_name || "..."}` when the equation is unused, or rewrite every branch in the indexed LHS-rematch form",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_indexed_scrutinee_unsupported,
        checking: Map.get(context, :checking),
        family: family,
        proof_name: proof_name,
        branch_count: length(branch_labels)
      }
    )
  end

  defp mixed_with_arms(context, opts) do
    arms =
      context
      |> Map.get(:with_arms, [])
      |> Enum.filter(&match?(%{style: style, span: %Span{}} when style in [:ordinary, :rematch], &1))

    frequencies = Enum.frequencies_by(arms, & &1.style)

    outlier_index =
      Enum.find_index(arms, fn arm ->
        Map.get(frequencies, arm.style) == 1 and
          Enum.any?(frequencies, fn {style, count} -> style != arm.style and count > 1 end)
      end)

    labels =
      arms
      |> Enum.with_index()
      |> Enum.map(fn {arm, index} ->
        %{span: arm.span, message: with_arm_label(arm.style, index == outlier_index), index: index}
      end)

    {primary, secondary} =
      case labels do
        [] ->
          {primary(Keyword.put_new(opts, :span, Map.get(context, :span)), "use one branch form throughout"), []}

        available ->
          chosen_index = outlier_index || 0
          chosen = Enum.at(available, chosen_index)

          secondary =
            available
            |> Enum.reject(&(&1.index == chosen_index))
            |> Enum.map(&%Label{span: &1.span, style: :secondary, message: &1.message})

          {%Label{span: chosen.span, style: :primary, message: chosen.message}, secondary}
      end

    body =
      if outlier_index do
        style = arms |> Enum.at(outlier_index) |> Map.fetch!(:style)

        Doc.stack([
          Doc.paragraph(
            "Possible outlier: only one branch uses the #{with_arm_style(style)} form; the other branches use the other form."
          ),
          Doc.paragraph(
            "A `with` block must use one shape throughout: either `Pattern -> body` in every branch, or `ParentPattern | WithPattern -> body` in every branch."
          )
        ])
      else
        Doc.stack([
          Doc.paragraph("These branches mix the two forms accepted by a `with` block."),
          Doc.paragraph(
            "Use either `Pattern -> body` in every branch, or `ParentPattern | WithPattern -> body` in every branch."
          )
        ])
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With branches use incompatible forms",
      body: body,
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Make every branch use the same `with` form; changing forms may change which values are refined",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_mixed_rematch_arms,
        checking: Map.get(context, :checking),
        branch_forms: Enum.map(arms, & &1.style),
        outlier_branch: outlier_index
      }
    )
  end

  defp with_arm_label(style, true),
    do: "possible outlier: this is the only #{with_arm_style(style)} branch"

  defp with_arm_label(:ordinary, false), do: "ordinary branch: `Pattern -> body`"
  defp with_arm_label(:rematch, false), do: "rematch branch: `ParentPattern | WithPattern -> body`"

  defp with_arm_style(:ordinary), do: "ordinary `Pattern -> body`"
  defp with_arm_style(:rematch), do: "rematch `ParentPattern | WithPattern -> body`"

  defp non_data_with(context, opts) do
    actual_type = context |> Map.get(:actual_type) |> surface_type()
    scrutinee_span = Map.get(context, :scrutinee_span) || Map.get(context, :span)
    form = Map.get(context, :with_form, :ordinary)

    branch_labels =
      context
      |> Map.get(:with_arms, [])
      |> Enum.flat_map(fn
        %{span: %Span{} = span} ->
          [%Label{span: span, style: :secondary, message: non_data_with_branch_label(form)}]

        _ ->
          []
      end)

    opener_label =
      case Map.get(context, :opener_span) do
        %Span{} = span when span != scrutinee_span ->
          [%Label{span: span, style: :secondary, message: "this `with` tries to refine the value by constructors"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With requires a data value",
      body:
        Doc.stack([
          Doc.paragraph(
            "This `with` scrutinee has type `#{actual_type}`, which does not provide data constructors to refine."
          ),
          Doc.paragraph(non_data_with_explanation(form))
        ]),
      primary: %Label{
        span: scrutinee_span || Keyword.get(opts, :span),
        style: :primary,
        message: "`#{actual_type}` cannot be split into constructor branches"
      },
      secondary: opener_label ++ branch_labels,
      suggestions: [
        %Suggestion{
          message:
            "Use `pickup` for conditions on primitive values, or remove `with` when no constructor refinement is needed",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_scrutinee_not_data,
        checking: Map.get(context, :checking),
        actual_type: actual_type,
        with_form: form,
        branch_count: length(branch_labels)
      }
    )
  end

  defp non_data_match(context, opts) do
    actual_type = context |> Map.get(:actual_type) |> surface_type()
    scrutinee_span = Map.get(context, :scrutinee_span) || Map.get(context, :span)

    constructor_patterns =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.filter(&(Map.get(&1, :kind) == :constructor and match?(%Span{}, Map.get(&1, :pattern_span))))

    pattern_labels =
      Enum.map(constructor_patterns, fn pattern ->
        %Label{
          span: pattern.pattern_span,
          style: :secondary,
          message: "`#{Map.get(pattern, :name, "this pattern")}` expects a data constructor"
        }
      end)

    {primary, remaining_patterns} =
      case pattern_labels do
        [%Label{} = first | rest] ->
          {%Label{first | style: :primary, message: "this constructor pattern cannot match `#{actual_type}`"}, rest}

        [] ->
          {%Label{
             span: scrutinee_span || Keyword.get(opts, :span),
             style: :primary,
             message: "`#{actual_type}` does not provide data constructors"
           }, []}
      end

    scrutinee_label =
      if match?(%Span{}, scrutinee_span) and scrutinee_span != primary.span do
        [%Label{span: scrutinee_span, style: :secondary, message: "this expression has type `#{actual_type}`"}]
      else
        []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Constructor patterns cannot match #{actual_type}",
      body:
        Doc.stack([
          Doc.paragraph(
            "The value being matched has type `#{actual_type}`, but these branches try to deconstruct it with data constructors."
          ),
          Doc.paragraph(
            "Constructor patterns work only when the scrutinee belongs to the same constructor-defined data type."
          )
        ]),
      primary: primary,
      secondary: scrutinee_label ++ remaining_patterns,
      suggestions: [
        %Suggestion{
          message:
            "Use a variable or wildcard for the whole `#{actual_type}` value, a supported literal pattern for a primitive, or match constructor-defined data",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :match_scrutinee_not_data,
        checking: Map.get(context, :checking),
        actual_type: actual_type,
        constructor_patterns: Enum.map(constructor_patterns, &Map.get(&1, :name))
      }
    )
  end

  defp non_data_with_explanation(:rematch),
    do:
      "A rematch branch can restate the parent patterns only when the value after `with` belongs to a constructor-defined data type."

  defp non_data_with_explanation(_ordinary),
    do:
      "A `with` block refines its surrounding goal through the constructors of the value after `with`; it is not a general conditional."

  defp non_data_with_branch_label(:rematch),
    do: "this rematch branch needs a constructor-defined `with` value"

  defp non_data_with_branch_label(_ordinary),
    do: "this branch cannot refine a value without constructors"

  defp match_inference(reason, details, opts) do
    {title, body, primary_message, hint} =
      case reason do
        :no_constructor_arm ->
          {
            "Match result needs an annotation",
            "Cure is inferring the result type of this match, but none of its patterns names a constructor. A wildcard or variable arm can handle values of many data types, so it does not reveal the family or dependent result that the branches must share.",
            "this match has no constructor arm to guide inference",
            "Add a result annotation to the enclosing declaration, or include a constructor pattern that identifies the matched data family"
          }

        :scrutinee_not_data ->
          {
            "Match target does not have a data type",
            "Cure can only infer an unannotated match from a scrutinee whose type has constructors. This value does not infer as a data family, so its patterns cannot determine a shared result type.",
            "this match cannot infer a result from its target",
            "Match a value of a declared data type, or add a result annotation that gives this match an expected type"
          }

        :unknown ->
          {
            "Cannot infer match type",
            "Cure cannot determine one result type shared by every branch of this match.",
            "add an annotation or make the branches agree",
            "Add a result annotation to the enclosing declaration"
          }
      end

    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: if(match?(%Span{}, span), do: %Label{span: span, style: :primary, message: primary_message}),
      secondary: match_inference_labels(reason, details, span),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :cannot_infer_match_type,
        reason: reason,
        expression_category: Map.get(details, :expression_category, :pattern_match)
      }
    )
  end

  defp match_inference_labels(:no_constructor_arm, details, primary_span) do
    details
    |> Map.get(:branch_spans, [])
    |> Enum.filter(&(match?(%Span{}, &1) and &1 != primary_span))
    |> Enum.map(&%Label{span: &1, style: :secondary, message: "this pattern does not identify a constructor"})
  end

  defp match_inference_labels(:scrutinee_not_data, details, primary_span) do
    case Map.get(details, :scrutinee_span) do
      %Span{} = span when span != primary_span ->
        [%Label{span: span, style: :secondary, message: "this value does not infer as a data family"}]

      _ ->
        []
    end
  end

  defp match_inference_labels(_reason, _details, _primary_span), do: []

  defp non_callable(details, context, opts) do
    index = Map.get(details, :argument_index, 0)
    actual = surface_type(Map.get(details, :actual))
    callee = Map.get(context, :callee_name)
    callee_span = Map.get(context, :callee_span)
    argument_span = Map.get(context, :argument_span)
    fallback_span = Map.get(context, :span) || Keyword.get(opts, :span)

    {title, body, primary_span, primary_message, related, hint} =
      if index == 0 do
        {
          "`#{actual}` value is not callable",
          "Parentheses apply a function or constructor, but this expression has type `#{actual}`. It cannot accept the argument written after it.",
          callee_span || fallback_span,
          "this expression has type `#{actual}`, not a function type",
          [{argument_span, "this argument has nowhere to go"}],
          "Remove the parentheses, or replace this expression with a function or constructor"
        }
      else
        callee_name = if callee, do: "`#{callee}`", else: "This call"

        {
          "#{callee_name} is given too many arguments",
          "After accepting #{index} #{if(index == 1, do: "argument", else: "arguments")}, #{callee_name} produces `#{actual}`. That result is not a function, so it cannot accept argument #{index + 1}.",
          argument_span || fallback_span,
          "this extra argument is applied to a `#{actual}` result",
          [{callee_span, "#{callee_name} has already produced its result before this argument"}],
          "Remove argument #{index + 1}, or call a function whose result accepts another argument"
        }
      end

    secondary =
      related
      |> Enum.filter(fn {span, _message} -> match?(%Span{}, span) and span != primary_span end)
      |> Enum.map(fn {span, message} -> %Label{span: span, style: :secondary, message: message} end)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{span: primary_span, style: :primary, message: primary_message}
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :applied_non_function,
        actual_type: actual,
        argument_index: index,
        callee: callee,
        expression_category: Map.get(context, :expression_category, :function_call)
      }
    )
  end

  defp instance_failure(interface, head, context, opts) do
    interface = name(interface)
    head = instance_head(head)

    {body, label, hint} =
      case head.kind do
        :type_variable ->
          {
            "This expression uses `#{interface}` operations on a type variable, but the surrounding function does not require `#{interface}` for that type.",
            "this operation requires `#{interface}` for its type variable",
            "Add a `where #{interface}(...)` constraint using this parameter's type variable"
          }

        :concrete ->
          {
            "No implementation of `#{interface}` is available for `#{head.surface}`. Cure needs one here to choose the behavior of this operation.",
            "this operation requires `#{interface}` for `#{head.surface}`",
            "Add or import `implementation #{interface} for #{head.surface}`"
          }
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "No `#{interface}` implementation found",
      body: Doc.paragraph(body),
      primary: primary(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :no_instance,
        interface: interface,
        head_kind: head.kind,
        head_surface: head.surface,
        head_id: head.id,
        expectation_origin: Map.get(context, :expectation_origin, :implicit),
        checking: Map.get(context, :checking)
      }
    )
  end

  # A `requires Iface(a)` whose `a` occurs in no parameter type is resolved from
  # the type expected at the call — the shape `Std.Json.decode_as` uses, where
  # `t` is named by the result and by the constraint and by nothing else. When
  # the expected type does not have the declared result's shape, there is no
  # position to read `a` off and the call cannot be resolved.
  #
  # This is an authoring mistake about the annotation, not a missing
  # implementation, so it must not be reported as one: telling the author to
  # write `implementation FromJSON for ...` sends them to fix code that is
  # already correct. Name the constraint, say what is unfixed, show the shape
  # the annotation has to take, and point at the annotation that fell short.
  defp undetermined_constraint_head(details, context, opts) do
    interface = name(details.interface)
    tyvar = name(details.type_variable)
    callee = name(details.callee)
    expected_surface = surface_type(details.expected)
    result_surface = constraint_result_surface(details.result_type)

    origin = %ExpectationOrigin{
      kind: Map.get(context, :expectation_origin, :annotation),
      span: Map.get(context, :expectation_span),
      owner: Map.get(context, :checking)
    }

    span = Keyword.get(opts, :span)

    occurrence =
      if result_surface,
        do: "it occurs only in the result type `#{result_surface}`",
        else: "it occurs only in the result type"

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Constraint type is not determined",
      body:
        Doc.stack([
          Doc.paragraph(
            "`#{callee}` requires `#{interface}(#{tyvar})`, and no argument fixes `#{tyvar}`: #{occurrence}."
          ),
          Doc.paragraph(
            "So `#{tyvar}` has to come from the type expected here, and `#{expected_surface}` does not " <>
              "supply it. Without `#{tyvar}` there is no `#{interface}` implementation to choose."
          )
        ]),
      primary: if(span, do: %Label{span: span, style: :primary, message: "`#{tyvar}` is not determined here"}),
      secondary: expectation_labels(origin, span, nil),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      suggestions: [
        %Suggestion{
          message:
            if(result_surface,
              do:
                "Annotate this call with a result type of the form `#{result_surface}`, " <>
                  "naming the type `#{interface}` should use for `#{tyvar}`",
              else: "Annotate this call with a result type that names the type `#{interface}` should use for `#{tyvar}`"
            ),
          applicability: :manual
        }
      ],
      payload: %{
        kind: :constraint_head_not_determined,
        interface: details.interface,
        type_variable: details.type_variable,
        callee: details.callee,
        expected_surface: expected_surface,
        result_surface: result_surface,
        checking: Map.get(context, :checking)
      }
    )
  end

  # The declared result type as the author wrote it. This is a surface AST, not
  # Core: it is the un-elaborated `-> Result(t, DecodeError)` of the callee's
  # signature, and the type variable in it is exactly the one the constraint
  # names. Anything else — a bare type, an unusual shape — has no useful spelling
  # here, so say nothing rather than guess.
  defp constraint_result_surface({:variable, _meta, var}), do: name(var)

  defp constraint_result_surface({:function_call, meta, args}) when is_list(meta) and is_list(args) do
    case Keyword.get(meta, :name) do
      nil ->
        nil

      head ->
        rendered = Enum.map(args, &constraint_result_surface/1)
        if Enum.all?(rendered), do: "#{name(head)}(#{Enum.join(rendered, ", ")})"
    end
  end

  defp constraint_result_surface(_ast), do: nil

  defp ambiguous_instance_failure(interface, expected, opts) do
    interface = name(interface)
    expected_surface = surface_type(expected)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Instance resolution is ambiguous",
      body:
        Doc.paragraph(
          "More than one `#{interface}` implementation can satisfy the expected type `#{expected_surface}`."
        ),
      primary: primary(opts, "make the `#{interface}` implementation choice unambiguous"),
      suggestions: [
        %Suggestion{
          message: "Qualify the implementation, add an annotation, or remove the overlapping instance",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :ambiguous_instance,
        interface: interface,
        expected_surface: expected_surface
      }
    )
  end

  defp instance_head({:rigid, index}) when is_integer(index),
    do: %{kind: :type_variable, surface: "a type variable", id: "rigid:#{index}"}

  defp instance_head(head) when is_atom(head) or is_binary(head) do
    canonical = name(head)
    surface = Cure.Elab.Name.base(head) || canonical
    %{kind: :concrete, surface: name(surface), id: canonical}
  end

  defp instance_head(head) do
    surface = surface_type(head)
    %{kind: :concrete, surface: surface, id: surface}
  end

  defp overload_mismatch(details, opts) do
    overload_name = name(details.name)

    arguments =
      details
      |> Map.get(:arguments, [])
      |> Enum.map(fn
        nil -> "unknown"
        type -> overload_type(type)
      end)

    candidates =
      details
      |> Map.get(:candidates, [])
      |> Enum.map(fn candidate ->
        owner = Map.get(candidate, :owner)
        prefix = if owner, do: "#{name(owner)}.", else: ""
        parameters = Enum.map_join(Map.get(candidate, :parameters, []), ", ", &overload_type/1)

        %{
          id: name(Map.get(candidate, :id, overload_name)),
          owner: if(owner, do: name(owner)),
          signature: "#{prefix}#{overload_name}(#{parameters})"
        }
      end)
      |> Enum.sort_by(& &1.signature)

    argument_text = if arguments == [], do: "unknown argument types", else: Enum.join(arguments, ", ")

    candidates_doc =
      case candidates do
        [] ->
          Doc.paragraph("No declared overload accepts these argument types.")

        available ->
          Doc.stack([
            Doc.paragraph("These overloads are available:"),
            Doc.bullet_list(Enum.map(available, &"`#{&1.signature}`"))
          ])
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "No overload of `#{overload_name}` matches",
      body:
        Doc.stack([
          Doc.paragraph("This call supplies argument types `#{argument_text}`."),
          candidates_doc
        ]),
      primary: primary(opts, "these arguments do not match any `#{overload_name}` overload"),
      suggestions: [
        %Suggestion{
          message: "Change the arguments to match one of the listed signatures",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :no_matching_overload,
        name: overload_name,
        arguments: arguments,
        candidates: candidates
      }
    )
  end

  defp overload_ambiguity(overload_name, owners, opts) do
    overload_name = name(overload_name)
    owners = owners |> List.wrap() |> Enum.map(&name/1) |> Enum.uniq() |> Enum.sort()
    candidates = Enum.map(owners, &qualified_candidate(&1, overload_name))

    {candidate_text, verb} =
      case candidates do
        [one] -> {"`#{one}`", "accepts"}
        [one, two] -> {"Both `#{one}` and `#{two}`", "accept"}
        many -> {"All of " <> Enum.map_join(many, ", ", &"`#{&1}`"), "accept"}
      end

    hint =
      case candidates do
        [one] -> "Qualify the call as `#{one}(...)`"
        [one, two] -> "Choose `#{one}(...)` or `#{two}(...)`"
        many -> "Qualify the call with one of: " <> Enum.map_join(many, ", ", &"`#{&1}(...)`")
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Call to `#{overload_name}` is ambiguous",
      body:
        Doc.paragraph(
          "#{candidate_text} #{verb} the arguments at this call site. Cure cannot choose one without changing the program's meaning."
        ),
      primary: primary(opts, "qualify this call with the module you intend"),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :ambiguous_overload,
        name: overload_name,
        owners: owners,
        qualified_candidates: candidates
      }
    )
  end

  defp overload_type(type) when is_atom(type) or is_binary(type),
    do: name(Cure.Elab.Name.base(type) || type)

  defp overload_type(type), do: surface_type(type)

  defp qualified_candidate(owner, overload_name) do
    if String.contains?(owner, ".#{overload_name}"), do: owner, else: "#{owner}.#{overload_name}"
  end

  defp operator_failure(kind, operator, context, opts) do
    spelling = name(operator)
    types = context |> Map.get(:operand_types, []) |> Enum.map(&surface_type/1)
    operator_span = Map.get(context, :operator_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    {title, body, primary_message, hint} = operator_copy(kind, spelling, types)

    secondary =
      context
      |> Map.get(:operand_spans, [])
      |> Enum.with_index()
      |> Enum.map(fn {span, index} ->
        side = if index == 0, do: "left", else: "right"

        message =
          case Enum.at(types, index) do
            nil -> "the #{side} operand is here"
            type -> "the #{side} operand has type `#{type}`"
          end

        if match?(%Span{}, span), do: %Label{span: span, style: :secondary, message: message}
      end)
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: if(kind == :unsupported_operand_type, do: :operator_type_mismatch, else: :operator_resolution),
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, operator_span),
          do: %Label{span: operator_span, style: :primary, message: primary_message}
        ),
      secondary: if(kind == :unsupported_operand_type, do: secondary, else: []),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, operator: operator, operand_types: types}
    )
  end

  defp operator_copy(:unsupported_operand_type, spelling, types) do
    description =
      case types do
        [left, right] -> "`#{left}` on the left and `#{right}` on the right"
        _ -> "the operand types used here"
      end

    {
      "`#{spelling}` does not support these operands",
      "The `#{spelling}` operator does not accept #{description}.",
      "this operator is not defined for these operand types",
      "Change the operand types, or use an operator or interface implementation defined for them"
    }
  end

  defp operator_copy(:no_operator_meaning, spelling, _types) do
    {
      "`#{spelling}` has no definition",
      "A fixity declaration tells Cure how to parse `#{spelling}`, but no function, constructor, or interface method with that name is available here.",
      "this operator has precedence, but no callable definition",
      "Define `#{spelling}` with two parameters, import its definition, or use an operator that is in scope"
    }
  end

  defp branch_failure(context, opts) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))
    branches = Keyword.get(opts, :branch_patterns, Map.get(context, :branch_patterns, []))
    branch_names = Enum.map(branches, &branch_name/1)
    checking = Map.get(context, :checking)
    subject = if checking, do: " in `#{checking}`", else: ""
    details = Map.get(context, :branch_details, %{})
    branch_details = Map.get(details, :branches, [])

    selected =
      case Enum.find(branch_details, &match?({:error, _}, Map.get(&1, :status))) do
        nil -> List.first(branch_details, details)
        detail -> detail
      end

    singleton_branches = singleton_type_branches(branch_details)

    failing =
      Map.get(selected, :constructor) ||
        case singleton_branches do
          [{constructor, _type}] -> constructor
          _ -> nil
        end

    actual = Map.get(selected, :actual)
    expected = Map.get(selected, :expected)

    detail =
      branch_detail(singleton_branches, failing, actual, expected, branch_names)

    labels =
      branches
      |> Enum.map(fn branch ->
        branch_name = branch_name(branch)

        message =
          if same_branch?(branch_name, failing),
            do: "possible outlier: this branch has the incompatible type",
            else: "compare this branch with the declared result"

        %{span: branch_span(branch), name: branch_name, message: message}
      end)
      |> Enum.reject(&is_nil(&1.span))
      |> Enum.sort_by(fn item -> if String.starts_with?(item.message, "possible outlier"), do: 0, else: 1 end)

    {primary, secondary} = branch_labels(labels, failing, opts)
    dependent? = Map.get(context, :expectation_origin) == :dependent_branch

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title:
        if(dependent?,
          do: "Dependent branch has the wrong result#{subject}",
          else: "Pattern branches disagree#{subject}"
        ),
      body:
        Doc.stack([
          Doc.paragraph(detail),
          Doc.paragraph(
            if dependent?,
              do:
                "This constructor refines indices in the branch context. Check the authored branch against the resulting specialized proposition.",
              else: "Check each branch expression against the result type written after the function name."
          )
        ]),
      primary: primary,
      secondary: secondary,
      payload: %{
        kind: :branch_type,
        branches: branch_names,
        failing_branch: failing,
        actual_surface: if(actual, do: surface_type(actual)),
        expected_surface: if(expected, do: surface_type(expected)),
        branch_types: branch_type_payload(branch_details),
        checking: checking,
        expression_category: Map.get(context, :expression_category),
        expectation_origin: Map.get(context, :expectation_origin)
      }
    )
  end

  defp branch_detail([{constructor, type}], _failing, _actual, _expected, _names),
    do:
      "Possible outlier: only the `#{name(constructor)}` branch has type `#{type}`; check it against the other branches and the declared result."

  defp branch_detail(_singletons, constructor, actual, expected, _names)
       when not is_nil(constructor) and not is_nil(actual) and not is_nil(expected),
       do:
         "Possible outlier: the `#{name(constructor)}` branch has type `#{surface_type(actual)}`, but the declared result requires `#{surface_type(expected)}`."

  defp branch_detail(_singletons, _failing, _actual, _expected, [first, second | rest]) do
    names = Enum.map_join([first, second | rest], ", ", &"`#{&1}`")

    "The branches #{names} of this match are checked against the declared result, but at least one branch does not produce that result."
  end

  defp branch_detail(_singletons, _failing, _actual, _expected, _names),
    do: "Every branch of this match is checked against the declared result type."

  defp branch_labels([], _failing, opts),
    do: {primary(opts, "make these branches return the same type"), []}

  defp branch_labels(labels, failing, _opts) do
    {outliers, comparisons} = Enum.split_with(labels, &same_branch?(&1.name, failing))
    [chosen | rest] = if outliers == [], do: labels, else: outliers ++ comparisons

    primary = %Label{span: chosen.span, style: :primary, message: chosen.message}

    secondary =
      Enum.map(rest, &%Label{span: &1.span, style: :secondary, message: &1.message})

    {primary, secondary}
  end

  defp singleton_type_branches(details) do
    groups =
      details
      |> Enum.filter(&(not is_nil(Map.get(&1, :actual))))
      |> Enum.group_by(&surface_type(&1.actual))

    if map_size(groups) > 1 and Enum.any?(groups, fn {_type, entries} -> length(entries) > 1 end) do
      for {type, [entry]} <- groups, do: {entry.constructor, type}
    else
      []
    end
  end

  defp branch_type_payload(details) do
    Enum.map(details, fn detail ->
      %{
        branch: detail.constructor,
        status: detail.status,
        actual: if(detail.actual, do: surface_type(detail.actual)),
        expected: if(detail.expected, do: surface_type(detail.expected))
      }
    end)
  end

  defp branch_name(%{name: name}), do: to_string(name)
  defp branch_name(name), do: to_string(name)

  defp same_branch?(_name, nil), do: false

  defp same_branch?(branch, failing) do
    branch = to_string(branch)
    failing = to_string(failing)
    failing == branch or String.ends_with?(failing, "#" <> branch) or String.ends_with?(failing, "." <> branch)
  end

  defp branch_span(%{span: %Span{} = span}), do: span
  defp branch_span(_branch), do: nil

  @doc false
  @spec contextual_failure(atom(), map(), keyword(), {String.t(), String.t(), String.t()}) :: Diagnostic.t()
  def contextual_failure(kind, details, opts, {title, message, label}) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary(opts, label),
      suggestions: [
        %Suggestion{
          message: sentence_case(label),
          applicability: :manual
        }
      ],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp character_literal_failure(kind, value, opts) do
    {title, message, label, hint} =
      case kind do
        :char_literal_needs_bounded ->
          {
            "Character literal needs a bound",
            "This character literal requires an explicit bounded character type.",
            "this character literal needs a bounded character type",
            "Add the required bounded character annotation"
          }

        :char_literal_out_of_range ->
          # Name the bound. "The supported character range" told the author
          # nothing they could act on — the range is Unicode scalar space, it is
          # fixed, and a numeral checked against `Char` is admitted by exactly
          # this rule, so the endpoints are the whole answer.
          {
            "Character literal is out of range",
            "The character value `#{inspect(value)}` is not a Unicode code point. " <>
              "A `Char` holds a code point in `0`..`#{0x110000 - 1}` (`0x10FFFF`), " <>
              "the whole of Unicode scalar space.",
            "code point must be between 0 and #{0x110000 - 1}",
            "Use a code point in `0`..`#{0x110000 - 1}`, or a character literal such as `'a'`"
          }
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, value: value}
    )
  end

  defp legacy_contextual_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :projection_not_a_record ->
          {"Record projection requires a record", "This projection was applied to a value that is not a record.",
           "project a field from a record value"}

        :bad_projection ->
          {"Invalid record projection", "This record projection is not valid for the value's type.",
           "use a field declared by the record"}

        :typed_pattern_type_error ->
          {"Pattern annotation does not match",
           "The type annotation on this pattern is incompatible with the value it matches.",
           "change the pattern or its annotation"}

        :unsolved_index ->
          {"Indexed constructor has an unresolved index",
           "Cure could not determine an index required by this constructor.",
           "provide an annotation or make the index explicit"}

        :unsolved_field_type ->
          {"Constructor field type is unresolved", "Cure could not determine the type of a field in this constructor.",
           "add an annotation that determines the field type"}

        :unsolved_parameters ->
          {"Constructor parameters are unresolved",
           "Cure could not determine all parameters required by this constructor.",
           "add an annotation or make the constructor parameters explicit"}
      end

    contextual_failure(kind, details, opts, {title, message, label})
  end

  @doc false
  @spec comparison_doc(term(), term()) :: Doc.t()
  def comparison_doc(expected, actual) do
    {expected_doc, actual_doc} = difference_docs(printable_core(expected), printable_core(actual), false)

    Doc.concat([
      Doc.concat(["Expected: ", expected_doc]),
      Doc.text("\n"),
      Doc.concat(["Found:    ", actual_doc])
    ])
  end

  defp difference_docs(expected, actual, _within_common?) when expected == actual do
    {plain_type_doc(expected), plain_type_doc(actual)}
  end

  defp difference_docs(
         {:data, name, expected_params, expected_indices},
         {:data, name, actual_params, actual_indices},
         _within_common?
       )
       when length(expected_params) == length(actual_params) and length(expected_indices) == length(actual_indices) do
    application_docs(Cure.Elab.Name.base(name), expected_params ++ expected_indices, actual_params ++ actual_indices)
  end

  defp difference_docs({:ctor, name, expected_args}, {:ctor, name, actual_args}, _within_common?)
       when length(expected_args) == length(actual_args) do
    application_docs(Cure.Elab.Name.base(name), expected_args, actual_args)
  end

  defp difference_docs({:app, expected_fun, expected_arg}, {:app, actual_fun, actual_arg}, _within_common?) do
    {expected_fun_doc, actual_fun_doc} = difference_docs(expected_fun, actual_fun, true)
    {expected_arg_doc, actual_arg_doc} = difference_docs(expected_arg, actual_arg, true)

    {
      Doc.concat([expected_fun_doc, Doc.text(" "), expected_arg_doc]),
      Doc.concat([actual_fun_doc, Doc.text(" "), actual_arg_doc])
    }
  end

  defp difference_docs(expected, actual, true) do
    {
      Doc.emphasis(:expected, plain_type_doc(expected)),
      Doc.emphasis(:observed, plain_type_doc(actual))
    }
  end

  defp difference_docs(expected, actual, false),
    do: {plain_type_doc(expected), plain_type_doc(actual)}

  defp application_docs(head, expected_args, actual_args) do
    {expected_args, actual_args} =
      expected_args
      |> Enum.zip(actual_args)
      |> Enum.map(&difference_docs(elem(&1, 0), elem(&1, 1), true))
      |> Enum.unzip()

    {application_doc(head, expected_args), application_doc(head, actual_args)}
  end

  defp application_doc(head, []), do: Doc.text(head)

  defp application_doc(head, args) do
    args_doc = args |> Enum.intersperse(Doc.text(", ")) |> Doc.concat()
    Doc.concat([Doc.text(head), Doc.text("("), args_doc, Doc.text(")")])
  end

  defp plain_type_doc({:diagnostic_alias, name, original}),
    do: Doc.text("#{name} (#{print_core(original)})")

  defp plain_type_doc(type) when is_binary(type), do: Doc.text(type)
  defp plain_type_doc(type), do: Doc.text(print_core(type))

  defp append_dependent_mismatch(blocks, %{dependent_mismatch: mismatch}) when is_map(mismatch) do
    blocks ++ [dependent_mismatch_doc(mismatch)]
  end

  defp append_dependent_mismatch(blocks, _debug), do: blocks

  defp maybe_put_dependent_mismatch(payload, %{dependent_mismatch: mismatch}) when is_map(mismatch) do
    Map.put(payload, :dependent_mismatch, mismatch)
  end

  defp maybe_put_dependent_mismatch(payload, _debug), do: payload

  defp dependent_mismatch_doc(mismatch) do
    scrutinee = surface_type(Map.get(mismatch, :scrutinee, "the branch scrutinee"))
    actual = surface_type(Map.get(mismatch, :actual_subterm, "the actual indexed term"))
    expected = surface_type(Map.get(mismatch, :expected_subterm, "the expected indexed term"))

    detail =
      case Map.get(mismatch, :cause) do
        :missing_equality_transport ->
          "The branch refinement changes this indexed term, but no explicit equality transport connects the two forms."

        :unsolved_metavariable ->
          "The branch refinement is still blocked by an unsolved metavariable; infer or annotate the missing index."

        :failed_branch_refinement ->
          "The constructor branch does not refine the index enough to establish the required result type."

        cause when is_binary(cause) ->
          cause

        _ ->
          "The branch refinement does not establish the required indexed result."
      end

    Doc.paragraph(
      "Dependent mismatch: scrutinee `#{scrutinee}` refines `#{actual}`, but the surrounding branch requires `#{expected}`. #{detail}"
    )
  end

  defp surface_type({:diagnostic_alias, name, original}), do: "#{name} (#{print_core(original)})"
  defp surface_type(type) when is_binary(type), do: type
  defp surface_type(type), do: print_core(type)

  defp print_core(term) do
    term
    |> printable_core()
    |> Cure.Core.Printer.print()
  rescue
    ArgumentError -> inspect(term)
  end

  defp printable_core(term) when is_tuple(term) do
    case elem(term, 0) do
      :diagnostic_alias ->
        term

      :var ->
        term

      tag ->
        case Atom.to_string(tag) do
          "v" <> _ -> Cure.Core.Quote.reify(term, 0)
          _ -> term
        end
    end
  end

  defp printable_core(term), do: term

  defp maybe_put_debug(payload, expected, actual, details, opts) do
    if Keyword.get(opts, :debug, false) do
      Map.put(payload, :debug, %{
        expected_core: inspect(expected),
        actual_core: inspect(actual),
        details: details
      })
    else
      payload
    end
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}

      nil ->
        nil
    end
  end

  defp sentence_case(<<first::utf8, rest::binary>>),
    do: String.upcase(<<first::utf8>>) <> rest

  defp sentence_case(""), do: "Revise this expression"

  defp literal_protocol_mismatch(kind, interface, expected, context, opts) do
    origin = %ExpectationOrigin{
      kind: kind,
      span: Map.get(context, :expectation_span),
      owner: Map.get(context, :checking),
      index: Map.get(context, :argument_index)
    }

    span = Keyword.get(opts, :span, Map.get(context, :span))
    spelling = Map.fetch!(@literal_spellings, interface)
    expected_surface = surface_type(expected)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title(origin),
      body:
        Doc.stack([
          Doc.paragraph(context(origin)),
          Doc.paragraph(
            "This is #{spelling}. A literal takes its value through the expected type's " <>
              "literal protocol, and `#{expected_surface}` has no `#{interface}` " <>
              "implementation, so it cannot be written this way."
          )
        ]),
      primary: if(span, do: %Label{span: span, style: :primary, message: label(origin)}),
      secondary: expectation_labels(origin, span, nil),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      suggestions: [
        %Suggestion{
          message: "Write a `#{expected_surface}` value here, or implement `#{interface}` for `#{expected_surface}`",
          applicability: :manual
        }
      ],
      payload: %{
        expected_surface: expected_surface,
        actual_surface: spelling,
        interface: interface,
        origin: Map.from_struct(origin),
        expression_category: :literal
      }
    )
  end

  defp title(%ExpectationOrigin{kind: :annotation}), do: "Annotation does not match"
  defp title(%ExpectationOrigin{kind: :local_fact}), do: "Local fact does not match"
  defp title(%ExpectationOrigin{kind: :call_result}), do: "Call result has the wrong type"
  defp title(%ExpectationOrigin{kind: :branch}), do: "Branches have different types"
  defp title(%ExpectationOrigin{kind: :dependent_branch}), do: "Dependent branch has the wrong type"
  defp title(%ExpectationOrigin{kind: :condition}), do: "Condition is not boolean"
  defp title(%ExpectationOrigin{kind: :call_argument}), do: "Argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :application}), do: "Application has the wrong type"
  defp title(%ExpectationOrigin{kind: :overload}), do: "No matching overload"
  defp title(%ExpectationOrigin{kind: :element}), do: "Collection element has the wrong type"
  defp title(%ExpectationOrigin{kind: :collection}), do: "Collection elements have different types"
  defp title(%ExpectationOrigin{kind: :record}), do: "Record has the wrong type"
  defp title(%ExpectationOrigin{kind: :record_field}), do: "Record field has the wrong type"
  defp title(%ExpectationOrigin{kind: :record_update}), do: "Record update has the wrong type"
  defp title(%ExpectationOrigin{kind: :pattern}), do: "Pattern has the wrong type"
  defp title(%ExpectationOrigin{kind: :constructor_argument}), do: "Constructor argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :implicit}), do: "Implicit argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :effects}), do: "Effect is not allowed here"
  defp title(%ExpectationOrigin{kind: :ffi}), do: "FFI boundary has the wrong type"
  defp title(%ExpectationOrigin{kind: :actor}), do: "Actor message has the wrong type"
  defp title(%ExpectationOrigin{kind: :fsm}), do: "FSM transition has the wrong type"
  defp title(%ExpectationOrigin{kind: :supervisor}), do: "Supervisor value has the wrong type"
  defp title(%ExpectationOrigin{kind: :operator_operand}), do: "Operator cannot use this value"
  defp title(_origin), do: "Type mismatch"

  defp context(%ExpectationOrigin{kind: :annotation}),
    do: "This expression does not match the type written in its annotation."

  defp context(%ExpectationOrigin{kind: :local_fact, owner: owner}),
    do: "The evidence for local fact `#{name(owner)}` does not match its stated type."

  defp context(%ExpectationOrigin{kind: :call_result, owner: owner}),
    do: "The result of `#{name(owner || "this call")}` does not match the surrounding expectation."

  defp context(%ExpectationOrigin{kind: :branch}),
    do: "Every branch of this expression must produce the same type."

  defp context(%ExpectationOrigin{kind: :dependent_branch}),
    do: "The constructor specializes this branch's indices, and its body must produce that refined result type."

  defp context(%ExpectationOrigin{kind: :condition}),
    do: "A condition must produce `Bool` before either branch can run."

  defp context(%ExpectationOrigin{kind: :call_argument, index: index, owner: owner}),
    do: "Argument #{display_index(index)} of `#{name(owner || "this function")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :application, owner: owner}),
    do: "This application of `#{name(owner || "this function")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :overload, owner: owner}),
    do: "The overloaded call `#{name(owner || "this function")}` has no compatible type."

  defp context(%ExpectationOrigin{kind: :operator_operand, owner: owner}),
    do: "The `#{name(owner || "operator")}` operator cannot use this operand type."

  defp context(%ExpectationOrigin{kind: :element, index: index}),
    do: "Element #{display_index(index)} of this collection has an incompatible type."

  defp context(%ExpectationOrigin{kind: :collection}),
    do: "All elements of this collection must agree on one type."

  defp context(%ExpectationOrigin{kind: :record, owner: owner}),
    do: "This value does not match the declared shape of record `#{name(owner || "this record")}`."

  defp context(%ExpectationOrigin{kind: :record_field, owner: owner}),
    do: "Field `#{name(owner || "this field")}` does not match the record's declared field type."

  defp context(%ExpectationOrigin{kind: :record_update, owner: owner}),
    do: "This record update does not preserve the declared record shape of `#{name(owner || "this record")}`."

  defp context(%ExpectationOrigin{kind: :pattern}),
    do: "This pattern must match the type of the value it is checking."

  defp context(%ExpectationOrigin{kind: :constructor_argument, index: index, owner: owner}),
    do:
      "Argument #{display_index(index)} of constructor `#{name(owner || "this constructor")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :implicit, owner: owner}),
    do: "The implicit argument required by `#{name(owner || "this call")}` has the wrong type."

  defp context(%ExpectationOrigin{kind: :effects}),
    do: "This expression performs an effect that is not allowed in its context."

  defp context(%ExpectationOrigin{kind: :ffi, owner: owner}),
    do: "The FFI boundary `#{name(owner || "this declaration")}` does not match its Cure type."

  defp context(%ExpectationOrigin{kind: :actor, owner: owner}),
    do: "Actor `#{name(owner || "this actor")}` received a value with the wrong message type."

  defp context(%ExpectationOrigin{kind: :fsm, owner: owner}),
    do: "FSM transition `#{name(owner || "this transition")}` does not produce the required state type."

  defp context(%ExpectationOrigin{kind: :supervisor, owner: owner}),
    do: "Supervisor `#{name(owner || "this supervisor")}` does not match the required child specification type."

  defp context(_origin), do: "This expression has a different type than its context requires."

  defp label(%ExpectationOrigin{kind: :condition}), do: "this condition has the wrong type"
  defp label(%ExpectationOrigin{kind: :local_fact}), do: "this evidence has the wrong type"
  defp label(%ExpectationOrigin{kind: :call_result}), do: "this call result has the wrong type"
  defp label(%ExpectationOrigin{kind: :branch}), do: "this branch disagrees with another branch"
  defp label(%ExpectationOrigin{kind: :dependent_branch}), do: "this branch does not satisfy its refined result"
  defp label(%ExpectationOrigin{kind: :call_argument}), do: "this argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :application}), do: "this application has the wrong type"
  defp label(%ExpectationOrigin{kind: :overload}), do: "this overloaded call has no matching type"
  defp label(%ExpectationOrigin{kind: :element}), do: "this collection element has the wrong type"
  defp label(%ExpectationOrigin{kind: :collection}), do: "this collection element has the wrong type"
  defp label(%ExpectationOrigin{kind: :record}), do: "this record has the wrong type"
  defp label(%ExpectationOrigin{kind: :record_field}), do: "this record field has the wrong type"
  defp label(%ExpectationOrigin{kind: :record_update}), do: "this record update has the wrong type"
  defp label(%ExpectationOrigin{kind: :pattern}), do: "this pattern has the wrong type"
  defp label(%ExpectationOrigin{kind: :constructor_argument}), do: "this constructor argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :implicit}), do: "this implicit argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :effects}), do: "this expression has an invalid effect"
  defp label(%ExpectationOrigin{kind: :ffi}), do: "this FFI boundary has the wrong type"
  defp label(%ExpectationOrigin{kind: :actor}), do: "this actor message has the wrong type"
  defp label(%ExpectationOrigin{kind: :fsm}), do: "this FSM transition has the wrong type"
  defp label(%ExpectationOrigin{kind: :supervisor}), do: "this supervisor value has the wrong type"
  defp label(%ExpectationOrigin{kind: :operator_operand}), do: "this operator operand has the wrong type"
  defp label(_origin), do: "this expression has the wrong type"

  defp expectation_labels(%ExpectationOrigin{span: %Span{} = span}, primary_span, _related)
       when span != primary_span,
       do: [%Label{span: span, style: :secondary, message: "the expectation comes from here"}]

  defp expectation_labels(_origin, primary_span, %Span{} = related) when related != primary_span,
    do: [%Label{span: related, style: :secondary, message: "the compared expression is here"}]

  defp expectation_labels(_origin, _primary_span, _related), do: []

  defp display_index(nil), do: ""
  defp display_index(index), do: index + 1

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
