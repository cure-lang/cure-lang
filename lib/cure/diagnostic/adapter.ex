defmodule Cure.Diagnostic.Adapter do
  @moduledoc "Converts phase-specific and legacy error values into shared diagnostics."

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    DefiningEquationProblem,
    ExpectationOrigin,
    InductionProblem,
    Label,
    ProofChainMismatchProblem,
    ProofChainSyntaxProblem,
    RewriteProblem,
    SimplificationProblem,
    Span,
    Suggestion,
    SyntaxProblem,
    TextEdit,
    TypeProblem
  }

  alias Cure.Diagnostic.Adapter.Codegen
  alias Cure.Diagnostic.Adapter.Arity
  alias Cure.Diagnostic.Adapter.Declaration
  alias Cure.Diagnostic.Adapter.Hole
  alias Cure.Diagnostic.Adapter.Kernel, as: KernelAdapter
  alias Cure.Diagnostic.Adapter.Macro, as: MacroAdapter
  alias Cure.Diagnostic.Adapter.Name, as: NameAdapter
  alias Cure.Diagnostic.Adapter.Operational
  alias Cure.Diagnostic.Adapter.Pattern
  alias Cure.Diagnostic.Adapter.Proof, as: ProofAdapter
  alias Cure.Diagnostic.Adapter.Runtime
  alias Cure.Diagnostic.Adapter.StaticAnalysis
  alias Cure.Diagnostic.Adapter.Syntax, as: SyntaxAdapter
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter

  @compile {:nowarn_unused_function, [shadowed_guard_binding_failure: 3, shadowed_sub_union_pattern_failure: 3]}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:error, reason}, opts), do: from_error(reason, opts)

  def from_error({:type_error, errors}, opts) when is_list(errors) do
    from_error(errors, opts)
  end

  def from_error({tag, {package, module_name} = identity, reason}, opts)
      when tag in [
             :module_skeleton_error,
             :module_type_skeleton_failed,
             :module_interface_registration_failed,
             :module_interface_freeze_failed,
             :module_body_check_failed
           ] and is_binary(package) and is_binary(module_name) do
    reason
    |> from_error(opts)
    |> preserve_pipeline_envelope(tag, identity)
  end

  def from_error([reason | _], opts), do: from_error(reason, opts)

  def from_error([], opts) do
    TypeAdapter.empty_type_failure(opts)
  end

  def from_error(
        {:unresolved_global, %{key: {_package, _module, _namespace, name}, closure_path: closure_path} = details},
        opts
      ) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(details, :origin))
      |> Keyword.put(:provenance, Map.get(details, :provenance, []))

    %Diagnostic{} = diagnostic = NameAdapter.from_error({:unknown_global, name, details}, opts)

    %Diagnostic{
      diagnostic
      | payload:
          diagnostic.payload
          |> Map.put(:unresolved_global, details.key)
          |> Map.put(:closure_path, closure_path)
          |> Map.put(:source_context, Map.get(details, :source_context))
    }
  end

  def from_error({:type_mismatch, _, _} = error, opts), do: TypeAdapter.from_error(error, opts)

  def from_error({:unknown_erasure_class, _name, _class} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:erases_on_non_opaque, _name} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:non_strictly_positive, _family} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:erased_used_relevantly, details} = error, opts) when is_map(details),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:usage_violation, details} = error, opts) when is_map(details),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({kind, name}, opts)
      when kind in [
             :duplicate_type,
             :duplicate_ctor,
             :duplicate_constructor,
             :duplicate_field,
             :duplicate_parameter,
             :duplicate_index,
             :reserved_union_type_name,
             :constructor_function_collision,
             :duplicate_definition
           ],
      do: NameAdapter.from_error({kind, name}, opts)

  def from_error({:overlapping_overload, _name, _arity} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:overlapping_overload, %{name: _name, first: _first, second: _second}} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:overlapping_instance, _interface, _head} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:overlapping_instance, %{interface: _interface, head: _head}} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:overlapping_named_instance, _name, _interface, _head} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:overlapping_named_instance, %{name: _name}} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:sibling_module_collision, _name, _owners} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:sibling_module_collision, %{name: _name}} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:precedence_cycle, _groups} = error, opts), do: NameAdapter.from_error(error, opts)
  def from_error({:conflicting_operator_fixity, _details} = error, opts), do: NameAdapter.from_error(error, opts)
  def from_error({:conflicting_precedence_group, _details} = error, opts), do: NameAdapter.from_error(error, opts)

  def from_error({:unsupported_operand_type, _operator} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:no_operator_meaning, _operator} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:cannot_infer_match_type, %{reason: reason}} = error, opts)
      when reason in [:no_constructor_arm, :scrutinee_not_data],
      do: TypeAdapter.from_error(error, opts)

  def from_error({:cannot_infer_match_type, _legacy_expression} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:lambda_expected_pi, %{expected: _expected}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:lambda_expected_pi, _expected} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:unsupported_async, message, meta}, opts)
      when is_binary(message) and is_list(meta),
      do: Runtime.from_error({:unsupported_async, message, meta}, opts)

  def from_error({:unsupported_async, %{primitive: _primitive} = details}, opts),
    do: Runtime.from_error({:unsupported_async, details}, opts)

  def from_error({:splice_outside_quote, tag, meta}, opts) when is_list(meta),
    do: MacroAdapter.from_error({:splice_outside_quote, tag, meta}, opts)

  def from_error({:splice_outside_quote, %{form: tag} = details}, opts)
      when tag in [:splice, :splice_group],
      do: MacroAdapter.from_error({:splice_outside_quote, details}, opts)

  def from_error({:proof_chain_syntax, %ProofChainSyntaxProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:proof_chain_syntax, problem}, opts)

  def from_error({:proof_chain_mismatch, %ProofChainMismatchProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:proof_chain_mismatch, problem}, opts)

  def from_error({:rewrite_failed, %RewriteProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:rewrite_failed, problem}, opts)

  def from_error({:simplification_failed, %SimplificationProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:simplification_failed, problem}, opts)

  def from_error({:induction_failed, %InductionProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:induction_failed, problem}, opts)

  def from_error({:defining_equation_unavailable, %DefiningEquationProblem{} = problem}, opts),
    do: ProofAdapter.from_error({:defining_equation_unavailable, problem}, opts)

  def from_error({:named_argument_mismatch, variant, details}, opts) when is_map(details) do
    NameAdapter.from_error({:named_argument_mismatch, variant, details}, opts)
  end

  def from_error({:missing_diagnosis, points}, opts),
    do: MacroAdapter.validation_failure(:missing_diagnosis, points, opts)

  def from_error({:rule_unpinned, keywords}, opts), do: MacroAdapter.validation_failure(:rule_unpinned, keywords, opts)

  def from_error({:source_context, {:missing_diagnosis, points}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:missing_diagnosis, points, opts, context)

  def from_error({:source_context, {:rule_unpinned, keywords}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:rule_unpinned, keywords, opts, context)

  def from_error({:source_context, {:example_mismatch, mismatches}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:example_mismatch, mismatches, opts, context)

  def from_error({:source_context, {:example_type_mismatch, failures}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:example_type_mismatch, failures, opts, context)

  def from_error({:source_context, {:computed_example_error, failures}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:computed_example_error, failures, opts, context)

  def from_error({:source_context, {:reserved_syntax_field, field, keywords}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:reserved_syntax_field, %{first: field, second: keywords}, opts, context)

  def from_error({:source_context, {:expansion_ill_typed, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: MacroAdapter.expansion_proof_failure(details, context, opts)

  def from_error({:source_context, {:unsupported_hole_type, category}, context}, opts) when is_map(context),
    do: MacroAdapter.validation_failure(:unsupported_hole_type, %{detail: category}, opts, context)

  def from_error({:source_context, {:generated_hole_not_well_typed, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: MacroAdapter.generated_hole_invariant_failure(details, context, opts)

  def from_error({:example_mismatch, mismatches}, opts),
    do: MacroAdapter.validation_failure(:example_mismatch, mismatches, opts)

  def from_error({:example_type_mismatch, failures}, opts),
    do: MacroAdapter.validation_failure(:example_type_mismatch, failures, opts)

  def from_error({:computed_example_error, failures}, opts),
    do: MacroAdapter.validation_failure(:computed_example_error, failures, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_packet_name,
             :invalid_packet_endian,
             :unknown_packet_scalar,
             :missing_packet_endian,
             :invalid_packet_field
           ],
      do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error({kind, field, dependency}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields],
      do: MacroAdapter.from_error({kind, field, dependency}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_packet_field, :invalid_packet_field_name, :duplicate_packet_field],
      do: MacroAdapter.from_error(kind, opts)

  def from_error({:invalid_driver_base, base}, opts),
    do: MacroAdapter.from_error({:invalid_driver_base, base}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_driver_register, :duplicate_driver_register, :overlapping_driver_register],
      do: MacroAdapter.from_error(kind, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_board_name,
             :invalid_board_chip,
             :unknown_board_pin,
             :invalid_board_capability,
             :invalid_board_bus,
             :unknown_bus_pin,
             :missing_bus_capability
           ],
      do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_board_definition,
             :missing_board_chip,
             :invalid_board_pins,
             :invalid_board_capabilities,
             :invalid_board_buses,
             :invalid_board_flash,
             :flash_offset_out_of_bounds
           ],
      do: MacroAdapter.from_error(kind, opts)

  def from_error({:codegen_error, {:computed_macro_error, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:expansion_ill_typed, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_global, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_global, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_name, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_constructor, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:conversion_failure, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:source_context, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unfilled_hole, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:implementation_scope, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:sibling_module_collision, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {kind, _} = reason}, opts)
      when kind in [
             :duplicate_type,
             :duplicate_ctor,
             :duplicate_constructor,
             :duplicate_field,
             :duplicate_parameter,
             :duplicate_index,
             :reserved_union_type_name,
             :constructor_function_collision,
             :duplicate_definition
           ],
      do: from_error(reason, opts)

  def from_error({:codegen_error, {kind, _} = reason}, opts)
      when kind in [
             :proof_chain_mismatch,
             :rewrite_failed,
             :simplification_failed,
             :induction_failed,
             :defining_equation_unavailable
           ],
      do: from_error(reason, opts)

  def from_error({:codegen_error, {:named_argument_mismatch, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:proof_shape_mismatch, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_failure, details}, opts) when is_map(details) do
    Codegen.from_error({:codegen_failure, details}, opts)
  end

  def from_error({:beam_emission_input_missing, module} = reason, opts) do
    Codegen.from_error(
      {:codegen_failure,
       %{
         stage: :canonical_beam_emission,
         module: module,
         reason: reason
       }},
      opts
    )
  end

  def from_error({:beam_emission_failed, module, reason}, opts) do
    Codegen.from_error(
      {:codegen_failure,
       %{
         stage: :canonical_beam_emission,
         module: module,
         reason: reason
       }},
      opts
    )
  end

  def from_error({:codegen_error, reason}, opts), do: Codegen.from_error({:codegen_error, reason}, opts)

  def from_error({:parse_error, [reason | _]}, opts), do: from_error(reason, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_sub_union, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_literal_member, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_as, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_nested, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple_arg, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: reason, name: _name} = details}, context},
        opts
      )
      when reason in [:shadowed_catchall, :shadowed_literal_catchall, :shadowed_default] and is_map(context),
      do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :named_default_nonvariable, name: _name} = details},
         context},
        opts
      )
      when is_map(context),
      do: Pattern.named_default_nonvariable_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :default_in_with, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: Pattern.with_default_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :unlowered_nested_constructor_argument} = details}, context},
        opts
      )
      when is_map(context),
      do: Pattern.unlowered_nested_constructor_failure(details, context, opts)

  def from_error({:source_context, {:unsupported_pattern, shape}, context}, opts) when is_map(context) do
    from_error(
      %SyntaxProblem{
        kind: :unrecognized_pattern,
        observed: shape,
        at: Keyword.get(opts, :span, Map.get(context, :span)),
        context: context
      },
      opts
    )
  end

  def from_error({:source_context, {:unsupported_guard, :non_exhaustive}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :shadowed, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: NameAdapter.shadowed_guard_binding_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :refutable_pattern}}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :complex_scrutinee}}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:unsolved_metavariables, name}, context}, opts) when is_map(context),
    do: TypeAdapter.from_error({:source_context, {:unsolved_metavariables, name}, context}, opts)

  def from_error({:source_context, {:no_instance, _interface, _head}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:constraint_head_not_determined, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:ambiguous_method, method, interfaces}, context}, opts)
      when is_map(context),
      do: NameAdapter.ambiguous_member(method, interfaces, context, opts)

  def from_error({:source_context, {:inconsistent_head_kind, interface}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:inconsistent_head_kind, interface}, context}, opts)

  def from_error({:source_context, {:no_named_instance, name}, context}, opts) when is_map(context),
    do: NameAdapter.from_error({:source_context, {:no_named_instance, name}, context}, opts)

  def from_error({:source_context, {:missing_branch, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error(
        {:source_context, {:tuple_missing_branch, %{branch: _branch}}, context} = error,
        opts
      )
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, :branch_type, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:branch_type, _details}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:reachable_impossible, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:duplicate_branch, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error(
        {:source_context, {:forced_pattern_mismatch, _actual, _expected}, %{forced_pattern_span: _}} = error,
        opts
      ),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:forced_pattern_mismatch, _actual, _expected}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:named_implicit_unforced, name}, %{named_implicit_status: :unforced} = context},
        opts
      ),
      do: TypeAdapter.from_error({:source_context, {:named_implicit_unforced, name}, context}, opts)

  def from_error({:source_context, {:named_implicit_unforced, name}, context}, opts) when is_map(context),
    do: TypeAdapter.from_error({:source_context, {:named_implicit_unforced, name}, context}, opts)

  def from_error({:source_context, {kind, _first, _second}, context} = error, opts)
      when kind == :with_rematch_ctor_mismatch and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {kind, _details}, context} = error, opts)
      when kind in [
             :with_rematch_ctor_mismatch,
             :with_rematch_non_constructor_pattern,
             :with_rematch_inconsistent_binding,
             :with_rematch_unsupported_parent_pattern
           ] and
             is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:with_rematch_arity_mismatch, _expected, _actual}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:unknown_record, name, candidates}, context}, opts)
      when is_map(context) and is_list(candidates),
      do: NameAdapter.from_error({:source_context, {:unknown_record, name, candidates}, context}, opts)

  def from_error({:source_context, {:unknown_record, name}, context}, opts) when is_map(context),
    do: NameAdapter.from_error({:source_context, {:unknown_record, name}, context}, opts)

  def from_error({:source_context, {:unknown_field, _record, _field}, context} = error, opts)
      when is_map(context),
      do: NameAdapter.from_error(error, opts)

  def from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
      when is_map(context) and is_list(available_fields) do
    NameAdapter.from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
  end

  def from_error({:source_context, {:projection_not_a_record, _record}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:dependent_record_projection, _record, _field}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:unknown_field, _record, _field} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_field, _record, _field, available_fields} = error, opts)
      when is_list(available_fields),
      do: NameAdapter.from_error(error, opts)

  def from_error({:source_context, {:projection_non_record, _field}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:unknown_record, name}, opts),
    do: from_error({:source_context, {:unknown_record, name}, %{}}, opts)

  def from_error({:unknown_record, name, candidates}, opts) when is_list(candidates),
    do: from_error({:source_context, {:unknown_record, name, candidates}, %{}}, opts)

  def from_error({:source_context, {:record_field_mismatch, name}, context}, opts)
      when is_map(context) and not is_map(name),
      do: NameAdapter.from_error({:source_context, {:record_field_mismatch, name}, context}, opts)

  def from_error({:source_context, {:record_field_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: NameAdapter.from_error({:source_context, {:record_field_mismatch, details}, context}, opts)

  def from_error({:source_context, {:record_update_base_mismatch, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:foreign_ctor, constructor}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:foreign_ctor, constructor}, context}, opts)

  def from_error({:source_context, {:shadowed_ctor, info}, context} = error, opts)
      when is_map(context) and is_list(info),
      do: NameAdapter.from_error(error, opts)

  def from_error({:shadowed_ctor, info} = error, opts) when is_list(info),
    do: NameAdapter.from_error(error, opts)

  def from_error({:source_context, {kind, _name}, context} = error, opts)
      when kind in [:unknown_ctor, :foreign_ctor, :unknown_pattern_constructor, :unknown_family] and
             is_map(context),
      do: NameAdapter.from_error(error, opts)

  def from_error({:no_such_interface, _interface} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_interface_method, _interface, _method} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_interface_method, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:implementation_scope, %{kind: kind} = details}, opts)
      when kind in [:member_outside, :empty],
      do: NameAdapter.from_error({:implementation_scope, details}, opts)

  def from_error({:missing_method, interface, method}, opts),
    do: NameAdapter.from_error({:missing_method, interface, method}, opts)

  def from_error({:missing_method, %{interface: _interface, method: _method} = details}, opts),
    do: NameAdapter.from_error({:missing_method, details}, opts)

  def from_error({:method_signature_mismatch, interface, method}, opts),
    do: NameAdapter.from_error({:method_signature_mismatch, interface, method}, opts)

  def from_error({:method_signature_mismatch, %{interface: _interface, method: _method} = details}, opts),
    do: NameAdapter.from_error({:method_signature_mismatch, details}, opts)

  def from_error({:instance_head_ill_formed, %{reason: _reason} = details}, opts),
    do: NameAdapter.from_error({:instance_head_ill_formed, details}, opts)

  def from_error({:instance_head_ill_formed, reason}, opts),
    do: NameAdapter.from_error({:instance_head_ill_formed, reason}, opts)

  def from_error({:missing_superinterface, interface, super_interface, head}, opts),
    do: NameAdapter.from_error({:missing_superinterface, interface, super_interface, head}, opts)

  def from_error({:missing_superinterface, %{interface: _interface} = details}, opts),
    do: NameAdapter.from_error({:missing_superinterface, details}, opts)

  def from_error({:union_member_not_ground, member}, opts),
    do: TypeAdapter.from_error({:union_member_not_ground, member}, opts)

  def from_error({:unsupported_member_shape, members}, opts),
    do: TypeAdapter.from_error({:unsupported_member_shape, members}, opts)

  def from_error({:same_runtime_shape, members}, opts),
    do: TypeAdapter.from_error({:same_runtime_shape, members}, opts)

  def from_error({:same_erased_literal, members}, opts),
    do: TypeAdapter.from_error({:same_erased_literal, members}, opts)

  def from_error({:cannot_derive, interface}, opts),
    do: NameAdapter.from_error({:cannot_derive, interface}, opts)

  def from_error({:deriving_needs_strings, interface}, opts),
    do: NameAdapter.from_error({:deriving_needs_strings, interface}, opts)

  def from_error({:deriving_needs_constraints, interface, type_name}, opts),
    do: NameAdapter.from_error({:deriving_needs_constraints, interface, type_name}, opts)

  def from_error({:cannot_derive_shape, interface, type_name}, opts),
    do: NameAdapter.from_error({:cannot_derive_shape, interface, type_name}, opts)

  def from_error({:cannot_derive_method, interface, method, reason}, opts),
    do: NameAdapter.from_error({:cannot_derive_method, interface, method, reason}, opts)

  def from_error({:missing_stdlib_source, source, path}, _opts),
    do: Cure.Diagnostic.Operational.file_read(path || source, :enoent)

  def from_error({:missing_stdlib_source_dir, source}, _opts),
    do: Cure.Diagnostic.Operational.file_read(source, :enoent)

  def from_error({:source_context, {:non_strictly_positive, _constructor}, context} = error, opts)
      when is_map(context),
      do: KernelAdapter.from_error(error, opts)

  def from_error({:source_context, {:erased_used_relevantly, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:usage_violation, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:totality_required, _name}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:compile_time_totality, _name, _reason}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:final_core_violation, name, rejections}, context}, opts)
      when is_list(rejections) and is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:provenance, Map.get(context, :provenance, []))
      |> Keyword.put(:codegen_stage, Map.get(context, :codegen_stage, :final_core_validation))
      |> Keyword.put(:codegen_module, Map.get(context, :codegen_module))

    Codegen.from_error({:final_core_violation, name, rejections}, opts)
  end

  def from_error(
        {:source_context, {:unsupported_expression, {:hole, meta, _children}}, context},
        opts
      )
      when is_list(meta) and is_map(context) do
    Hole.inferred_failure(Keyword.get(meta, :name), context, opts)
  end

  def from_error({:source_context, {:unsafe_call_required, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: contextual_type_failure(:unsafe_call_required, Map.merge(context, details), opts)

  def from_error(
        {:source_context, {:unsupported_expression, expression}, context},
        opts
      )
      when is_map(context) do
    span = unsupported_expression_span(expression) || Map.get(context, :span)

    contextual_type_failure(
      :unsupported_expression,
      %{detail: expression, form: unsupported_expression_form(expression)},
      Keyword.put(opts, :span, span)
    )
  end

  def from_error({:unsafe_call_required, details}, opts) when is_map(details),
    do: contextual_type_failure(:unsafe_call_required, details, opts)

  def from_error({:run_requires_effect, details}, opts) when is_map(details),
    do: contextual_type_failure(:run_requires_effect, details, opts)

  def from_error({:run_arity, actual}, opts),
    do: contextual_type_failure(:run_arity, %{actual: actual}, opts)

  def from_error({:operator_provider_not_in_scope, details}, opts) when is_map(details),
    do: contextual_type_failure(:operator_provider_not_in_scope, details, opts)

  def from_error({:retired_process_type, details}, opts) when is_map(details),
    do:
      contextual_type_failure(
        :retired_process_type,
        details,
        Keyword.put_new(opts, :span, Map.get(details, :span))
      )

  def from_error({:unsupported_expression, expression}, opts) do
    contextual_type_failure(
      :unsupported_expression,
      %{detail: expression, form: unsupported_expression_form(expression)},
      Keyword.put_new(opts, :span, unsupported_expression_span(expression))
    )
  end

  def from_error({:source_context, {kind, _operator}, context} = error, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning] and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {kind, _detail}, context} = error, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ] and
             is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {kind}, context} = error, opts)
      when kind in [:binary_match_needs_default, :map_match_needs_default] and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {kind, _detail}, context} = error, opts)
      when kind in [
             :unsupported_comprehension_pattern,
             :unsupported_binary_generator_pattern,
             :unsupported_binary_segment,
             :unsupported_binary_match_arm,
             :unsupported_map_match_arm,
             :unsupported_map_value_pattern,
             :unsupported_map_key_pattern,
             :unsupported_block_statement,
             :unsupported_block
           ] and is_map(context),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:source_context, {:primitive_missing_builtin, name}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:missing_builtin, %{name: name}, context, opts)

  def from_error({:source_context, {:unknown_primitive_tag, tag}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:unknown_builtin, %{tag: tag}, context, opts)

  def from_error(
        {:source_context, {:primitive_floor_mismatch, name, declared, expected}, context},
        opts
      )
      when is_map(context),
      do:
        primitive_declaration_failure(
          :floor_mismatch,
          %{name: name, declared: primitive_core_tag(declared), expected: primitive_core_tag(expected)},
          context,
          opts
        )

  def from_error({:source_context, {:unsupported_declaration, shape}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:unsupported_declaration, %{shape: shape}, context, opts)

  def from_error({:source_context, {:extern_returns_union, _name, _codomain}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:extern_union_indistinct, _name, _reason}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:bounded_lit_out_of_range, _value, _bound}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:cannot_infer_dependent_match, _inferred_type}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:result_type_not_family, _family}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:typed_pattern_type_mismatch, _type_ast}, %{field_type: field_type}} = error,
        opts
      )
      when not is_nil(field_type),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:typed_pattern_arity, _position}, %{visible_arity: _} = context},
        opts
      ),
      do: Arity.typed_pattern_arity_failure(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_not_in_pattern, _meta},
         %{forced_pattern_position: :positional_constructor_argument}} = error,
        opts
      ),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:applied_non_function, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:telescope_index_out_of_bounds, index, arity}, context} = error,
        opts
      )
      when is_integer(index) and is_integer(arity) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:unknown_erasure_class, _name, _class}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:erases_on_non_opaque, _name}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:effect_binder_erased, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:forced_pattern_not_in_pattern, _meta}, context} = error, opts)
      when is_map(context),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:source_context, {:named_implicit_not_in_pattern, _meta}, context} = error, opts)
      when is_map(context),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:source_context, kind, context} = error, opts)
      when kind in [:rewrite_requires_expected_type, :rewrite_proof_not_equality] and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, :with_mixed_rematch_arms, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, :with_scrutinee_not_data, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, :match_scrutinee_not_data, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:with_indexed_scrutinee_unsupported, _family}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:with_sibling_dependency_unsupported, reason}, context} = error,
        opts
      )
      when reason in [:sibling_references_sibling, :kept_references_sibling] and
             is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:rewrite_no_match, _left, _right}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:rewrite_no_match, _left, _right, _goal}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:cannot_derive, interface}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:cannot_derive, interface}, context}, opts)

  def from_error({:source_context, {:deriving_needs_strings, interface}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:deriving_needs_strings, interface}, context}, opts)

  def from_error({:source_context, {:deriving_needs_constraints, interface, type_name}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:deriving_needs_constraints, interface, type_name}, context}, opts)

  def from_error({:source_context, {:cannot_derive_shape, interface, type_name}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:cannot_derive_shape, interface, type_name}, context}, opts)

  def from_error({:source_context, {:cannot_derive_method, interface, method, reason}, context}, opts)
      when is_map(context),
      do:
        NameAdapter.from_error(
          {:source_context, {:cannot_derive_method, interface, method, reason}, context},
          opts
        )

  def from_error({:source_context, reason, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put(:checking, Map.get(context, :checking))
      |> then(fn opts ->
        case Map.get(context, :span) do
          # A presentation boundary may have remapped this span into its own
          # source registry (for example `Errors.to_diagnostic/3`). Preserve
          # that registry-owned span instead of restoring the compiler's
          # original `nofile` identity.
          %Span{} = span -> Keyword.put_new(opts, :span, span)
          _ -> opts
        end
      end)
      |> then(fn opts ->
        if is_list(Map.get(context, :name_candidates)) do
          opts
          |> Keyword.put(:candidates, Map.get(context, :name_candidates))
          |> Keyword.put(:arity, Map.get(context, :name_arity))
        else
          opts
        end
      end)

    case {reason, Map.get(context, :expectation_origin)} do
      {{:index_mismatch, {:cannot_unify, actual, expected}}, origin} when not is_nil(origin) ->
        contextual_type_problem(:index_mismatch, actual, expected, origin, context, opts)

      {{:cannot_unify, actual, expected}, origin} when not is_nil(origin) ->
        contextual_type_problem(:cannot_unify, actual, expected, origin, context, opts)

      {{:conversion_failure, actual, expected}, origin} when not is_nil(origin) ->
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

      _ ->
        from_error(reason, opts)
    end
  end

  def from_error({:index_mismatch, _details} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:cannot_unify, _actual, _expected} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:escaping_variable, _id} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:hole_in_inference_position, name}, opts),
    do: Hole.inferred_failure(name, %{}, opts)

  def from_error({kind, _detail} = error, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ],
      do: StaticAnalysis.from_error(error, opts)

  def from_error({kind} = error, opts) when kind in [:binary_match_needs_default, :map_match_needs_default],
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:ctor_requires_checking_mode, _family} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:bounded_bound_not_concrete, _bound} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:cyclic_typealiases, aliases}, opts),
    do: NameAdapter.from_error({:cyclic_typealiases, aliases}, opts)

  def from_error({:module_identity_missing, path}, _opts),
    do: Cure.Diagnostic.Operational.file_read(path, :module_identity_missing)

  def from_error({:module_identity_mismatch, requested, declared, path}, opts),
    do: NameAdapter.from_error({:module_identity_mismatch, requested, declared, path}, opts)

  def from_error({:module_path_identity_mismatch, path, declared, requested}, opts),
    do: NameAdapter.from_error({:module_path_identity_mismatch, path, declared, requested}, opts)

  def from_error({:char_literal_needs_bounded, value}, opts),
    do: TypeAdapter.from_error({:char_literal_needs_bounded, value}, opts)

  def from_error({:char_literal_out_of_range, value}, opts),
    do: TypeAdapter.from_error({:char_literal_out_of_range, value}, opts)

  def from_error({:extern_returns_union, _name, _codomain} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:extern_union_indistinct, _name, _reason} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:cannot_infer_dependent_match, branch}, opts),
    do: TypeAdapter.from_error({:cannot_infer_dependent_match, branch}, opts)

  def from_error({:generated_hole_not_well_typed, term}, opts),
    do: MacroAdapter.generated_hole_invariant_failure(%{term: term}, %{}, opts)

  def from_error({:example_use_site_not_fully_consumed, _unused, _ast}, opts),
    do: MacroAdapter.validation_failure(:example_use_site_not_fully_consumed, %{}, opts)

  def from_error({:closed_category_extension, categories}, opts),
    do: MacroAdapter.from_error({:closed_category_extension, categories}, opts)

  def from_error({:ambiguous_macro_extension, keywords}, opts),
    do: MacroAdapter.from_error({:ambiguous_macro_extension, keywords}, opts)

  def from_error({kind, detail}, opts) when kind in [:module_rule_not_fully_consumed, :not_a_module_rule],
    do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error({:invalid_macro_rules, _detail}, opts),
    do: MacroAdapter.family_failure(:invalid_macro_rules, opts)

  def from_error({kind, detail}, opts)
      when not is_map(detail) and
             kind in [
               :unknown_syntax_family,
               :duplicate_syntax_family,
               :duplicate_syntax_family_field,
               :syntax_family_cycle
             ],
      do: MacroAdapter.family_failure({kind, detail}, opts)

  def from_error({:duplicate_unit, suffix}, opts),
    do: MacroAdapter.from_error({:duplicate_unit, suffix}, opts)

  def from_error({kind, detail}, opts)
      when kind in [:invalid_unit, :unknown_unit],
      do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error({:invalid_unit_literal, value, suffix}, opts),
    do: MacroAdapter.from_error({:invalid_unit_literal, value, suffix}, opts)

  def from_error({:invalid_check_name, name}, opts),
    do: MacroAdapter.from_error({:invalid_check_name, name}, opts)

  def from_error({:invalid_protocol_name, name}, opts),
    do: MacroAdapter.from_error({:invalid_protocol_name, name}, opts)

  def from_error({:protocol_role_count, count}, opts),
    do: MacroAdapter.from_error({:protocol_role_count, count}, opts)

  def from_error({kind, role}, opts)
      when kind in [:self_protocol_step, :unknown_choice_decider, :invalid_protocol_branches, :unprojectable_choice],
      do: MacroAdapter.from_error({kind, role}, opts)

  def from_error({:unknown_protocol_role, sender, receiver}, opts),
    do: MacroAdapter.from_error({:unknown_protocol_role, sender, receiver}, opts)

  def from_error({:invalid_parse_name, name}, opts),
    do: MacroAdapter.from_error({:invalid_parse_name, name}, opts)

  def from_error({:left_recursive_parse_production, names}, opts),
    do: MacroAdapter.from_error({:left_recursive_parse_production, names}, opts)

  def from_error({:missing_raw_delimiter, delimiter}, opts),
    do: MacroAdapter.from_error({:missing_raw_delimiter, delimiter}, opts)

  def from_error({:invalid_raw_delimiter, delimiter}, opts),
    do: MacroAdapter.from_error({:invalid_raw_delimiter, delimiter}, opts)

  def from_error({kind, path}, opts)
      when kind in [
             :raw_syntax_in_expansion,
             :quoted_syntax_in_expansion,
             :malformed_expansion_syntax,
             :malformed_expansion_attribute,
             :malformed_expansion_map,
             :malformed_expansion_literal,
             :malformed_reflected_syntax,
             :malformed_reflected_attribute,
             :malformed_reflected_map,
             :malformed_reflected_literal
           ],
      do: MacroAdapter.from_error({kind, path}, opts)

  def from_error({:invalid_syntax_node, attrs, kids}, opts),
    do: MacroAdapter.from_error({:invalid_syntax_node, attrs, kids}, opts)

  def from_error({:invalid_syntax_node, detail}, opts),
    do: MacroAdapter.from_error({:invalid_syntax_node, detail}, opts)

  def from_error({:invalid_syntax_leaf, tag}, opts),
    do: MacroAdapter.from_error({:invalid_syntax_leaf, tag}, opts)

  def from_error({:invalid_syntax_failure, name}, opts),
    do: MacroAdapter.from_error({:invalid_syntax_failure, name}, opts)

  def from_error({:unsupported_syntax_core, term}, opts),
    do: MacroAdapter.from_error({:unsupported_syntax_core, term}, opts)

  def from_error({:invalid_syntax_attrs, core}, opts),
    do: MacroAdapter.from_error({:invalid_syntax_attrs, core}, opts)

  def from_error({kind, _detail}, opts) when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
    do: MacroAdapter.from_error({kind, :detail}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_macro_segment,
             :unsupported_surface_filler,
             :missing_hole_filler,
             :invalid_repeated_hole_filler
           ],
      do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: MacroAdapter.from_error({kind, detail}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_lift_module,
             :invalid_lift_module_name,
             :invalid_lift_callback,
             :invalid_module_name,
             :invalid_behaviour,
             :lifted_module_dependency_cycle,
             :duplicate_lifted_module
           ],
      do: MacroAdapter.lift_module_validation(kind, %{detail: detail}, opts)

  def from_error({:unknown_reducer_constructor, constructors}, opts),
    do: MacroAdapter.from_error({:unknown_reducer_constructor, constructors}, opts)

  def from_error({:incomplete_reducer, constructors}, opts),
    do: MacroAdapter.from_error({:incomplete_reducer, constructors}, opts)

  # Some trusted checking paths can return the bare verdict after their
  # declaration wrapper has been stripped. Keep that verdict contextual rather
  # than falling through to the unhelpful generic "Elaboration failed" title.
  def from_error(:branch_type, opts), do: TypeAdapter.from_error(:branch_type, opts)

  def from_error({kind, detail}, opts)
      when not is_map(detail) and
             kind in [
               :invalid_packet_name,
               :invalid_packet_endian,
               :unknown_packet_scalar,
               :missing_packet_endian,
               :forward_packet_length,
               :invalid_packet_crc_fields,
               :invalid_packet_field,
               :invalid_packet_field_name,
               :duplicate_packet_field,
               :invalid_driver_base,
               :invalid_driver_register,
               :duplicate_driver_register,
               :overlapping_driver_register,
               :unsupported_hole_type,
               :invalid_generated_syntax
             ],
      do: MacroAdapter.validation_failure(kind, %{detail: detail}, opts)

  def from_error({kind, first, second}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields, :reserved_syntax_field],
      do: MacroAdapter.validation_failure(kind, %{first: first, second: second}, opts)

  # C2/Core artifact decoding is an untrusted boundary. Its failures are
  # operational artifact diagnostics, not kernel terms to expose in default
  # output. The detail is retained only as machine/debug data by the
  # operational converter.
  def from_error({:bad_grade, grade}, _opts),
    do:
      Operational.artifact_error("Core artifact contains an invalid relevance grade", %{kind: :bad_grade, grade: grade})

  def from_error({:unknown_symbol, symbol}, _opts),
    do: Operational.artifact_error("Core artifact contains an unknown symbol", %{kind: :unknown_symbol, symbol: symbol})

  def from_error({:ill_formed_term, term}, _opts),
    do: Operational.artifact_error("Core artifact contains an ill-formed term", %{kind: :ill_formed_term, term: term})

  def from_error({:reducer_arity, constructor, actual, expected}, opts),
    do: MacroAdapter.from_error({:reducer_arity, constructor, actual, expected}, opts)

  def from_error({:primitive_missing_builtin, name}, opts),
    do: primitive_declaration_failure(:missing_builtin, %{name: name}, %{}, opts)

  def from_error({:unknown_primitive_tag, tag}, opts),
    do: primitive_declaration_failure(:unknown_builtin, %{tag: tag}, %{}, opts)

  def from_error({:primitive_floor_mismatch, name, declared, expected}, opts),
    do:
      primitive_declaration_failure(
        :floor_mismatch,
        %{name: name, declared: primitive_core_tag(declared), expected: primitive_core_tag(expected)},
        %{},
        opts
      )

  def from_error({:unsupported_declaration, shape}, opts),
    do: primitive_declaration_failure(:unsupported_declaration, %{shape: shape}, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :bounded_family_unregistered,
             :absurd_in_reachable_position,
             :opaque_not_eliminable,
             :case_scrutinee_not_data,
             :not_total,
             :not_a_function,
             :coverage,
             :branch_arity,
             :index_arity
           ],
      do: contextual_type_failure(kind, %{}, opts)

  def from_error({:applied_non_function, details} = error, opts) when is_map(details),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:effect_binder_erased, details} = error, opts) when is_map(details),
    do: TypeAdapter.from_error(error, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_driver_register,
             :duplicate_driver_register,
             :overlapping_driver_register
           ],
      do: MacroAdapter.validation_failure(kind, %{}, opts)

  def from_error(kind, opts) when kind in [:no_compatible_macro_input, :normalization_fuel_exhausted],
    do: from_error({:computed_macro_error, [], kind}, opts)

  def from_error(kind, opts) when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
    do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [:not_a_nat, :invalid_macro_fuzz_rule, :invalid_macro_fuzz_bindings],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts) when kind in [:invalid_check_property, :duplicate_check_property],
    do: MacroAdapter.from_error(kind, opts)

  def from_error(:invalid_raw_tokens, opts), do: MacroAdapter.from_error(:invalid_raw_tokens, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_lift_module_ast,
             :invalid_lift_callback,
             :invalid_lift_declaration,
             :invalid_lift_import,
             :invalid_lift_inheritance
           ],
      do: MacroAdapter.lift_module_validation(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :module_rule_not_fully_consumed,
             :not_a_module_rule,
             :invalid_module_rule_set,
             :invalid_module_rule_bindings,
             :invalid_macro_extension_rules,
             :invalid_macro_extension_rule
           ],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_macro_rules,
             :expander_without_accepts,
             :accepts_without_syntax_family,
             :accepts_without_expander,
             :multiple_accepts_declarations,
             :multiple_expands_declarations
           ],
      do: MacroAdapter.family_failure(kind, opts)

  def from_error(kind, opts)
      when kind in [:invalid_parse_productions, :invalid_parse_production, :duplicate_parse_production],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [:invalid_reducer_arms, :invalid_reducer_arm, :duplicate_reducer_constructor],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_protocol_roles,
             :invalid_protocol_role,
             :duplicate_protocol_role,
             :invalid_protocol_steps,
             :invalid_protocol_step,
             :invalid_protocol_message,
             :invalid_protocol_options,
             :invalid_protocol_choices,
             :invalid_protocol_choice
           ],
      do: MacroAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [
             :rewrite_requires_expected_type,
             :rewrite_proof_not_equality
           ],
      do: TypeAdapter.from_error(kind, opts)

  def from_error(kind, opts)
      when kind in [
             :applied_non_function,
             :match_scrutinee_not_data,
             :with_mixed_rematch_arms,
             :with_scrutinee_not_data,
             :too_few_arguments,
             :too_many_arguments,
             :nonvariable_scrutinee
           ],
      do: contextual_type_failure(kind, %{}, opts)

  def from_error(:shadowed, opts),
    do: NameAdapter.from_error(:shadowed, opts)

  def from_error(kind, opts)
      when kind in [
             :arg_arity,
             :ctor_arity,
             :domain_mismatch,
             :grade_mismatch,
             :bad_motive,
             :not_a_type,
             :not_a_type_value,
             :index_mismatch,
             :universe_level,
             :universe_ceiling,
             :hole_in_inference_position,
             :ctor_requires_checking_mode,
             :bounded_bound_not_concrete
           ],
      do: KernelAdapter.from_error(kind, opts)

  def from_error({:occurs_check, _id, _term} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:no_instance, _interface, _head} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:constraint_head_not_determined, details} = error, opts) when is_map(details),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:ambiguous_instance_for_expected_type, interface, expected}, opts),
    do: TypeAdapter.from_error({:ambiguous_instance_for_expected_type, interface, expected}, opts)

  def from_error({:no_matching_overload, _name, _arguments} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:no_matching_overload, %{name: _name}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:label_mismatch, key, declared, written}, opts),
    do:
      contextual_type_failure(
        :label_mismatch,
        %{key: key, declared: declared, written: written},
        opts
      )

  def from_error({:ambiguous_overload, _name, _owners} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:ambiguous_method, method, interfaces}, opts),
    do: NameAdapter.ambiguous_member(method, interfaces, opts)

  def from_error({:projection_not_a_record, record}, opts),
    do: TypeAdapter.from_error({:projection_not_a_record, record}, opts)

  def from_error({:bad_projection, details}, opts),
    do: TypeAdapter.from_error({:bad_projection, details}, opts)

  def from_error({:typed_pattern_arity, position}, opts),
    do: Arity.from_error({:typed_pattern_arity, position}, opts)

  def from_error({:typed_pattern_type_error, reason}, opts),
    do: TypeAdapter.from_error({:typed_pattern_type_error, reason}, opts)

  def from_error({:unsolved_index, constructor}, opts),
    do: TypeAdapter.from_error({:unsolved_index, constructor}, opts)

  def from_error({:unsolved_field_type, constructor}, opts),
    do: TypeAdapter.from_error({:unsolved_field_type, constructor}, opts)

  def from_error({:forced_pattern_not_in_pattern, _meta} = error, opts),
    do: SyntaxAdapter.from_error(error, opts)

  def from_error({:named_implicit_not_in_pattern, _meta} = error, opts),
    do: SyntaxAdapter.from_error(error, opts)

  def from_error({:unsolved_parameters, constructor}, opts),
    do: TypeAdapter.from_error({:unsolved_parameters, constructor}, opts)

  def from_error({:untyped_parameter, %{name: _name}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:graded_let_needs_annotation, %{name: _name}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:let_needs_annotation, %{name: _name}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:typealias_not_a_type, %{name: _name, actual_type: _actual}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:typealias_not_a_type, _name, _actual_type} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({kind, _detail} = error, opts)
      when kind in [
             :untyped_parameter,
             :let_needs_annotation,
             :graded_let_needs_annotation,
             :typealias_not_a_type
           ],
      do: TypeAdapter.from_error(error, opts)

  def from_error({:result_type_not_family, _detail} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :unsupported_expression,
             :unsupported_pattern,
             :unsupported_guard,
             :binary_match_needs_default,
             :map_match_needs_default,
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern,
             :constructor_result_mismatch,
             :dependent_record_projection,
             :with_indexed_scrutinee_unsupported,
             :with_rematch_unsupported_parent_pattern,
             :with_sibling_dependency_unsupported,
             :telescope_index_out_of_bounds,
             :effect_binder_erased
           ],
      do: contextual_type_failure(kind, %{detail: detail}, opts)

  def from_error({:effect_arity, name, expected, actual}, opts),
    do: TypeAdapter.from_error({:effect_arity, name, expected, actual}, opts)

  def from_error({kind, details} = error, opts)
      when kind in [
             :bad_result_type,
             :non_integer_index,
             :unsupported_index_literal,
             :unsupported_index_expr,
             :unsupported_index_operator,
             :sigma_projection_needs_ctx
           ] and is_map(details),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({kind, _detail} = error, opts)
      when kind in [
             :unsupported_comprehension_pattern,
             :unsupported_binary_generator_pattern,
             :unsupported_binary_segment,
             :unsupported_binary_match_arm,
             :unsupported_map_match_arm,
             :unsupported_map_value_pattern,
             :unsupported_map_key_pattern,
             :unsupported_block_statement,
             :unsupported_block
           ],
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({kind, _name} = error, opts)
      when kind in [:unknown_global, :unbound_var, :unknown_family, :unknown_ctor, :foreign_ctor, :unknown_constructor],
      do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_global, _name, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_name, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unfilled_hole, details}, opts) when is_map(details),
    do: Hole.from_error({:unfilled_hole, details}, opts)

  def from_error({:unfilled_hole, _name} = error, opts), do: Hole.from_error(error, opts)

  def from_error({:arity_mismatch, _, _} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:extern_arity_mismatch, _, _, _} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:call_arity_mismatch, _details} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:extern_arity_mismatch, %{name: _name} = _details} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:constructor_arity_mismatch, %{name: _name} = _details} = error, opts),
    do: Arity.from_error(error, opts)

  def from_error({:constructor_arity_mismatch, _name} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:pattern_arity_mismatch, %{constructor: _} = _details} = error, opts),
    do: Arity.from_error(error, opts)

  def from_error({:tuple_arity_mismatch, _, _} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:with_rematch_arity_mismatch, _, _} = error, opts), do: Arity.from_error(error, opts)

  def from_error({:typed_pattern_type_mismatch, _type_ast} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:extern_untyped_head, _, _} = error, opts), do: Declaration.from_error(error, opts)
  def from_error({:extern_has_body, _, _} = error, opts), do: Declaration.from_error(error, opts)

  def from_error({:proof_shape_mismatch, _, _} = error, opts), do: ProofAdapter.from_error(error, opts)
  def from_error({:ambiguous_proof_search, _, _} = error, opts), do: ProofAdapter.from_error(error, opts)

  def from_error({:totality_required, _name} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:compile_time_totality, _name, _reason} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:totality_closure_unresolved, details} = error, opts) when is_map(details),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({kind, details} = error, opts)
      when kind in [
             :totality_summary_stale,
             :totality_scc_incomplete,
             :totality_scc_invalid,
             :totality_matrix_invalid,
             :totality_derivation_invalid,
             :totality_dependency_not_total,
             :totality_unknown_callee
           ] and is_map(details),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:pickup_no_else, _details} = error, opts), do: StaticAnalysis.from_error(error, opts)

  def from_error({:pickup_else_not_last, _details} = error, opts), do: StaticAnalysis.from_error(error, opts)

  def from_error({:pickup_multiple_else, _details} = error, opts), do: StaticAnalysis.from_error(error, opts)

  def from_error({kind, _, _} = error, opts)
      when kind in [:pickup_no_else, :pickup_else_not_last, :pickup_multiple_else],
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:ambiguous_name, _name, _modules} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:duplicate_module, _name, _paths} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:duplicate_module_identity, name, other_path, path}, opts) do
    NameAdapter.from_error({:duplicate_module_identity, name, other_path, path}, opts)
  end

  def from_error({:duplicate_module_identity, name, paths}, opts) when is_list(paths) do
    NameAdapter.from_error({:duplicate_module_identity, name, paths}, opts)
  end

  def from_error({:import_cycle, _hops} = error, opts), do: NameAdapter.from_error(error, opts)

  def from_error(%TypeProblem{} = problem, opts) do
    TypeAdapter.from_error(problem, opts)
  end

  def from_error(%SyntaxProblem{} = problem, opts) do
    span = problem.at || Keyword.get(opts, :span)
    code = Map.get(problem.context, :code, syntax_problem_code(problem.kind))

    primary =
      if span do
        %Label{span: span, style: :primary, message: syntax_problem_label(problem)}
      end

    Diagnostic.new(
      code: code,
      key: problem.kind,
      severity: :error,
      title: syntax_problem_title(problem),
      body:
        Doc.stack([
          Doc.paragraph(syntax_problem_context(problem)),
          syntax_expected_doc(problem)
        ]),
      primary: primary,
      secondary: syntax_secondary_labels(problem, span),
      suggestions: syntax_insertions(problem, span),
      payload: %{
        kind: problem.kind,
        expected: problem.expected,
        alternatives: problem.alternatives,
        observed: problem.observed,
        at: problem.at,
        within: problem.within,
        opener: problem.opener,
        previous: problem.previous,
        context: problem.context
      }
    )
  end

  def from_error({:conversion_failure, _actual, _expected} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:expected, expected, :got, actual, line, column, %Span{} = span}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        expected: expected,
        observed: actual,
        at: Keyword.get(opts, :span, span),
        context: %{line: line, column: column}
      },
      opts
    )
  end

  def from_error({:expected_token, expected, actual_type, actual_value, line, column, %Span{} = span}, opts) do
    from_error(
      %SyntaxProblem{
        kind: missing_delimiter_kind(expected, actual_type),
        expected: expected,
        observed: if(is_nil(actual_value), do: actual_type, else: actual_value),
        at: Keyword.get(opts, :span, span),
        context: %{line: line, column: column, token_type: actual_type}
      },
      opts
    )
  end

  def from_error({:expected_literal_capture, _details} = error, opts), do: MacroAdapter.from_error(error, opts)

  def from_error({:unknown_syntax_family_field, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:missing_syntax_family_field, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:unknown_macro_obligation_capture, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:graded_let_requires_variable, details} = error, opts)
      when is_map(details),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:unknown_grade, details} = error, opts)
      when is_map(details),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:grade_requires_type, details} = error, opts)
      when is_map(details),
      do: SyntaxAdapter.from_error(error, opts)

  def from_error({:unit_type_reserved, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:duplicate_syntax_family_field, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:non_associative, details}, opts) when is_map(details),
    do:
      from_error(
        %SyntaxProblem{
          kind: :non_associative,
          observed: details.next_operator,
          at: Map.get(details, :span) || Keyword.get(opts, :span),
          previous: Map.get(details, :operator_span),
          context: details
        },
        opts
      )

  def from_error({:ambiguous_precedence, details}, opts) when is_map(details),
    do:
      from_error(
        %SyntaxProblem{
          kind: :ambiguous_precedence,
          observed: details.operator,
          at: Map.get(details, :span) || Keyword.get(opts, :span),
          previous: Map.get(details, :operator_span),
          context: details
        },
        opts
      )

  def from_error({:with_multi_proof_unsupported, message}, opts),
    do: contextual_type_failure(:with_multi_proof_unsupported, %{message: message}, opts)

  def from_error({:with_multi_rematch_unsupported, message}, opts),
    do: contextual_type_failure(:with_multi_rematch_unsupported, %{message: message}, opts)

  def from_error({:with_multi_arity_mismatch, message}, opts),
    do: contextual_type_failure(:with_multi_arity_mismatch, %{message: message}, opts)

  def from_error({:with_multi_proof_unsupported, message, meta}, opts),
    do: contextual_type_failure(:with_multi_proof_unsupported, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_rematch_unsupported, message, meta}, opts),
    do: contextual_type_failure(:with_multi_rematch_unsupported, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_arity_mismatch, message, meta}, opts),
    do: contextual_type_failure(:with_multi_arity_mismatch, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_no_arms, message, meta}, opts),
    do: contextual_type_failure(:with_multi_no_arms, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_inconsistent_pattern, message, meta}, opts),
    do: contextual_type_failure(:with_multi_inconsistent_pattern, %{message: message, meta: meta}, opts)

  def from_error({:unexpected_token, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.get(details, :kind, :unexpected_token),
        expected: Map.get(details, :expected),
        observed: details.observed,
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        context: details
      },
      opts
    )
  end

  def from_error({:missing_function_body, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :missing_function_body,
        expected: :expression,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        context: details
      },
      opts
    )
  end

  def from_error({:function_parameters_unparenthesized, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :function_parameters_unparenthesized,
        expected: :lparen,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :name_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_parameters_unparenthesized, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :lambda_parameters_unparenthesized,
        expected: :lparen,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :lambda_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_arrow_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :lambda_arrow_missing,
        expected: :arrow,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :lambda_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:branch_arrow_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :branch_arrow_missing,
        expected: Map.get(details, :expected, :arrow),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:proof_command_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:macro_check_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:macro_rule_separator_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:syntax_family_definition_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        alternatives: Map.get(details, :alternatives, []),
        context: details
      },
      opts
    )
  end

  def from_error({:syntax_family_body_syntax, details}, opts) when is_map(details) do
    valid_fields = Map.get(details, :valid_fields, [])
    expected = Map.get(details, :expected) || List.first(valid_fields)

    alternatives =
      if Map.get(details, :kind) == :syntax_family_entry_invalid,
        do: Enum.drop(valid_fields, 1),
        else: []

    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: expected,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :previous_span),
        alternatives: alternatives,
        context: details
      },
      opts
    )
  end

  def from_error({:macro_nested_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        alternatives: Map.get(details, :alternatives, []),
        context: details
      },
      opts
    )
  end

  def from_error({:refinement_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:sigma_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:declaration_separator_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:indexed_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:invalid_parameter_name, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :invalid_parameter_name,
        expected: :identifier,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        context: details
      },
      opts
    )
  end

  def from_error({:variadic_parameter_name_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :variadic_parameter_name_missing,
        expected: :identifier,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :marker_span),
        context: details
      },
      opts
    )
  end

  def from_error({:call_arguments_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:container_elements_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_block_unterminated, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :unterminated_lambda,
        expected: Map.get(details, :expected, :end),
        observed: Map.get(details, :observed, :eof),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lex_error, reason}, opts), do: from_error(lex_problem(reason, opts), opts)

  def from_error({:macro_use_mismatch, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :macro_use_mismatch,
        expected: details.expected,
        observed: details.got,
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :invocation_span),
        within: Map.get(details, :definition_span),
        alternatives: [],
        context: details
      },
      opts
    )
  end

  def from_error({:malformed_hole, _details} = error, opts), do: SyntaxAdapter.from_error(error, opts)

  def from_error({:edition_pragma_placement, _details} = error, opts), do: SyntaxAdapter.from_error(error, opts)

  def from_error({:edition_pragma_malformed, _details} = error, opts), do: SyntaxAdapter.from_error(error, opts)

  def from_error({:edition_pragma_unknown, _details} = error, opts), do: SyntaxAdapter.from_error(error, opts)

  def from_error({kind, line, column}, opts)
      when kind in [:edition_pragma_placement, :edition_pragma_malformed, :edition_pragma_unknown] and
             is_integer(line) and is_integer(column) do
    from_error(
      %SyntaxProblem{
        kind: kind,
        observed: :edition_pragma,
        at: Keyword.get(opts, :span),
        context: %{column: column}
      },
      opts
    )
  end

  def from_error({:edition_error, {:unknown_edition, _edition}} = error, opts),
    do: SyntaxAdapter.from_error(error, opts)

  def from_error({:computed_macro_error, meta, reason}, opts) when is_list(meta),
    do: MacroAdapter.computed_macro_error(meta, reason, opts)

  def from_error({:invalid_macro_family, details}, opts) when is_map(details),
    do: MacroAdapter.from_error({:invalid_macro_family, details}, opts)

  def from_error({:macro_expansion_cycle, chain} = error, opts)
      when is_list(chain),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:macro_expansion_budget, kind, frames} = error, opts)
      when is_atom(kind) and is_list(frames),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:expansion_ill_typed, details} = error, opts)
      when is_map(details),
      do: MacroAdapter.from_error(error, opts)

  def from_error({:beam_lint_error, errors, warnings}, opts) do
    Codegen.from_error({:beam_lint_error, errors, warnings}, opts)
  end

  def from_error({:beam_lint_error, errors}, opts) do
    Codegen.from_error({:beam_lint_error, errors}, opts)
  end

  def from_error({:final_core_violation, rejections}, opts) when is_list(rejections) do
    Codegen.from_error({:final_core_violation, rejections}, opts)
  end

  def from_error({:final_core_violation, name, rejections}, opts) when is_list(rejections) do
    Codegen.from_error({:final_core_violation, name, rejections}, opts)
  end

  def from_error({:expected_module, _ast} = error, opts), do: Codegen.from_error(error, opts)
  def from_error({:unsupported_container, _type} = error, opts), do: Codegen.from_error(error, opts)
  def from_error({:cannot_emit, _reason} = error, opts), do: Codegen.from_error(error, opts)

  def from_error({:inconsistent_head_kind, name}, opts),
    do: NameAdapter.from_error({:inconsistent_head_kind, name}, opts)

  def from_error({:lift_module_error, details}, opts) when is_map(details),
    do: MacroAdapter.lift_module_error(details, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :bad_result_type,
             :non_integer_index,
             :unsupported_index_literal,
             :unsupported_index_expr,
             :unsupported_index_operator,
             :sigma_projection_needs_ctx,
             :unknown_macro_failure,
             :unsolved_metavariable_in_type,
             :lambda_expected_pi
           ],
      do: contextual_type_failure(kind, %{detail: detail}, opts)

  def from_error({:rewrite_no_match, _first, _second} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:non_uniform_parameter, first, second}, opts),
    do: contextual_type_failure(:non_uniform_parameter, %{first: first, second: second}, opts)

  def from_error({:non_uniform_parameter, details}, opts) when is_map(details),
    do: contextual_type_failure(:non_uniform_parameter, details, opts)

  def from_error({:rewrite_no_match, _first, _second, _goal} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:bounded_lit_out_of_range, _value, _bound} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp preserve_pipeline_envelope(%Diagnostic{} = diagnostic, tag, identity) do
    stage =
      case tag do
        :module_skeleton_error -> :module_skeleton
        :module_type_skeleton_failed -> :type_skeleton
        :module_interface_registration_failed -> :interface_registration
        :module_interface_freeze_failed -> :interface_freeze
        :module_body_check_failed -> :body_check
      end

    context = %{pipeline_stage: stage, module_identity: identity}

    %Diagnostic{
      diagnostic
      | payload: Map.merge(diagnostic.payload || %{}, context),
        notes:
          diagnostic.notes ++
            [Doc.paragraph("While checking canonical module `#{elem(identity, 1)}` during #{stage}.")]
    }
  end

  defp contextual_type_problem(kind, actual, expected, origin, context, opts) do
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

  @doc false
  def operator_conflict(kind, details, opts), do: NameAdapter.operator_conflict(kind, details, opts)

  @doc false
  def operator_conflict_labels(spans, opts, primary_message, secondary_message),
    do: NameAdapter.operator_conflict_labels(spans, opts, primary_message, secondary_message)

  defp primitive_declaration_failure(kind, details, context, opts) do
    Declaration.primitive_declaration_failure(kind, details, context, opts)
  end

  defp primitive_core_tag({:float_type}), do: :float
  defp primitive_core_tag({:binary_type}), do: :binary
  defp primitive_core_tag({:atom_type}), do: :atom
  defp primitive_core_tag(other) when is_atom(other), do: other
  defp primitive_core_tag(_other), do: :unknown

  defp overload_type_surface(type) when is_atom(type) or is_binary(type),
    do: name_to_string(Cure.Elab.Name.base(type) || type)

  defp overload_type_surface(type), do: surface_type(type)

  @doc false
  def overload_declaration_signature(name, member) do
    parameters = Enum.map_join(Map.get(member, :parameters, []), ", ", &overload_type_surface/1)
    "#{name}(#{parameters})"
  end

  @doc false
  def shadowed_guard_binding_failure(details, context, opts),
    do: NameAdapter.shadowed_guard_binding_failure(details, context, opts)

  @doc false
  def shadowed_sub_union_pattern_failure(details, context, opts),
    do: NameAdapter.shadowed_sub_union_pattern_failure(details, context, opts)

  defp contextual_type_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :non_uniform_parameter ->
          family = name_to_string(Map.get(details, :family, :type))
          constructor = name_to_string(Map.get(details, :ctor, :constructor))
          position = Map.get(details, :position, :unknown)

          {"Constructor changes a type parameter",
           "The constructor `#{constructor}` does not return the family `#{family}` with parameter #{position} unchanged. Parameters must be uniform across every constructor result; values that vary belong in the `indices` telescope.",
           "return the declared parameter unchanged or make it an index"}

        :no_instance ->
          {"No instance found",
           "Cure could not find an implementation of `#{name_to_string(details.interface)}` for the required type `#{surface_type(details.head)}`.",
           "add or import an instance for this type"}

        :ambiguous_instance ->
          {"Instance resolution is ambiguous",
           "More than one `#{name_to_string(details.interface)}` instance can satisfy this expected type.",
           "make the instance selection unambiguous"}

        :no_matching_overload ->
          {"No matching overload",
           "No overload of `#{name_to_string(details.name)}` accepts the argument types at this call site.",
           "change the arguments or choose a different overload"}

        :label_mismatch ->
          {"Argument label mismatch",
           "The argument label `#{name_to_string(details.key)}` does not match the labels declared by this overload.",
           "use the declared argument label"}

        :ambiguous_overload ->
          {"Overload resolution is ambiguous",
           "More than one overload of `#{name_to_string(details.name)}` matches this call.",
           "add an annotation or qualify the overload"}

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

        :forced_pattern_not_in_pattern ->
          {"Forced pattern is unavailable", "This forced pattern refers to a name that is not bound by the pattern.",
           "bind the name in the pattern before forcing it"}

        :named_implicit_not_in_pattern ->
          {"Named implicit is unavailable", "This named implicit is not bound by the surrounding pattern.",
           "bind the implicit in the pattern or remove the reference"}

        :unsolved_parameters ->
          {"Constructor parameters are unresolved",
           "Cure could not determine all parameters required by this constructor.",
           "add an annotation or make the constructor parameters explicit"}

        :unsupported_expression ->
          case Map.get(details, :form, :expression) do
            :expression ->
              {"Unsupported expression", "Cure does not support this expression in the current elaboration context.",
               "rewrite this expression using a supported form"}

            form ->
              form = name_to_string(form)

              {"Unsupported #{form} expression",
               "Cure does not support this `#{form}` expression in the current elaboration context.",
               "rewrite this `#{form}` expression using a supported form"}
          end

        :operator_provider_not_in_scope ->
          operator = name_to_string(details.operator)

          {"Operator provider is not in scope",
           "The `#{operator}` operator dispatches through `#{details.provider}.#{details.method}/2`, but `#{details.provider}` is not imported here.",
           "add `use #{details.provider}` to this module"}

        :retired_process_type ->
          replacement = if(details.name == :Pid, do: "Pid(message)", else: "MonitorRef or TimerRef")

          {"Unindexed process type was retired",
           "`#{details.name}` belonged to Cure's unrestricted process algebra. The formal OTP surface uses indexed process handles and distinct reference types.",
           "use `Std.Otp` and replace `#{details.name}` with `#{replacement}`"}

        :unsupported_pattern ->
          {"Pattern is not supported here", "This pattern form cannot be checked in the current context.",
           "use a supported pattern"}

        :unsupported_guard ->
          {"Guard is not supported here", "This guard expression cannot be used in a pattern guard.",
           "rewrite the guard using supported operations"}

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

        :binary_match_needs_default ->
          {"Binary match needs a default", "This binary match does not cover all possible segment lengths.",
           "add a default binary-match arm"}

        :map_match_needs_default ->
          {"Map match needs a default", "This map match does not cover unmatched keys.", "add a default map-match arm"}

        :nonlinear_pattern ->
          {"Pattern binds a name twice", "A pattern cannot bind the same name more than once.",
           "use distinct names or a forced pattern"}

        :duplicate_default_pattern ->
          {"Duplicate default pattern", "This match contains more than one default pattern.",
           "keep only one default pattern"}

        :impossible_default_pattern ->
          {"Default pattern is unreachable", "This default pattern cannot be reached after the earlier patterns.",
           "remove or revise the unreachable pattern"}

        :typealias_not_a_type ->
          {"Type alias does not name a type", "The right-hand side of this type alias is not a well-formed type.",
           "define the alias using a type expression"}

        :result_type_not_family ->
          {"Result type is not a type family",
           "This dependent result must be a type family indexed by the function's result.",
           "return a valid indexed type"}

        :constructor_result_mismatch ->
          {"Constructor result does not match",
           "This constructor's result type does not match the family being defined.",
           "correct the constructor result indices"}

        :dependent_record_projection ->
          {"Dependent record projection is invalid",
           "This record field projection does not preserve the required dependent type.",
           "project a field with a compatible dependent type"}

        :with_indexed_scrutinee_unsupported ->
          {"Indexed with-scrutinee is unsupported",
           "This indexed value cannot be used as the parent of a `with` rematch.", "rematch a supported parent value"}

        :with_rematch_unsupported_parent_pattern ->
          {"With parent pattern is unsupported",
           "The parent pattern cannot be structurally rematched in this `with` expression.",
           "use a supported parent pattern"}

        :with_sibling_dependency_unsupported ->
          {"With sibling dependency is unsupported",
           "This rematch depends on a sibling binding that is not available here.",
           "restructure the dependent bindings"}

        :telescope_index_out_of_bounds ->
          {"Dependent index is out of scope", "This indexed reference points outside the available telescope.",
           "use an index that is in scope"}

        :effect_binder_erased ->
          {"Effect binder is erased", "An erased effect binder is used where a runtime-relevant value is required.",
           "make the binder relevant or remove the runtime use"}

        :effect_arity ->
          {"Effect operation arity mismatch", "This effect operation was given the wrong number of arguments.",
           "provide the arguments required by the effect operation"}

        :char_literal_needs_bounded ->
          {"Character literal needs a bound", "This character literal requires an explicit bounded character type.",
           "add the required bounded character annotation"}

        :char_literal_out_of_range ->
          {"Character literal is out of range",
           "This value is not a Unicode code point. A `Char` holds a code point in `0`..`1114111` (`0x10FFFF`).",
           "code point must be between 0 and 1114111"}

        :extern_returns_union ->
          {"Extern return type is unsupported", "An extern declaration cannot return this union type.",
           "use a representable foreign return type"}

        :extern_union_indistinct ->
          {"Extern union is indistinct", "The extern union members cannot be distinguished at the foreign boundary.",
           "make the foreign union members representationally distinct"}

        :cannot_infer_dependent_match ->
          {"Dependent match needs an expected type", "Cure cannot infer the indexed result of this match expression.",
           "add an annotation that determines the dependent result"}

        :applied_non_function ->
          {"Application target is not callable", "This expression is applied but does not have a callable type.",
           "apply a function or constructor"}

        :rewrite_requires_expected_type ->
          {"Rewrite needs an expected type", "Cure cannot infer the type required by this rewrite.",
           "add an annotation that fixes the rewritten type"}

        :rewrite_proof_not_equality ->
          {"Rewrite proof is not an equality", "The proof supplied to rewrite does not prove an equality.",
           "use an equality proof for the value being rewritten"}

        :match_scrutinee_not_data ->
          {"Match scrutinee is not data", "This match expression scrutinizes a value without data constructors.",
           "match a data value"}

        :with_mixed_rematch_arms ->
          {"With arms use incompatible rematches", "The rematch arms of this with expression do not have one shape.",
           "use the same rematch form in every arm"}

        :with_scrutinee_not_data ->
          {"With scrutinee is not data", "A with rematch requires a data-valued scrutinee.", "rematch a data value"}

        :too_few_arguments ->
          {"Too few arguments", "This application does not provide every required argument.",
           "supply the remaining arguments"}

        :too_many_arguments ->
          {"Too many arguments", "This application provides more arguments than the declaration accepts.",
           "remove the extra arguments"}

        :nonvariable_scrutinee ->
          {"Scrutinee must be a variable", "This dependent operation requires a variable scrutinee.",
           "bind the scrutinee before using it"}

        :graded_let_requires_variable ->
          {"Graded binding needs a variable", "A graded binding must bind a variable so its relevance can be tracked.",
           "bind a variable before applying the grade"}

        :unknown_grade ->
          {"Unknown relevance grade", "The written relevance grade is not defined by the current language edition.",
           "use a supported relevance grade"}

        :grade_requires_type ->
          {"Graded binding needs a type", "A graded binding must declare the type whose usage is being restricted.",
           "add a type annotation to the graded binding"}

        :with_multi_proof_unsupported ->
          {"Multiple with-scrutinee proof is unsupported",
           "A `proof` binding cannot be combined with multiple `with` scrutinees in this form.",
           "use one scrutinee or move the proof binding into a separate match"}

        :with_multi_rematch_unsupported ->
          {"Multiple with-scrutinee rematch is unsupported",
           "An LHS rematch cannot be combined with multiple `with` scrutinees in this form.",
           "use one scrutinee or restructure the rematch"}

        :with_multi_arity_mismatch ->
          {"Multiple with-arm arity mismatch",
           "Each arm of a multiple-scrutinee `with` must provide one pattern per scrutinee.",
           "make the arm pattern count match the scrutinee count"}

        :with_multi_no_arms ->
          {"Multiple with-scrutinee has no arms", "A multiple-scrutinee `with` must contain at least one matching arm.",
           "add a `with` arm"}

        :with_multi_inconsistent_pattern ->
          {"Multiple with patterns disagree",
           "Multiple-scrutinee `with` arms must use structurally consistent outer patterns.",
           "make the outer patterns agree or split the match"}

        :bounded_family_unregistered ->
          {"Bounded type family is not registered",
           "This bounded type family is not available in the current checking environment.",
           "declare or import the bounded family before using it"}

        :absurd_in_reachable_position ->
          {"Absurd branch is reachable", "This branch claims an impossible value, but the scrutinee can reach it.",
           "refine the index or handle the reachable constructor"}

        :opaque_not_eliminable ->
          {"Opaque value cannot be eliminated",
           "This opaque value cannot be inspected in the current checking context.",
           "use its public interface instead of matching on its representation"}

        :case_scrutinee_not_data ->
          {"Case scrutinee is not data", "This case expression scrutinizes a value without data constructors.",
           "match a data-valued expression"}

        :not_total ->
          {"Definition is not total",
           "This definition does not cover every input or does not terminate by the required measure.",
           "add the missing cases or provide a decreasing recursive argument"}

        :not_a_function ->
          {"Application target is not callable", "This value is used as a function, but its type is not callable.",
           "apply a function or constructor value"}

        :unsafe_call_required ->
          {"Unsafe call requires `unsafe`",
           "Calling `#{name_to_string(details.callee || "this function")}` crosses an unsafe boundary and must be written with the `unsafe` keyword.",
           "prefix the call with `unsafe`"}

        :run_requires_effect ->
          {"`run` expects an effect", "The argument to `run` must have type `Effect(T)`.",
           "pass an effectful computation to `run`"}

        :run_arity ->
          {"`run` expects one argument", "The effect escape `run` takes exactly one computation.",
           "pass exactly one argument"}

        :branch_arity ->
          {"Pattern branch has the wrong arity",
           "A pattern branch does not bind the number of values required by the matched constructor.",
           "make the branch pattern match the constructor's arguments"}

        :coverage ->
          {"Pattern match is not exhaustive", "This pattern match does not cover every constructor that can reach it.",
           "add the missing branch or a final wildcard branch"}

        :index_arity ->
          {"Indexed type has the wrong arity",
           "The number of indices supplied to this indexed type does not match its declaration.",
           "supply exactly the declared indices"}

        _ ->
          contextual_type_fallback(kind, opts)
      end

    TypeAdapter.contextual_failure(kind, details, opts, {title, message, label})
  end

  defp unsupported_expression_span({_tag, meta, _children}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Span{} = span} -> span
      _ -> nil
    end
  end

  defp unsupported_expression_span(_expression), do: nil

  defp unsupported_expression_form({tag, _meta, _children}) when is_atom(tag), do: tag
  defp unsupported_expression_form(_expression), do: :expression

  defp contextual_type_fallback(_kind, opts) do
    checking = Keyword.get(opts, :checking)
    origin = Keyword.get(opts, :expectation_origin)

    context_suffix =
      case checking do
        nil -> ""
        checking -> " while checking `#{name_to_string(checking)}`"
      end

    {title, message, label} =
      case origin do
        :annotation ->
          {"Expression does not match its annotation",
           "This expression does not satisfy the type required by its annotation#{context_suffix}.",
           "change the expression or its annotation"}

        :branch ->
          {"Branches have different types",
           "The branches of this match do not produce one compatible type#{context_suffix}.",
           "make the branches produce the same type"}

        :condition ->
          {"Condition has the wrong type",
           "This condition does not produce the type required by the conditional expression#{context_suffix}.",
           "make the condition produce `Bool`"}

        _ ->
          {"Cannot determine this expression's type",
           "Cure could not determine a valid type for this expression in its current checking context#{context_suffix}.",
           "add an annotation or revise this expression"}
      end

    {title, message, label}
  end

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []),
    do: NameAdapter.unknown_name(namespace, name, opts)

  defp pickup_label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp pickup_label(_, _style, _message), do: nil

  defp syntax_problem_code(:unterminated_lambda), do: "E035"
  defp syntax_problem_code(:unrecognized_pattern), do: "E090"
  defp syntax_problem_code(_kind), do: "E094"

  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_lambda}), do: "Lambda body is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unrecognized_pattern}), do: "Pattern is not supported"
  defp syntax_problem_title(%SyntaxProblem{kind: :tab_not_allowed}), do: "Tabs are not valid indentation"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_string}), do: "String is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_char}), do: "Character is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_quoted_identifier}), do: "Quoted name is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_number}), do: "Number literal is incomplete"
  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_char_escape}), do: "Invalid character escape"
  defp syntax_problem_title(%SyntaxProblem{kind: :atom_too_long}), do: "Atom literal is too long"
  defp syntax_problem_title(%SyntaxProblem{kind: :unexpected_character}), do: "Unexpected character"
  defp syntax_problem_title(%SyntaxProblem{kind: :obsolete_anonymous_hole}), do: "Anonymous hole spelling changed"
  defp syntax_problem_title(%SyntaxProblem{kind: :macro_use_mismatch}), do: "Macro syntax does not match"
  defp syntax_problem_title(%SyntaxProblem{kind: :macro_literal_capture}), do: "Macro literal capture is invalid"
  defp syntax_problem_title(%SyntaxProblem{kind: :non_associative}), do: "Operator chain needs parentheses"
  defp syntax_problem_title(%SyntaxProblem{kind: :ambiguous_precedence}), do: "Operator precedence is ambiguous"
  defp syntax_problem_title(%SyntaxProblem{kind: :malformed_macro_hole}), do: "Macro hole is incomplete"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_placement}), do: "Edition pragma is misplaced"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_malformed}), do: "Edition pragma is malformed"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_unknown}), do: "Edition is unknown"
  defp syntax_problem_title(%SyntaxProblem{kind: :missing_function_body}), do: "Function body is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :function_parameters_unparenthesized}),
    do: "Function parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "Lambda parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :lambda_arrow_missing}), do: "Lambda arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "Induction case arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_using_missing}), do: "Rewrite command needs `using`"
  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_in_missing}), do: "Rewrite expression needs `in`"
  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_occurrence_invalid}), do: "Rewrite occurrence is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid}),
    do: "Rewrite target needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :induction_case_introducer_missing}),
    do: "Induction branch needs `case`"

  defp syntax_problem_title(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "Induction cases must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_else_missing}),
    do: "Macro check needs `else`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_fail_missing}),
    do: "Macro check needs `fail`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid}),
    do: "Macro check needs a failure value"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_rule_becomes_missing}),
    do: "Macro rule needs `becomes`"

  defp syntax_problem_title(%SyntaxProblem{kind: :literal_rule_becomes_missing}),
    do: "Literal rule needs `becomes`"

  defp syntax_problem_title(%SyntaxProblem{kind: :computed_rule_by_missing}),
    do: "Computed rule needs `by`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_example_expands_missing}),
    do: "Macro example needs `expands`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_expands_with_missing}),
    do: "Macro expander needs `with`"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_indent_missing}),
    do: "Syntax family body must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_member_invalid}),
    do: "Syntax family member is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_entry_invalid}),
    do: "Structured macro entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_production_invalid}),
    do: "Structured macro production is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_body_indent_missing}),
    do: "Structured macro body must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_definition_entry_invalid}),
    do: "Macro declaration entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_example_entry_invalid}),
    do: "Macro example entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_explain_point_invalid}),
    do: "Macro explanation point is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "Local function needs `fn`"

  defp syntax_problem_title(%SyntaxProblem{kind: :implementation_for_keyword_missing}),
    do: "Implementation needs `for`"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "Explanation clause arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :match_arm}}),
    do: "Pattern branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}})
       when family in [:pickup_clause, :pickup_else],
       do: "Pickup branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :function_clause}}),
    do: "Function clause arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}})
       when family in [:with_arm, :with_rematch_arm],
       do: "With branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_binder_invalid}),
    do: "Refinement binder needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "Refinement binder needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "Refinement type needs a separator"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "Refinement type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :refinement_type}}),
    do: "Refinement type has the wrong closer"

  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_binder_invalid}), do: "Sigma binder needs a name"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_colon_missing}), do: "Sigma binder needs a colon"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_comma_missing}), do: "Sigma type needs a separator"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_unclosed}), do: "Sigma type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :sigma_type}}),
    do: "Sigma type has the wrong closer"

  defp syntax_problem_title(%SyntaxProblem{kind: :gadt_constructor_colon_missing}),
    do: "Constructor signature needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :record_field_colon_missing}),
    do: "Record field needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :fixity_colon_missing}),
    do: "Fixity declaration needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :precedencegroup_field_colon_missing}),
    do: "Precedence group field needs a colon"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{family: :typealias}
       }),
       do: "Type alias needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :type_declaration_assign_missing}),
    do: "Type declaration needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :type_indices_opener_missing}),
    do: "Type indices need parentheses"

  defp syntax_problem_title(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "Type assertion needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :named_implicit_pattern_assign_missing}),
    do: "Named implicit pattern needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :local_binding_assign_missing,
         context: %{family: :have}
       }),
       do: "Have binding needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :local_binding_assign_missing}),
    do: "Let binding needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "Local definitions must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :where_binding_assign_missing}),
    do: "Local definition needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true, container: :record}
       }),
       do: "Record fields need a separator"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true}
       }),
       do: "Map entries need a separator"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "Record entry needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "Map entry needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "Binary generator needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :send_comma_missing}),
    do: "Send needs a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{annotated: true}
       }),
       do: "Lifted callback needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :lift_callback_body_separator_missing}),
    do: "Lifted callback needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "Macro parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture}
       }),
       do: "Macro obligation needs parentheses"

  defp syntax_problem_title(%SyntaxProblem{kind: :with_rematch_separator_missing}),
    do: "With rematch needs a bar"

  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_parameter_name, context: %{lambda: true}}),
    do: "Lambda parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_parameter_name}), do: "Function parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "Variadic parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :call_unclosed}), do: "Function call is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :call_argument_separator_missing}),
    do: "Call arguments need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :list}}),
    do: "List is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :tuple}}),
    do: "Tuple is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: container}})
       when container in [:tuple_type, :tuple_type_sigil],
       do: "Tuple type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :grouped_type}}),
    do: "Grouped type is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_expression}
       }),
       do: "Parenthesized expression is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "Named constructor domain is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "Implicit constructor domain is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern}
       }),
       do: "Named implicit pattern is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter}
       }),
       do: "Implicit parameter is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments}
       }),
       do: "Binary specifier argument is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import}
       }),
       do: "Selective import is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :failure_parameters}
       }),
       do: "Failure parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :lift_callback_parameters}
       }),
       do: "Lifted callback parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :macro_obligation_capture}
       }),
       do: "Macro obligation is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group],
       do: "Syntax splice is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :match}
       }),
       do: "Pattern branch block is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: family}
       })
       when family in [:with, :multi_with],
       do: "With branch block is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :map}}),
    do: "Map is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :record}}),
    do: "Record is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :list_cons}}),
    do: "List cons is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :comprehension}
       }),
       do: "List comprehension is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :parameters}
       }),
       do: "Function parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_arguments}
       }),
       do: "Type application is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_parameters}
       }),
       do: "Type parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :constructor_parameters}
       }),
       do: "Constructor parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_indices}
       }),
       do: "Type index list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :lambda_parameters}
       }),
       do: "Lambda parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :binary_literal}}),
    do: "Binary literal is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_generator}
       }),
       do: "Binary generator is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :list}}),
    do: "List elements need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :tuple}}),
    do: "Tuple elements need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: container}})
       when container in [:tuple_type, :tuple_type_sigil],
       do: "Tuple type positions need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :grouped_type}
       }),
       do: "Grouped type positions need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :map}}),
    do: "Map entries need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "Record fields need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "Function parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments}
       }),
       do: "Type arguments need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters}
       }),
       do: "Type parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters}
       }),
       do: "Constructor parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices}
       }),
       do: "Type indices need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "Lambda parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import}
       }),
       do: "Imported names need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_trailing_separator, context: %{container: :list}}),
    do: "List ends with an extra comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_trailing_separator, context: %{container: :tuple}}),
    do: "Tuple ends with an extra comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :bare_brace_expression}), do: "Brace cannot start an expression"
  defp syntax_problem_title(%SyntaxProblem{kind: :unmatched_closer}), do: "Closing delimiter has no opener"
  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer}), do: "Closing delimiter does not match"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_parentheses}), do: "Parenthesized expression is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_brackets}), do: "Bracketed expression is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_braces}), do: "Braced expression is not closed"
  defp syntax_problem_title(_problem), do: "I got stuck while parsing this"

  defp syntax_problem_context(%SyntaxProblem{
         kind: :unterminated_lambda,
         expected: :rbrace,
         context: %{body_style: :brace}
       }),
       do: "This brace-delimited lambda body reaches the end of its container without the '}' that closes it."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_lambda}),
    do: "This multi-statement lambda body reaches the end of its container without a closing delimiter."

  defp syntax_problem_context(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}),
    do:
      "A range describes many values, but a pattern must describe a shape Cure can deconstruct. Bind the value and test the range in a guard instead."

  defp syntax_problem_context(%SyntaxProblem{kind: :unrecognized_pattern, observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} is not a pattern form Cure can deconstruct here."

  defp syntax_problem_context(%SyntaxProblem{kind: :tab_not_allowed}),
    do: "Cure indentation uses spaces so that block structure is the same in every editor."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_string}),
    do: "This string reaches the end of the source without its closing double quote."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_char}),
    do: "A character literal must contain one character and a closing single quote."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_quoted_identifier}),
    do: "This quoted name reaches the end of the source without its closing backtick."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_number}),
    do: "This numeric prefix or exponent is missing digits required by its literal form."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_char_escape, observed: observed}),
    do: "`\\#{syntax_name(observed)}` is not a supported character escape."

  defp syntax_problem_context(%SyntaxProblem{kind: :atom_too_long}),
    do: "BEAM atom names may contain at most 255 bytes; this authored atom exceeds that limit."

  defp syntax_problem_context(%SyntaxProblem{kind: :unexpected_character, observed: observed}),
    do: "#{syntax_name(observed)} does not begin any Cure token at this location."

  defp syntax_problem_context(%SyntaxProblem{kind: :obsolete_anonymous_hole}),
    do: "`??` was the anonymous-hole spelling before Cure 0.34; anonymous holes are now written `?_`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :macro_use_mismatch,
         context: %{keyword: keyword},
         expected: expected,
         observed: observed
       }) do
    "The `#{keyword}` macro invocation does not match its declared syntax. " <>
      capitalize_sentence(macro_expectation(expected, observed))
  end

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_literal_capture, expected: expected}),
    do: "This macro capture must match the literal shape `#{syntax_name(expected)}`."

  defp syntax_problem_context(%SyntaxProblem{kind: :non_associative, context: %{operator: operator}}),
    do: "The #{syntax_name(operator)} operator cannot be chained without parentheses."

  defp syntax_problem_context(%SyntaxProblem{kind: :ambiguous_precedence}),
    do: "These operators have no declared relative precedence; add parentheses to choose the grouping."

  defp syntax_problem_context(%SyntaxProblem{kind: :malformed_macro_hole}),
    do: "This macro hole is incomplete; write it as `<name: Kind>`."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_placement}),
    do: "The edition pragma must be the first authored construct in the file."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_malformed}),
    do: "The edition pragma must contain one 4-digit year, for example `@edition(\"2026\")`."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_unknown}),
    do:
      "Unknown edition: this edition is not supported by the current compiler. " <>
        "Use one of: #{Enum.join(Cure.Edition.all(), ", ")}."

  defp syntax_problem_context(%SyntaxProblem{kind: :missing_function_body}),
    do: "This function declaration ends after `=`, but every function needs a body expression."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :function_parameters_unparenthesized,
         context: %{function: function}
       }),
       do:
         "The function `#{function}` needs a parenthesized parameter list after its name. Write `()` when it takes no parameters."

  defp syntax_problem_context(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "An anonymous function must put its parameters inside parentheses immediately after `fn`."

  defp syntax_problem_context(%SyntaxProblem{kind: :lambda_arrow_missing}),
    do: "A lambda needs `->` between its parameter list and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "An induction case needs `=>` between its pattern and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_using_missing, observed: observed}),
    do:
      "A directed rewrite introduces its equality proof with `using`; #{authored_syntax(observed)} appears where `using` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_in_missing, observed: observed}),
    do:
      "A rewrite expression uses `in` between its equality proof and the expression being rewritten; #{authored_syntax(observed)} appears where `in` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_occurrence_invalid, observed: observed}),
    do:
      "The selector after `at` must be a positive integer occurrence such as `1`; #{authored_syntax(observed)} cannot select an occurrence."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid, observed: observed}),
    do: "The selector after `in` must name a local hypothesis; #{authored_syntax(observed)} is not a hypothesis name."

  defp syntax_problem_context(%SyntaxProblem{kind: :induction_case_introducer_missing, observed: observed}),
    do:
      "Every branch in an induction block starts with `case`; #{authored_syntax(observed)} appears at the start of this branch."

  defp syntax_problem_context(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "The `case` branches of an induction expression must form an indented block below its subject."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_else_missing, observed: observed}),
    do:
      "A macro check uses `else` between its condition and failure value; #{authored_syntax(observed)} appears where `else` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_fail_missing, observed: observed}),
    do:
      "The rejected branch of a macro check starts with `fail`; #{authored_syntax(observed)} appears where `fail` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid, observed: observed}),
    do:
      "After `fail`, write a declared macro failure with its arguments, such as `BadInput(value)`; #{authored_syntax(observed)} is not a failure constructor call."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_rule_becomes_missing, observed: observed}),
    do:
      "A syntax rule uses `becomes` between its matched form and expansion template; #{authored_syntax(observed)} appears where `becomes` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :literal_rule_becomes_missing, observed: observed}),
    do:
      "A literal rule uses `becomes` between its suffix pattern and expansion template; #{authored_syntax(observed)} appears where `becomes` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :computed_rule_by_missing, observed: observed}),
    do:
      "A computed rule uses `by` before the elaborator function that implements it; #{authored_syntax(observed)} appears where `by` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_example_expands_missing, observed: observed}),
    do:
      "A macro example uses `expands` between its use-site and expected result; #{authored_syntax(observed)} appears where `expands` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_expands_with_missing, observed: observed}),
    do:
      "A structured macro uses `expands with` before its expander function; #{authored_syntax(observed)} appears where `with` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :syntax_family_indent_missing, context: %{family: family}}),
    do:
      "The fields, included families, and productions of `#{family}` must be nested below its `syntax family` declaration."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_member_invalid,
         observed: observed,
         context: %{family: family}
       }),
       do:
         "#{authored_syntax(observed)} cannot declare a member of the `#{family}` syntax family. Write a typed field, `includes Family`, or a `syntax` production."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_entry_invalid,
         observed: observed,
         context: %{family: family, valid_fields: valid_fields}
       }),
       do:
         "#{authored_syntax(observed)} does not start a field of the `#{family}` structured macro body. Valid fields are #{inline_choices(valid_fields)}."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_production_invalid,
         observed: observed,
         context: context
       }) do
    field = Map.get(context, :field, "this field")
    family = Map.get(context, :family)
    owner = if family, do: " in `#{family}`", else: ""

    "#{authored_syntax(observed)} does not match any production accepted by `#{field}`#{owner}. Follow one of the forms declared by that syntax family."
  end

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_body_indent_missing,
         context: %{family: family, valid_fields: valid_fields}
       }),
       do:
         "The `#{family}` structured macro body must be indented below its invocation. Its fields are #{inline_choices(valid_fields)}."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_definition_entry_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot start an entry in a macro declaration. Use a syntax rule, family contract, expander, literal rule, explanation, failure, or opened category."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_example_entry_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot start a pinned macro example. Each line in this nested block must use `example use_site expands expected`."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_explain_point_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot name a macro failure point. Use a failure category such as `Duration`, or `keyword \"every\"` for a literal token."

  defp syntax_problem_context(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "A private function declaration must put `fn` between `local` and the function name."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :implementation_for_keyword_missing,
         context: %{declaration: declaration}
       }),
       do:
         "The implementation of `#{declaration}` needs `for` between its interface or protocol and the type receiving the implementation."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "An explanation clause needs `=>` between its failure point and message."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}}),
    do: "#{branch_family_name(family)} needs `->` between its head and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_binder_invalid, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name the value refined by this type. Use a lower-case name such as `value`."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "A refinement binder must be followed by `:` and the base type whose values it describes."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "A refinement type uses `|` between its base type and the proposition values must satisfy."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "This refinement type reaches the end of its container without the '}' that closes its proposition."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :mismatched_closer,
         expected: expected,
         observed: observed,
         context: %{family: :refinement_type}
       }),
       do:
         "This refinement type starts with '{', so #{authored_syntax(observed)} cannot close it. Use '#{syntax_insertion(expected)}' after the proposition."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_binder_invalid, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name the first value in this dependent pair. Use a lower-case binder such as `value`."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_colon_missing}),
    do: "A Sigma binder must be followed by `:` and the type of its first value."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_comma_missing}),
    do: "A Sigma type uses `,` between the first value's type and the dependent type of its second value."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_unclosed}),
    do: "This Sigma type reaches the end of the source without the ')' that closes its dependent pair."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :mismatched_closer,
         expected: expected,
         observed: observed,
         context: %{family: :sigma_type}
       }),
       do:
         "This Sigma type starts with '(', so #{authored_syntax(observed)} cannot close it. Use '#{syntax_insertion(expected)}' after the dependent result type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :gadt_constructor_colon_missing,
         context: %{declaration: constructor, family: family}
       }),
       do: "The constructor `#{constructor}` in `#{family}` needs `:` between its name and type signature."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :record_field_colon_missing,
         context: %{declaration: field, family: record}
       }),
       do: "The field `#{field}` in record `#{record}` needs `:` between its name and declared type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :fixity_colon_missing,
         context: %{declaration: operator, family: fixity}
       }),
       do: "The `#{fixity}` declaration for `#{operator}` needs `:` between the operator and its precedence group."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :precedencegroup_field_colon_missing,
         context: %{declaration: field, family: group}
       }),
       do: "The `#{field}` setting in precedence group `#{group}` needs `:` before its value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{declaration: name, family: :typealias}
       }),
       do: "The type alias `#{name}` needs `=` between its name and the type it expands to."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{declaration: name}
       }),
       do: "The type `#{name}` needs `=` between its declaration head and its constructors or aliased type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_indices_opener_missing,
         context: %{declaration: declaration}
       }),
       do: "The indexed type `#{declaration}` must put its index telescope inside parentheses after `indices`."

  defp syntax_problem_context(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "The `assert_type` expression needs `:` between the asserted value and its expected type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :named_implicit_pattern_assign_missing,
         context: %{binder: binder}
       }),
       do: "The named implicit pattern for `#{binder}` needs `=` before the pattern that fixes its value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :local_binding_assign_missing,
         context: %{family: family, declaration: name}
       }),
       do: "The `#{family}` binding for `#{name}` needs `=` before the value it binds."

  defp syntax_problem_context(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "Definitions belonging to this `where` block must be indented beneath it."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :where_binding_assign_missing,
         context: %{declaration: name}
       }),
       do: "The local definition `#{name}` needs `=` between its name and value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true, container: container, key: key}
       }),
       do:
         "After `#{key}`, this could be another punned #{container} entry needing `,`, or the value of `#{key}` needing `=>`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "This explicit record entry needs `=>` between its key and value."

  defp syntax_problem_context(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "This explicit map entry needs `=>` between its key and value."

  defp syntax_problem_context(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "This binary generator needs `<-` between its byte pattern and source expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :send_comma_missing}),
    do: "The keyword `send` form needs `,` between its target and message."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{declaration: name, annotated: true}
       }),
       do: "The lifted callback `#{name}` needs `=` between its declared return type and body."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{declaration: name}
       }),
       do: "The lifted callback `#{name}` needs `->` between its parameter list and body."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container, declaration: declaration}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "The macro declaration `#{declaration}` must put its parameters inside parentheses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture, interface: interface}
       }),
       do: "The `#{interface}` obligation must put the capture it constrains inside parentheses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :with_rematch_separator_missing,
         context: %{parent_pattern_count: count}
       }),
       do: "These #{count} restated parent patterns need `|` before the pattern for the `with` value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :invalid_parameter_name,
         observed: observed,
         context: %{lambda: true}
       }),
       do:
         "#{String.capitalize(syntax_name(observed))} cannot name a lambda parameter. Use a lower-case name such as `value`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :invalid_parameter_name,
         observed: observed,
         context: %{implicit: true}
       }),
       do:
         "#{String.capitalize(syntax_name(observed))} cannot name an implicit parameter. Write a lower-case binder such as `{type}` or `{type: Type}`."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_parameter_name, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name a function parameter. Use a lower-case name such as `value`, optionally followed by `: Type`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :variadic_parameter_name_missing,
         context: %{kind: :keyword_variadic}
       }),
       do: "The `**` marker must be followed by the name that receives extra named arguments, for example `**options`."

  defp syntax_problem_context(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "The `*` marker must be followed by the name that receives extra positional arguments, for example `*values`."

  defp syntax_problem_context(%SyntaxProblem{kind: :call_unclosed, context: %{call: call}}),
    do: "The call to `#{call}` reaches the end of the source without the ')' that closes its argument list."

  defp syntax_problem_context(%SyntaxProblem{kind: :call_argument_separator_missing, context: %{call: call}}),
    do: "The call to `#{call}` has another argument here, but consecutive arguments must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbrace,
         context: %{container: :map}
       }),
       do: "This map reaches the end of the source without the '}' that closes its entries."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbrace,
         context: %{container: :record}
       }),
       do: "This record reaches the end of the source without the '}' that closes its fields."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbracket,
         context: %{container: :list_cons}
       }),
       do: "This list cons reaches the end of the source without the ']' after its tail expression."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbracket,
         context: %{container: :comprehension}
       }),
       do: "This list comprehension reaches the end of the source without the ']' that closes its clauses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :parameters}
       }),
       do: "This function's parameter list reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments, type: type, token_type: :dedent}
       }),
       do: "The type application `#{type}` ends before the ')' that closes its arguments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments, type: type}
       }),
       do: "The type application `#{type}` reaches the end of the source without the ')' that closes its arguments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_parameters, declaration: declaration}
       }),
       do: "The declaration of `#{declaration}` reaches the end of its type parameter list without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :constructor_parameters, constructor: constructor}
       }),
       do: "The constructor `#{constructor}` reaches the end of its parameter list without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_indices, declaration: declaration}
       }),
       do: "The indexed type `#{declaration}` reaches the end of its index telescope without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :lambda_parameters}
       }),
       do: "This lambda's parameter list reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: expected,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil] and expected in [:rparen, :rbracket],
       do:
         "This tuple type reaches the end of the source without the '#{syntax_insertion(expected)}' that closes its positions."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :grouped_type}
       }),
       do: "This grouped type reaches the end of the source without the ')' that closes its positions."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :grouped_expression}
       }),
       do: "This parenthesized expression reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "This named constructor domain reaches the end of the declaration without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "This implicit constructor domain reaches the end of the declaration without its closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern, binder: binder}
       }),
       do: "The named implicit pattern for `#{binder}` reaches the end of its value without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter, binder: binder}
       }),
       do: "The implicit parameter `#{binder}` reaches the end of its annotation without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments, specifier: specifier}
       }),
       do: "The binary `#{specifier}` specifier reaches the end of its argument without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import, module: module}
       }),
       do: "The selective import from `#{module}` reaches the end of its names without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container, declaration: declaration}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "The parameter list for `#{declaration}` reaches its body without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :macro_obligation_capture, interface: interface, capture: capture}
       }),
       do: "The `#{interface}` obligation for `#{capture}` is missing the ')' that closes its capture."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group] do
    form = if container == :splice_group, do: "group splice", else: "splice"
    "This #{form} reaches the end of its expression without the closing ')'."
  end

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :match}
       }),
       do: "This inline `match` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :with}
       }),
       do: "This inline `with` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :multi_with}
       }),
       do: "This multi-scrutinee `with` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_literal}
       }),
       do: "This binary literal reaches the end of the source without the '>>' that closes its segments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_generator}
       }),
       do: "This binary generator reaches the end of the source without the '>>' after its source expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :container_unclosed, context: %{container: container}}),
    do: "This #{container} reaches the end of the source without the ']' that closes its elements."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :map}
       }),
       do: "This map has another entry here, but consecutive entries must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "This record has another field here, but consecutive fields must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "This function has another parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments, type: type}
       }),
       do:
         "The type application `#{type}` has another argument here, but consecutive type arguments must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters, declaration: declaration}
       }),
       do:
         "The declaration of `#{declaration}` has another type parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters, constructor: constructor}
       }),
       do:
         "The constructor `#{constructor}` has another parameter type here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices, declaration: declaration}
       }),
       do:
         "The indexed type `#{declaration}` has another index here, but consecutive indices must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "This lambda has another parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import, module: module}
       }),
       do: "The import from `#{module}` has another name here, but imported names must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: "This type has another position here, but consecutive type positions must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       }),
       do: "This #{container} has another element here, but consecutive elements must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_trailing_separator,
         context: %{container: container}
       }),
       do: "This #{container} ends immediately after a comma, but every comma must be followed by another element."

  defp syntax_problem_context(%SyntaxProblem{kind: :bare_brace_expression}),
    do:
      "A bare '{' does not begin a Cure expression. Write `Type{...}` for a record, `\#{...}` for a map, or use indentation for a block."

  defp syntax_problem_context(%SyntaxProblem{kind: :unmatched_closer, observed: observed}),
    do: "#{syntax_name(observed)} closes a construct, but there is no matching opener here."

  defp syntax_problem_context(%SyntaxProblem{kind: :mismatched_closer, expected: expected, observed: observed}),
    do: "This construct needs #{syntax_name(expected)}, but it is closed with #{syntax_name(observed)} instead."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_parentheses}),
    do: "This parenthesized expression reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_brackets}),
    do: "This bracketed expression reaches the end of the source without its closing ']'."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_braces}),
    do: "This braced expression reaches the end of the source without its closing '}'."

  defp syntax_problem_context(%SyntaxProblem{observed: :eof}),
    do: "The source ended while I was still parsing this construct."

  defp syntax_problem_context(%SyntaxProblem{observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} cannot appear at this point in the construct."

  defp capitalize_sentence(<<first::utf8, rest::binary>>), do: String.upcase(<<first::utf8>>) <> rest
  defp capitalize_sentence(text), do: text

  defp syntax_expected_doc(%SyntaxProblem{expected: nil, alternatives: []}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :macro_use_mismatch}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :mismatched_closer}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :function_parameters_unparenthesized}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :invalid_parameter_name}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :variadic_parameter_name_missing}), do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{kind: kind})
       when kind in [:call_unclosed, :call_argument_separator_missing],
       do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{kind: kind})
       when kind in [:container_unclosed, :container_separator_missing, :container_trailing_separator],
       do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{} = problem) do
    expected = [problem.expected | problem.alternatives] |> Enum.reject(&is_nil/1) |> Enum.map(&syntax_name/1)

    Doc.paragraph([
      "A valid continuation here starts with",
      Doc.emphasis(:expected, Enum.join(expected, " or ")) |> then(&Doc.concat([&1, Doc.text(".")]))
    ])
  end

  defp macro_expectation({:literal, expected}, observed),
    do: "expected `#{escape_macro_text(expected)}` here, but found #{macro_observed(observed)}."

  defp macro_expectation({:hole_kind, kind}, observed),
    do: "expected #{article_for_kind(kind)} #{kind} here, but found #{macro_observed(observed)}."

  defp macro_expectation(:nothing_more, observed),
    do: "This macro has no more to match here, but found #{macro_observed(observed)}."

  defp macro_expectation(expected, observed),
    do: "expected #{syntax_name(expected)} here, but found #{macro_observed(observed)}."

  defp article_for_kind(<<c, _::binary>>) when c in ~c"AEIOUaeiou", do: "an"
  defp article_for_kind(_kind), do: "a"

  defp macro_observed(:newline), do: "`end of line`"
  defp macro_observed(:dedent), do: "`a dedent`"
  defp macro_observed(nil), do: "`nil`"

  defp macro_observed({:char, value}) when is_integer(value) do
    "`'#{escape_macro_text(<<value::utf8>>)}'`"
  end

  defp macro_observed({:regex, _value}), do: "`a regex`"
  defp macro_observed(value) when is_list(value), do: "`an interpolated string`"

  defp macro_observed(value) when is_binary(value),
    do: "`#{escape_macro_text(value)}`"

  defp macro_observed(value) when is_atom(value), do: "`#{syntax_name(value)}`"
  defp macro_observed(value), do: "`#{escape_macro_text(inspect(value))}`"

  defp escape_macro_text(value) when is_binary(value) do
    value
    |> String.replace("\\", "\\\\")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda, expected: :rbrace}),
    do: "close this lambda body with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda}), do: "the unclosed body reaches here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}),
    do: "a range operator cannot be used in a pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :unrecognized_pattern}), do: "this pattern form is not supported"
  defp syntax_problem_label(%SyntaxProblem{kind: :missing_function_body}), do: "write the function body after this `=`"

  defp syntax_problem_label(%SyntaxProblem{kind: :function_parameters_unparenthesized}),
    do: "the parameter list belongs before this token"

  defp syntax_problem_label(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "insert `(` before the first parameter"

  defp syntax_problem_label(%SyntaxProblem{kind: :lambda_arrow_missing}),
    do: "insert `->` before the lambda body"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "insert `=>` before this induction case body"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_using_missing}),
    do: "insert `using` before the equality proof"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_in_missing}),
    do: "insert `in` before the expression to rewrite"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_occurrence_invalid}),
    do: "write a positive occurrence number here"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid}),
    do: "write the local hypothesis name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :induction_case_introducer_missing}),
    do: "this induction branch must start with `case`"

  defp syntax_problem_label(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "indent the induction cases below the subject"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_else_missing}),
    do: "insert `else` before the rejected branch"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_fail_missing}),
    do: "insert `fail` before this failure value"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid}),
    do: "call a declared macro failure here"

  defp syntax_problem_label(%SyntaxProblem{kind: kind, expected: expected, context: %{token_type: type}})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] and type in [:eof, :dedent, :newline],
       do: "add `#{expected}` and the expression that follows it"

  defp syntax_problem_label(%SyntaxProblem{kind: kind, expected: expected})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ],
       do: "insert `#{expected}` before this expression"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_indent_missing}),
    do: "indent the syntax family members below this declaration"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_member_invalid}),
    do: "write a field, include, or production here"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_entry_invalid}),
    do: "start this entry with a valid structured field"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_production_invalid}),
    do: "this does not match a declared family production"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_body_indent_missing}),
    do: "indent the structured macro body here"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_definition_entry_invalid}),
    do: "replace this with a valid macro declaration entry"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_example_entry_invalid}),
    do: "start this line with `example`"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_explain_point_invalid}),
    do: "name the failure point before `=>`"

  defp syntax_problem_label(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "insert `fn` before this function name"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :implementation_for_keyword_missing,
         context: %{repair: :replace}
       }),
       do: "replace this with `for`"

  defp syntax_problem_label(%SyntaxProblem{kind: :implementation_for_keyword_missing}),
    do: "insert `for` before this implementation type"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "insert `=>` before this explanation message"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing}),
    do: "insert `->` before this branch body"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_binder_invalid}),
    do: "write a lower-case refinement binder here"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "insert `:` before the base type"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "insert `|` before the proposition"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "close this refinement type with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :refinement_type}}),
    do: "replace this with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_binder_invalid}),
    do: "write a lower-case Sigma binder here"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_colon_missing}),
    do: "insert `:` before the first value's type"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_comma_missing}),
    do: "insert `,` before the dependent result type"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_unclosed}),
    do: "close this Sigma type with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :sigma_type}}),
    do: "replace this with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :gadt_constructor_colon_missing}),
    do: "insert `:` before this constructor signature"

  defp syntax_problem_label(%SyntaxProblem{kind: :record_field_colon_missing}),
    do: "insert `:` before this field type"

  defp syntax_problem_label(%SyntaxProblem{kind: :fixity_colon_missing}),
    do: "insert `:` before this precedence group"

  defp syntax_problem_label(%SyntaxProblem{kind: :precedencegroup_field_colon_missing}),
    do: "insert `:` before this setting value"

  defp syntax_problem_label(%SyntaxProblem{kind: :type_declaration_assign_missing}),
    do: "insert `=` before this type body"

  defp syntax_problem_label(%SyntaxProblem{kind: :type_indices_opener_missing}),
    do: "insert `(` before the first type index"

  defp syntax_problem_label(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "insert `:` before this expected type"

  defp syntax_problem_label(%SyntaxProblem{kind: :named_implicit_pattern_assign_missing}),
    do: "insert `=` before this implicit pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :local_binding_assign_missing}),
    do: "insert `=` before this binding value"

  defp syntax_problem_label(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "indent this definition beneath `where`"

  defp syntax_problem_label(%SyntaxProblem{kind: :where_binding_assign_missing}),
    do: "insert `=` before this local value"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true}
       }),
       do: "separate these entries with `,`, or make this the value with `=>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "insert `=>` before this record value"

  defp syntax_problem_label(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "insert `=>` before this map value"

  defp syntax_problem_label(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "insert `<-` before this generator source"

  defp syntax_problem_label(%SyntaxProblem{kind: :send_comma_missing}),
    do: "insert a comma before this message"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{annotated: true}
       }),
       do: "insert `=` before this callback body"

  defp syntax_problem_label(%SyntaxProblem{kind: :lift_callback_body_separator_missing}),
    do: "insert `->` before this callback body"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "open this parameter list with `(`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture}
       }),
       do: "insert `(` before this capture"

  defp syntax_problem_label(%SyntaxProblem{kind: :with_rematch_separator_missing}),
    do: "insert `|` before this with-pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :invalid_parameter_name, context: %{lambda: true}}),
    do: "write a lambda parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :invalid_parameter_name}),
    do: "write a parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :obsolete_anonymous_hole}),
    do: "replace `??` with `?_`"

  defp syntax_problem_label(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "write the variadic parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :call_unclosed}), do: "close this call with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :call_argument_separator_missing}),
    do: "insert a comma before this argument"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :parameters}
       }),
       do: "close this parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments}
       }),
       do: "close these type arguments with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_parameters}
       }),
       do: "close these type parameters with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :constructor_parameters}
       }),
       do: "close this constructor's parameters with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_indices}
       }),
       do: "close these type indices with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :lambda_parameters}
       }),
       do: "close this lambda parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "close this macro parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :macro_obligation_capture}
       }),
       do: "close this obligation with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_literal}
       }),
       do: "close this binary literal with `>>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_generator}
       }),
       do: "close this binary generator with `>>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: expected,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil],
       do: "close this tuple type with `#{syntax_insertion(expected)}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_type}
       }),
       do: "close this grouped type with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_expression}
       }),
       do: "close this parenthesized expression with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "close this named constructor domain with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "close this implicit constructor domain with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern}
       }),
       do: "close this named implicit pattern with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter}
       }),
       do: "close this implicit parameter with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments}
       }),
       do: "close this binary specifier with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import}
       }),
       do: "close these imported names with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group],
       do: "close this syntax splice with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block}
       }),
       do: "close this branch block with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_unclosed, expected: expected}),
    do: "close this container with `#{syntax_insertion(expected)}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :map}
       }),
       do: "insert a comma before this entry"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "insert a comma before this field"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "insert a comma before this parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments}
       }),
       do: "insert a comma before this type argument"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters}
       }),
       do: "insert a comma before this type parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters}
       }),
       do: "insert a comma before this constructor parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices}
       }),
       do: "insert a comma before this type index"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "insert a comma before this lambda parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import}
       }),
       do: "insert a comma before this imported name"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: "insert a comma before this type position"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_separator_missing}),
    do: "insert a comma before this element"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_trailing_separator}),
    do: "this comma has no following element"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_string}),
    do: "insert the closing `\"` here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_char}),
    do: "insert the closing `'` here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_quoted_identifier}),
    do: "insert the closing backtick here"

  defp syntax_problem_label(%SyntaxProblem{kind: :bare_brace_expression}),
    do: "choose record, map, or block syntax here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unmatched_closer}), do: "this delimiter has nothing to close"
  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer}), do: "replace this mismatched delimiter"

  defp syntax_problem_label(%SyntaxProblem{kind: kind})
       when kind in [:unclosed_parentheses, :unclosed_brackets, :unclosed_braces],
       do: "the closing delimiter belongs here"

  defp syntax_problem_label(%SyntaxProblem{kind: :non_associative}),
    do: "this second operator makes the chain ambiguous"

  defp syntax_problem_label(%SyntaxProblem{kind: :ambiguous_precedence}),
    do: "this operator has no precedence relative to the surrounding one"

  defp syntax_problem_label(_problem), do: "this syntax does not fit here"

  defp syntax_secondary_labels(%SyntaxProblem{kind: :macro_use_mismatch} = problem, primary_span) do
    [
      pickup_label(problem.opener, :secondary, "this macro invocation starts here"),
      pickup_label(problem.within, :secondary, "the matching rule is declared here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :mismatched_closer,
           opener: opener,
           previous: previous,
           context: %{family: family, binder_span: binder_span}
         },
         primary_span
       )
       when family in [:refinement_type, :sigma_type] do
    {opener_message, binder_message, previous_message} =
      case family do
        :refinement_type ->
          {"this refinement type starts here", "this is the refinement binder", "the proposition ends here"}

        :sigma_type ->
          {"this Sigma type starts here", "this is the Sigma binder", "the dependent result type ends here"}
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(binder_span, :secondary, binder_message),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: opener,
           previous: previous,
           context: %{container: :macro_obligation_capture} = context
         },
         primary_span
       )
       when kind in [:container_opener_missing, :container_unclosed] do
    open_label =
      if kind == :container_unclosed do
        pickup_label(opener, :secondary, "the capture starts here")
      end

    [
      pickup_label(Map.get(context, :owner_span), :secondary, "this obligation starts here"),
      pickup_label(Map.get(context, :interface_span) || previous, :secondary, "this is the required interface"),
      open_label,
      pickup_label(previous, :secondary, "the capture ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :unterminated_lambda,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    opener_message =
      if Map.get(context, :body_style) == :brace,
        do: "this lambda body starts here",
        else: "this lambda starts here"

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the previous body expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :variadic_parameter_name_missing, opener: %Span{} = marker},
         primary_span
       )
       when marker != primary_span,
       do: [%Label{span: marker, style: :secondary, message: "this variadic marker needs a binder"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :lambda_parameters_unparenthesized, opener: %Span{} = lambda},
         primary_span
       )
       when lambda != primary_span,
       do: [%Label{span: lambda, style: :secondary, message: "this lambda starts here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :lambda_arrow_missing,
           opener: %Span{} = lambda,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(lambda, :secondary, "this lambda starts here"),
      pickup_label(previous, :secondary, "its parameter list ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: %{family: :induction_case}
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction case starts here"),
      pickup_label(previous, :secondary, "the induction pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :rewrite_using_missing,
              :rewrite_in_missing,
              :rewrite_occurrence_invalid,
              :rewrite_hypothesis_name_invalid
            ] do
    previous_message =
      case kind do
        :rewrite_using_missing -> "the rewrite direction ends here"
        :rewrite_in_missing -> "the equality proof ends here"
        :rewrite_occurrence_invalid -> "this `at` selector needs an occurrence number"
        :rewrite_hypothesis_name_invalid -> "this `in` selector needs a hypothesis name"
      end

    [
      pickup_label(opener, :secondary, "this rewrite command starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous, context: context},
         primary_span
       )
       when kind in [:syntax_family_indent_missing, :syntax_family_member_invalid] do
    previous_message =
      case kind do
        :syntax_family_indent_missing ->
          "the syntax family header ends here"

        :syntax_family_member_invalid ->
          if previous == Map.get(context, :name_span),
            do: "the syntax family header ends here",
            else: "the previous family member ends here"
      end

    [
      pickup_label(opener, :secondary, "this syntax family declaration starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, previous: %Span{} = previous},
         primary_span
       )
       when kind in [:syntax_family_entry_invalid, :syntax_family_production_invalid] and
              previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the previous structured entry ends here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :macro_definition_entry_invalid,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    previous_message =
      if previous && previous.start_line == opener.start_line,
        do: "the macro header ends here",
        else: "the previous macro entry ends here"

    [
      pickup_label(opener, :secondary, "this macro declaration starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [:macro_example_entry_invalid, :macro_explain_point_invalid] do
    {opener_message, previous_message} =
      case kind do
        :macro_example_entry_invalid ->
          {"this syntax rule owns the example block", "the previous macro example ends here"}

        :macro_explain_point_invalid ->
          {"this explanation block starts here", "the previous explanation clause ends here"}
      end

    [pickup_label(opener, :secondary, opener_message), pickup_label(previous, :secondary, previous_message)]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] do
    {opener_message, previous_message} =
      case kind do
        :macro_rule_becomes_missing -> {"this syntax rule starts here", "the matched form ends here"}
        :literal_rule_becomes_missing -> {"this literal rule starts here", "the suffix pattern ends here"}
        :computed_rule_by_missing -> {"this computed rule starts here", "the computed modifier ends here"}
        :macro_example_expands_missing -> {"this macro example starts here", "the example use-site ends here"}
        :macro_expands_with_missing -> {"this expander section starts here", "the `expands` keyword ends here"}
      end

    [pickup_label(opener, :secondary, opener_message), pickup_label(previous, :secondary, previous_message)]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :induction_case_introducer_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction block starts here"),
      pickup_label(previous, :secondary, "the previous induction case ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :induction_block_indent_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction expression starts here"),
      pickup_label(previous, :secondary, "the induction subject ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :macro_check_else_missing,
              :macro_check_fail_missing,
              :macro_check_failure_constructor_invalid
            ] do
    previous_message =
      case kind do
        :macro_check_else_missing -> "the checked condition ends here"
        :macro_check_fail_missing -> "the rejected branch starts after this `else`"
        :macro_check_failure_constructor_invalid -> "this `fail` needs a failure constructor call"
      end

    [
      pickup_label(opener, :secondary, "this macro check starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: %{family: :explain_clause}
         },
         primary_span
       ) do
    labels =
      if opener == previous do
        [pickup_label(previous, :secondary, "this is the failure point")]
      else
        [
          pickup_label(opener, :secondary, "this explanation clause starts here"),
          pickup_label(previous, :secondary, "the failure point ends here")
        ]
      end

    labels
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :branch_arrow_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this branch head ends here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :gadt_constructor_colon_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this is the constructor name"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :type_indices_opener_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the index telescope follows this keyword"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :assert_type_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this type assertion starts here"),
      pickup_label(previous, :secondary, "the asserted expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :named_implicit_pattern_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this named implicit pattern starts here"),
      pickup_label(previous, :secondary, "this is the implicit binder")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :local_binding_assign_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this #{Map.get(context, :family, :let)} binding starts here"),
      pickup_label(Map.get(context, :pattern_span), :secondary, "this is the binding pattern"),
      pickup_label(previous, :secondary, "the binding head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :where_block_indent_missing,
           opener: %Span{} = opener
         },
         primary_span
       )
       when opener != primary_span,
       do: [pickup_label(opener, :secondary, "this local `where` block starts here")]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :where_binding_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this local `where` block starts here"),
      pickup_label(previous, :secondary, "this is the local definition name")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :map_entry_separator_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    container = Map.get(context, :container, :map)

    [
      pickup_label(opener, :secondary, "this #{container} starts here"),
      pickup_label(Map.get(context, :entry_span), :secondary, "this #{container} entry starts here"),
      pickup_label(previous, :secondary, "the #{container} key ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :binary_generator_arrow_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this binary generator starts here"),
      pickup_label(previous, :secondary, "the binary pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :send_comma_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this send starts here"),
      pickup_label(previous, :secondary, "the send target ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :lift_callback_body_separator_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this lifted callback starts here"),
      pickup_label(Map.get(context, :name_span), :secondary, "this is the callback name"),
      pickup_label(previous, :secondary, "the callback head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :with_rematch_separator_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "the restated parent patterns start here"),
      pickup_label(previous, :secondary, "the final parent pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :record_field_colon_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this is the record field name"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :local_function_keyword_missing, opener: %Span{} = opener},
         primary_span
       )
       when opener != primary_span,
       do: [%Label{span: opener, style: :secondary, message: "this starts a private declaration"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :implementation_for_keyword_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the implementation"),
      pickup_label(previous, :secondary, "the implemented interface or protocol ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :fixity_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the fixity declaration"),
      pickup_label(previous, :secondary, "this is the operator being declared")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :precedencegroup_field_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this is the precedence group"),
      pickup_label(previous, :secondary, "this is the setting name")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :type_declaration_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the type declaration"),
      pickup_label(previous, :secondary, "the declaration head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [
              :refinement_binder_invalid,
              :refinement_colon_missing,
              :refinement_bar_missing,
              :refinement_unclosed
            ] do
    [
      pickup_label(opener, :secondary, "this refinement type starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the refinement binder"),
      pickup_label(previous, :secondary, refinement_previous_label(kind))
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when container in [:splice, :splice_group] do
    [
      pickup_label(opener, :secondary, "the syntax splice starts here"),
      pickup_label(previous, :secondary, "the spliced expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :grouped_expression}
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this parenthesized expression starts here"),
      pickup_label(previous, :secondary, "the grouped expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container} = context
         },
         primary_span
       )
       when container in [:named_constructor_domain, :implicit_constructor_domain] do
    implicit? = container == :implicit_constructor_domain

    [
      pickup_label(
        opener,
        :secondary,
        if(implicit?,
          do: "this implicit constructor domain starts here",
          else: "this named constructor domain starts here"
        )
      ),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the dependent argument binder"),
      pickup_label(previous, :secondary, "the argument type ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :named_implicit_pattern} = context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this named implicit pattern starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the implicit binder"),
      pickup_label(previous, :secondary, "the implicit pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :implicit_parameter} = context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this implicit parameter starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the implicit parameter name"),
      pickup_label(previous, :secondary, "the parameter annotation ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :binary_specifier_arguments} = context
         },
         primary_span
       ) do
    [
      pickup_label(Map.get(context, :specifier_span), :secondary, "this is the binary specifier"),
      pickup_label(opener, :secondary, "its argument starts here"),
      pickup_label(previous, :secondary, "the specifier argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :selective_import}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "the selective import list starts here"),
      pickup_label(previous, :secondary, "the previous imported name ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: opener,
           previous: previous,
           context: %{container: container} = context
         },
         primary_span
       )
       when kind in [:container_opener_missing, :container_unclosed] and
              container in [:failure_parameters, :lift_callback_parameters] do
    owner = if container == :failure_parameters, do: "failure declaration", else: "lifted callback"

    opener_labels =
      if kind == :container_unclosed do
        [pickup_label(opener, :secondary, "the parameter list starts here")]
      else
        []
      end

    (opener_labels ++
       [
         pickup_label(Map.get(context, :owner_span), :secondary, "this #{owner} starts here"),
         pickup_label(Map.get(context, :name_span), :secondary, "this is its name"),
         pickup_label(previous, :secondary, "the previous parameter ends here")
       ])
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [
              :sigma_binder_invalid,
              :sigma_colon_missing,
              :sigma_comma_missing,
              :sigma_unclosed
            ] do
    [
      pickup_label(opener, :secondary, "this Sigma type starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the Sigma binder"),
      pickup_label(previous, :secondary, sigma_previous_label(kind))
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] and
              container in [:tuple_type, :tuple_type_sigil, :grouped_type] do
    opener_message =
      if container == :grouped_type, do: "this grouped type starts here", else: "this tuple type starts here"

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the previous type position ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this parameter list starts here"),
      pickup_label(previous, :secondary, "the previous parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when container in [:binary_literal, :binary_generator] do
    {opener_message, previous_message} =
      case container do
        :binary_literal -> {"this binary literal starts here", "the previous binary segment ends here"}
        :binary_generator -> {"this binary generator starts here", "its source expression ends here"}
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :lambda_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this lambda parameter list starts here"),
      pickup_label(previous, :secondary, "the previous lambda parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_arguments}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type arguments start here"),
      pickup_label(previous, :secondary, "the previous type argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type parameters start here"),
      pickup_label(previous, :secondary, "the previous type parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :constructor_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this constructor's parameter list starts here"),
      pickup_label(previous, :secondary, "the previous constructor parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :branch_block, family: family}
         },
         primary_span
       ) do
    opener_message =
      case family do
        :match -> "this inline match's branch block starts here"
        :with -> "this inline with's branch block starts here"
        :multi_with -> "this multi-scrutinee with's branch block starts here"
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the final branch ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_indices}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type indices start here"),
      pickup_label(previous, :secondary, "the previous type index ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       )
       when kind in [:call_unclosed, :call_argument_separator_missing] do
    [
      pickup_label(opener, :secondary, "this call's argument list starts here"),
      pickup_label(previous, :secondary, "the previous argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing, :container_trailing_separator] do
    item = container_item_name(Map.get(context, :container))

    [
      pickup_label(opener, :secondary, "this container starts here"),
      pickup_label(previous, :secondary, "the previous #{item} ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(%SyntaxProblem{opener: %Span{} = opener}, primary_span) when opener != primary_span,
    do: [%Label{span: opener, style: :secondary, message: "the construct starts here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :function_parameters_unparenthesized, previous: %Span{} = name},
         primary_span
       )
       when name != primary_span,
       do: [%Label{span: name, style: :secondary, message: "this function name needs a parameter list after it"}]

  defp syntax_secondary_labels(%SyntaxProblem{kind: kind, previous: %Span{} = previous}, primary_span)
       when kind in [:non_associative, :ambiguous_precedence] and previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the conflicting operator is here"}]

  defp syntax_secondary_labels(%SyntaxProblem{within: %Span{} = within}, primary_span) when within != primary_span,
    do: [%Label{span: within, style: :secondary, message: "while parsing this construct"}]

  defp syntax_secondary_labels(_problem, _primary_span), do: []

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :macro_use_mismatch,
           expected: {:literal, expected},
           context: %{token_type: token_type}
         },
         %Span{} = span
       )
       when token_type not in [:newline, :dedent, :eof] do
    [
      %Suggestion{
        message: "Replace it with `#{expected}`",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: to_string(expected)}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :function_parameters_unparenthesized, context: %{token_type: type}},
         %Span{} = span
       )
       when type in [:arrow, :assign, :newline, :eof] do
    insertion = %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

    [
      %Suggestion{
        message: "Insert `()` after the function name",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion, replacement: "()"}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :lambda_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `->` before the lambda body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "-> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           context: %{family: :induction_case, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=>` before the induction case body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :rewrite_using_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `using` before the equality proof",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "using "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :rewrite_in_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `in` before the expression to rewrite",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "in "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: kind, context: %{token_type: type}},
         %Span{} = span
       )
       when kind in [:macro_check_else_missing, :macro_check_fail_missing] and
              type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    {keyword, branch} =
      case kind do
        :macro_check_else_missing -> {"else", "the rejected branch"}
        :macro_check_fail_missing -> {"fail", "this failure value"}
      end

    [
      %Suggestion{
        message: "Insert `#{keyword}` before #{branch}",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{keyword} "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: kind, expected: expected, context: %{token_type: type}},
         %Span{} = span
       )
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] and type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `#{expected}` before this expression",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{expected} "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: kind, expected: expected}, %Span{})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] do
    [
      %Suggestion{
        message: "Add `#{expected}` and the expression that follows it",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_indent_missing}, %Span{}) do
    [
      %Suggestion{
        message: "Indent one or more family members below the declaration",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_member_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Replace this line with a typed field, an `includes` line, or a `syntax` production",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_entry_invalid, context: %{valid_fields: fields}}, %Span{}) do
    [
      %Suggestion{
        message: "Start this entry with one of: #{inline_choices(fields)}",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_production_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Rewrite this entry using one of the syntax family's declared production forms",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :syntax_family_body_indent_missing, context: %{valid_fields: fields}},
         %Span{}
       ) do
    [
      %Suggestion{
        message: "Indent a structured body starting with one of: #{inline_choices(fields)}",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_definition_entry_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Replace this line with a valid macro declaration entry",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_example_entry_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Write `example use_site expands expected` on this line",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_explain_point_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Write `Category => message` or `keyword \"word\" => message`",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           context: %{family: :explain_clause, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=>` before the explanation message",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :branch_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `->` before the branch body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "-> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :gadt_constructor_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the constructor signature",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :assert_type_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `:` before the expected type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :named_implicit_pattern_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the implicit pattern",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :local_binding_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the binding value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :where_block_indent_missing}, %Span{}),
    do: [
      %Suggestion{
        message: "Indent each local definition beneath `where`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :where_binding_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the local value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :map_entry_separator_missing, context: %{ambiguous: true}},
         %Span{}
       ) do
    [
      %Suggestion{
        message: "Choose `,` for two punned entries or `=>` for a key-value entry",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :map_entry_separator_missing,
           context: %{token_type: type} = context
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    container = Map.get(context, :container, :map)

    [
      %Suggestion{
        message: "Insert `=>` before the #{container} value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :binary_generator_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :binary_close, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `<-` before the generator source",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "<- "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :send_comma_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `,` before the send message",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :lift_callback_body_separator_missing,
           expected: expected,
           context: %{token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    separator = if expected == :assign, do: "=", else: "->"

    [
      %Suggestion{
        message: "Insert `#{separator}` before the callback body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{separator} "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_opener_missing,
           observed: observed,
           context: %{container: container, token_type: type}
         },
         %Span{} = span
       )
       when container in [:failure_parameters, :lift_callback_parameters] do
    empty? = type in [:arrow, :assign, :newline, :dedent, :eof] or observed in ["returns", :returns]
    insertion = if empty?, do: "()", else: "("
    message = if empty?, do: "Insert an empty `()` parameter list", else: "Insert `(` before the first parameter"

    [
      %Suggestion{
        message: message,
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: insertion}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_opener_missing,
           context: %{container: :macro_obligation_capture}
         },
         %Span{} = span
       ) do
    [
      %Suggestion{
        message: "Insert `(` before the constrained capture",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "("}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :with_rematch_separator_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :arrow, :rbrace] do
    [
      %Suggestion{
        message: "Insert `|` before the with-pattern",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "| "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :type_indices_opener_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `(` before the type indices",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "("}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :local_function_keyword_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `fn` before the local function name",
        applicability: :machine_applicable,
        edits: [
          %TextEdit{
            span: %{
              span
              | end_byte: span.start_byte,
                end_line: span.start_line,
                end_column: span.start_column
            },
            replacement: "fn "
          }
        ]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :implementation_for_keyword_missing, context: %{repair: :replace}},
         %Span{} = span
       ) do
    [
      %Suggestion{
        message: "Replace this keyword with `for`",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "for"}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :implementation_for_keyword_missing,
           context: %{repair: :insert, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    insertion_span = %{
      span
      | end_byte: span.start_byte,
        end_line: span.start_line,
        end_column: span.start_column
    }

    [
      %Suggestion{
        message: "Insert `for` before the implementation type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion_span, replacement: "for "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :record_field_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the field type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :fixity_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the precedence group",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :precedencegroup_field_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the setting value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :type_declaration_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent] do
    [
      %Suggestion{
        message: "Insert `=` before the type body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :refinement_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rbrace] do
    [
      %Suggestion{
        message: "Insert `:` before the refinement's base type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :refinement_bar_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rbrace] do
    [
      %Suggestion{
        message: "Insert `|` before the refinement proposition",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "| "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :refinement_binder_invalid}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case binder",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :sigma_binder_invalid}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case Sigma binder",
        applicability: :manual
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :sigma_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `:` before the first value's type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :sigma_comma_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `,` before the dependent result type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rparen, context: %{container: :type_parameters}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rparen, context: %{container: :type_indices}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rbrace, context: %{container: :named_implicit_pattern}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rbrace, context: %{container: :implicit_parameter}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: :binary_specifier_arguments}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rbrace,
           context: %{container: :selective_import}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: container}
         },
         %Span{} = span
       )
       when container in [:splice, :splice_group] do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: container}
         },
         %Span{} = span
       )
       when container in [:failure_parameters, :lift_callback_parameters] do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: :macro_obligation_capture}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(%SyntaxProblem{observed: :eof, expected: expected}, %Span{} = span) do
    closing_delimiter_insertion(expected, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: expected, context: %{token_type: token_type}},
         %Span{} = span
       )
       when token_type in [:dedent, :newline] do
    closing_delimiter_insertion(expected, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :mismatched_closer, expected: expected, observed: observed},
         %Span{} = span
       ) do
    replacement = syntax_insertion(expected)

    if replacement do
      [
        %Suggestion{
          message: "Replace #{syntax_name(observed)} with `#{replacement}`",
          applicability: :machine_applicable,
          edits: [%TextEdit{span: span, replacement: replacement}]
        }
      ]
    else
      []
    end
  end

  defp syntax_insertions(%SyntaxProblem{kind: kind}, %Span{})
       when kind in [:non_associative, :ambiguous_precedence],
       do: [
         %Suggestion{
           message: "Add parentheses around the operation that should happen first",
           applicability: :manual
         }
       ]

  defp syntax_insertions(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}, %Span{}),
    do: [
      %Suggestion{
        message: "Bind the value, then test its bounds with `when`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :missing_function_body}, %Span{}),
    do: [
      %Suggestion{
        message: "Write an expression after `=`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :invalid_parameter_name}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case parameter name",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :variadic_parameter_name_missing}, %Span{}),
    do: [
      %Suggestion{
        message: "Add a descriptive lower-case name after the variadic marker",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :call_argument_separator_missing}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Insert `,` between these arguments",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :map}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these entries",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :record}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these fields",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_arguments}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type arguments",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :constructor_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these constructor parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_indices}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type indices",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :lambda_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these lambda parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :selective_import}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these imported names",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: container}},
         %Span{} = span
       )
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: [
         %Suggestion{
           message: "Insert `,` between these type positions",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(%SyntaxProblem{kind: :container_separator_missing}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Insert `,` between these elements",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :container_trailing_separator}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Remove the trailing comma",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ""}]
      }
    ]

  defp syntax_insertions(_problem, _span), do: []

  defp closing_delimiter_insertion(expected, span) do
    case syntax_insertion(expected) do
      nil ->
        []

      replacement ->
        [
          %Suggestion{
            message: "Insert `#{replacement}` to close the construct",
            applicability: :machine_applicable,
            edits: [
              %TextEdit{
                span: %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column},
                replacement: replacement
              }
            ]
          }
        ]
    end
  end

  defp branch_family_name(:match_arm), do: "A pattern branch"
  defp branch_family_name(family) when family in [:pickup_clause, :pickup_else], do: "A pickup branch"
  defp branch_family_name(:function_clause), do: "A function clause"
  defp branch_family_name(family) when family in [:with_arm, :with_rematch_arm], do: "A with branch"

  defp refinement_previous_label(:refinement_bar_missing), do: "the base type ends here"
  defp refinement_previous_label(:refinement_unclosed), do: "the proposition ends here"
  defp refinement_previous_label(_kind), do: "this is the refinement binder"

  defp sigma_previous_label(:sigma_comma_missing), do: "the first value's type ends here"
  defp sigma_previous_label(:sigma_unclosed), do: "the dependent result type ends here"
  defp sigma_previous_label(_kind), do: "this is the Sigma binder"

  defp container_item_name(:map), do: "entry"
  defp container_item_name(:record), do: "field"
  defp container_item_name(:list_cons), do: "tail expression"
  defp container_item_name(:comprehension), do: "clause"
  defp container_item_name(:parameters), do: "parameter"
  defp container_item_name(:type_arguments), do: "type argument"
  defp container_item_name(:type_parameters), do: "type parameter"
  defp container_item_name(:constructor_parameters), do: "constructor parameter"
  defp container_item_name(:branch_block), do: "branch"
  defp container_item_name(:selective_import), do: "imported name"
  defp container_item_name(:type_indices), do: "type index"
  defp container_item_name(:lambda_parameters), do: "lambda parameter"

  defp container_item_name(container) when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
    do: "type position"

  defp container_item_name(:binary_literal), do: "binary segment"
  defp container_item_name(:binary_generator), do: "source expression"
  defp container_item_name(_container), do: "element"

  defp syntax_insertion(:rparen), do: ")"
  defp syntax_insertion(:rbracket), do: "]"
  defp syntax_insertion(:rbrace), do: "}"
  defp syntax_insertion(:binary_close), do: ">>"

  defp syntax_insertion(:end), do: "end"
  defp syntax_insertion(:double_quote), do: "\""
  defp syntax_insertion(:single_quote), do: "'"
  defp syntax_insertion(:backtick), do: "`"
  defp syntax_insertion(_expected), do: nil

  defp missing_delimiter_kind(:rparen, :eof), do: :unclosed_parentheses
  defp missing_delimiter_kind(:rbracket, :eof), do: :unclosed_brackets
  defp missing_delimiter_kind(:rbrace, :eof), do: :unclosed_braces

  defp missing_delimiter_kind(expected, observed)
       when expected in [:rparen, :rbracket, :rbrace] and observed in [:rparen, :rbracket, :rbrace],
       do: :mismatched_closer

  defp missing_delimiter_kind(_expected, _observed), do: :unexpected_token

  defp lex_problem({:tab_not_allowed, line, column}, opts),
    do: syntax_problem(:tab_not_allowed, nil, :tab, line, column, opts)

  defp lex_problem({:unterminated_string, line, column}, opts),
    do: syntax_problem(:unterminated_string, :double_quote, :eof, line, column, opts)

  defp lex_problem({:unterminated_char, line, column}, opts),
    do: syntax_problem(:unterminated_char, :single_quote, :eof, line, column, opts)

  defp lex_problem({:unterminated_quoted_identifier, line, column}, opts),
    do: syntax_problem(:unterminated_quoted_identifier, :backtick, :eof, line, column, opts)

  defp lex_problem({kind, line, column}, opts)
       when kind in [:invalid_hex_literal, :invalid_binary_literal, :invalid_float_literal],
       do: syntax_problem(:invalid_number, :digits, kind, line, column, opts)

  defp lex_problem({:invalid_char_escape, line, column}, opts),
    do: syntax_problem(:invalid_char_escape, :valid_escape, :escape, line, column, opts)

  defp lex_problem({:atom_too_long, line, column}, opts),
    do: syntax_problem(:atom_too_long, :shorter_atom, :atom, line, column, opts)

  defp lex_problem({:unexpected_character, character, line, column}, opts),
    do: syntax_problem(:unexpected_character, :token, character, line, column, opts)

  defp lex_problem({:obsolete_anonymous_hole, line, column}, opts),
    do: syntax_problem(:obsolete_anonymous_hole, :anonymous_hole, "??", line, column, opts)

  defp lex_problem(reason, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: {:lex_error, reason})

  defp syntax_problem(kind, expected, observed, line, column, opts) do
    %SyntaxProblem{
      kind: kind,
      expected: expected,
      observed: observed,
      at: Keyword.get(opts, :span),
      context: %{line: line, column: column}
    }
  end

  defp surface_type(type) when is_binary(type), do: type
  defp surface_type(type), do: print_core(type)

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp print_core(term) do
    term
    |> printable_core()
    |> Cure.Core.Printer.print()
  rescue
    ArgumentError -> inspect(term)
  end

  defp printable_core(term) when is_tuple(term) do
    case elem(term, 0) do
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

  # Parser errors retain token *kinds* for stable machine handling. Translate
  # punctuation and operators back to the spelling a user sees in the source;
  # `:arrow` and `:rparen` are implementation names, whereas `->` and `)` tell
  # the user precisely what needs attention.
  @syntax_token_spellings %{
    lparen: "(",
    rparen: ")",
    lbracket: "[",
    rbracket: "]",
    lbrace: "{",
    rbrace: "}",
    splice_open: "$(",
    tuple_open: "%[",
    map_open: "%{",
    binary_open: "<<",
    binary_close: ">>",
    comma: ",",
    semicolon: ";",
    colon: ":",
    colon_colon: "::",
    dot: ".",
    ellipsis: "...",
    range: "..",
    range_inclusive: "..=",
    arrow: "->",
    fat_arrow: "=>",
    assign: "=",
    plus_assign: "+=",
    minus_assign: "-=",
    star_assign: "*=",
    slash_assign: "/=",
    plus: "+",
    minus: "-",
    star: "*",
    slash: "/",
    eq: "==",
    neq: "!=",
    lt: "<",
    lte: "<=",
    gt: ">",
    gte: ">=",
    pipe: "|>",
    bar: "|",
    at: "@",
    caret: "^",
    percent: "%",
    bang: "!",
    string_concat: "<>",
    melquiades: "✉",
    double_quote: "\"",
    single_quote: "'",
    backtick: "`"
  }

  defp syntax_name(name) when is_map_key(@syntax_token_spellings, name),
    do: "'#{Map.fetch!(@syntax_token_spellings, name)}'"

  defp syntax_name(:eof), do: "the end of the file"
  defp syntax_name(:newline), do: "a new line"
  defp syntax_name(:indent), do: "an indented block"
  defp syntax_name(:dedent), do: "the end of this block"
  defp syntax_name(:expression), do: "an expression"
  defp syntax_name(:identifier), do: "an identifier"
  defp syntax_name(:keyword), do: "a keyword"
  defp syntax_name(:integer), do: "an integer"
  defp syntax_name(:positive_integer), do: "a positive integer"
  defp syntax_name(:failure_constructor), do: "a failure constructor call"
  defp syntax_name(:family_field), do: "a typed field"
  defp syntax_name(:syntax_family_production), do: "a declared family production"
  defp syntax_name(:failure_category), do: "a failure category"
  defp syntax_name(:float), do: "a number"
  defp syntax_name(:string), do: "a string"
  defp syntax_name(:char), do: "a character"
  defp syntax_name(:atom), do: "an atom"
  defp syntax_name(:bool), do: "a boolean"
  defp syntax_name(:hole), do: "a hole"
  defp syntax_name(:macro_hole), do: "a macro hole"
  defp syntax_name({:literal, value}), do: "the literal #{inspect(value)}"
  defp syntax_name(name) when is_binary(name), do: "'#{name}'"
  defp syntax_name(name) when is_atom(name), do: "'#{name}'"
  defp syntax_name(name), do: inspect(name)

  defp authored_syntax(value) when is_integer(value) or is_float(value), do: "'#{value}'"
  defp authored_syntax(value), do: syntax_name(value)

  defp inline_choices([]), do: "no fields"
  defp inline_choices(values), do: Enum.map_join(values, ", ", &"`#{&1}`")
end
