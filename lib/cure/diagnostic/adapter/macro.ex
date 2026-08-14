defmodule Cure.Diagnostic.Adapter.Macro do
  @moduledoc """
  Converts authored macro-family and expansion failures.

  Generated implementation details remain in payloads and provenance; primary
  labels point at authored macro syntax whenever a source span is available.
  """

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    Label,
    ProvenanceFrame,
    Span,
    Suggestion,
    TextEdit
  }

  alias Cure.Diagnostic.Suggest
  alias Cure.Diagnostic.SourceRegistry
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter
  alias Cure.MetaAST.Metadata

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:expected_literal_capture, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)
    article = article_for_kind(details.shape)

    Diagnostic.new(
      code: "E094",
      key: :macro_literal_capture,
      severity: :error,
      title: "Macro field needs a literal",
      body:
        Doc.paragraph(
          "This syntax-family field accepts #{article} `#{details.shape}` literal, not an expression of another shape."
        ),
      primary: label(span, :primary, "this is not #{article} `#{details.shape}` literal"),
      suggestions: [
        %Suggestion{message: "Replace this value with #{article} `#{details.shape}` literal", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:splice_outside_quote, tag, meta}, opts) when is_list(meta) do
    form = if tag == :splice_group, do: "$(e ...)", else: "$(e)"

    Diagnostic.new(
      code: "E108",
      key: :splice_outside_quote,
      severity: :error,
      title: "Splice outside quote",
      body: Doc.paragraph("The `#{form}` splice has no surrounding quote to receive generated syntax."),
      primary: label(Keyword.get(opts, :span), :primary, "place this splice inside a quote"),
      payload: %{form: tag, stage: :elaboration}
    )
  end

  def from_error({:splice_outside_quote, %{form: tag} = details}, opts)
      when tag in [:splice, :splice_group] do
    form = if tag == :splice_group, do: "$(expressions ...)", else: "$(expression)"
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E108",
      key: :splice_outside_quote,
      severity: :error,
      title: "Splice has no enclosing quote",
      body:
        Doc.paragraph(
          "`#{form}` inserts syntax into a surrounding `quote`, but this splice is in ordinary expression code. There is no quoted syntax tree here to receive its value."
        ),
      primary: label(span, :primary, "this splice is outside every `quote`"),
      suggestions: [
        %Suggestion{
          message: "Move this splice inside `quote ...`, or remove `$()` to evaluate an ordinary expression",
          applicability: :manual
        }
      ],
      payload: %{form: tag, stage: Map.get(details, :stage, :elaboration)}
    )
  end

  def from_error({:unknown_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_syntax_family_field,
      severity: :error,
      title: "Unknown syntax-family field",
      body: Doc.paragraph("`#{details.field}` is not a field of the `#{details.family}` syntax family."),
      primary:
        label(
          span,
          :primary,
          "this field is not declared by the family"
        ),
      suggestions: syntax_family_field_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:missing_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :missing_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is missing",
      body: Doc.paragraph("The `#{details.family}` syntax family requires a `#{details.field}` section here."),
      primary: label(span, :primary, "add `#{details.field}` here"),
      suggestions: [
        %Suggestion{
          message: "Add a `#{details.field} ...` section to this family body",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_macro_obligation_capture, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_macro_obligation_capture,
      severity: :error,
      title: "Unknown macro capture",
      body:
        Doc.paragraph(
          "The `#{details.interface}` obligation refers to `#{details.capture}`, but this rule declares no capture with that name."
        ),
      primary:
        label(
          span,
          :primary,
          "this capture is not declared by the rule"
        ),
      suggestions: macro_capture_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:unit_type_reserved, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :unit_span),
             :secondary,
             "this spelling denotes the built-in `Unit` type"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :unit_type_reserved,
      severity: :error,
      title: "Unit syntax cannot define another type",
      body: Doc.paragraph("`()` has exactly one type, `Unit`, so it cannot define the new type `#{details.name}`."),
      primary:
        label(
          span,
          :primary,
          "this declaration must not reuse `Unit` syntax"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give `#{details.name}` its own constructor, or rename the type to `Unit`",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:duplicate_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :first_span),
             :secondary,
             "the field was first supplied here"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :duplicate_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is duplicated",
      body: Doc.paragraph("The `#{details.field}` field may be supplied only once in this family body."),
      primary:
        label(
          span,
          :primary,
          "this second `#{details.field}` field is redundant"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Keep one `#{details.field}` section",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_packet_name,
             :invalid_packet_endian,
             :unknown_packet_scalar,
             :missing_packet_endian,
             :invalid_packet_field
           ],
      do: packet_failure(kind, %{detail: detail}, opts)

  def from_error({kind, field, dependency}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields],
      do: packet_failure(kind, %{field: field, dependency: dependency}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_packet_field, :invalid_packet_field_name, :duplicate_packet_field],
      do: packet_failure(kind, %{}, opts)

  def from_error({:invalid_driver_base, base}, opts),
    do: driver_failure(:invalid_driver_base, %{base: base}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_driver_register, :duplicate_driver_register, :overlapping_driver_register],
      do: driver_failure(kind, %{}, opts)

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
      do: board_failure(kind, %{detail: detail}, opts)

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
      do: board_failure(kind, %{}, opts)

  def from_error({:duplicate_unit, suffix}, opts),
    do: unit_failure(:duplicate_unit, %{suffix: suffix}, opts)

  def from_error({kind, detail}, opts) when kind in [:invalid_unit, :unknown_unit],
    do: unit_failure(kind, %{suffix: detail}, opts)

  def from_error({:invalid_unit_literal, value, suffix}, opts),
    do: unit_failure(:invalid_unit_literal, %{value: value, suffix: suffix}, opts)

  def from_error({:invalid_check_name, name}, opts),
    do: check_failure(:invalid_check_name, %{name: name}, opts)

  def from_error(kind, opts) when kind in [:invalid_check_property, :duplicate_check_property],
    do: check_failure(kind, %{}, opts)

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
      do: protocol_failure(kind, %{}, opts)

  def from_error({:invalid_protocol_name, name}, opts),
    do: protocol_failure(:invalid_protocol_name, %{name: name}, opts)

  def from_error({:protocol_role_count, count}, opts),
    do: protocol_failure(:protocol_role_count, %{count: count}, opts)

  def from_error({kind, role}, opts)
      when kind in [:self_protocol_step, :unknown_choice_decider, :invalid_protocol_branches, :unprojectable_choice],
      do: protocol_failure(kind, %{role: role}, opts)

  def from_error({:unknown_protocol_role, sender, receiver}, opts),
    do: protocol_failure(:unknown_protocol_role, %{sender: sender, receiver: receiver}, opts)

  def from_error({:invalid_parse_name, name}, opts),
    do: parse_failure(:invalid_parse_name, %{name: name}, opts)

  def from_error({:left_recursive_parse_production, names}, opts),
    do: parse_failure(:left_recursive_parse_production, %{names: names}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_parse_productions, :invalid_parse_production, :duplicate_parse_production],
      do: parse_failure(kind, %{}, opts)

  def from_error({:missing_raw_delimiter, delimiter}, opts),
    do: raw_failure(:missing_raw_delimiter, %{delimiter: delimiter}, opts)

  def from_error({:invalid_raw_delimiter, delimiter}, opts),
    do: raw_failure(:invalid_raw_delimiter, %{delimiter: delimiter}, opts)

  def from_error(:invalid_raw_tokens, opts),
    do: raw_failure(:invalid_raw_tokens, %{}, opts)

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
      do: syntax_integrity_failure(kind, path, opts)

  def from_error({:unknown_reducer_constructor, constructors}, opts),
    do: reducer_failure(:unknown_reducer_constructor, %{constructors: constructors}, opts)

  def from_error({:incomplete_reducer, constructors}, opts),
    do: reducer_failure(:incomplete_reducer, %{constructors: constructors}, opts)

  def from_error({:reducer_arity, constructor, actual, expected}, opts),
    do: reducer_failure(:reducer_arity, %{constructor: constructor, actual: actual, expected: expected}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_reducer_arms, :invalid_reducer_arm, :duplicate_reducer_constructor],
      do: reducer_failure(kind, %{}, opts)

  def from_error({:invalid_syntax_node, _attrs, _kids}, opts),
    do: syntax_decode_failure(:invalid_syntax_node, %{}, opts)

  def from_error({:invalid_syntax_node, _detail}, opts),
    do: syntax_decode_failure(:invalid_syntax_node, %{}, opts)

  def from_error({:invalid_syntax_leaf, tag}, opts),
    do: syntax_decode_failure(:invalid_syntax_leaf, %{tag: tag}, opts)

  def from_error({:invalid_syntax_failure, name}, opts),
    do: syntax_decode_failure(:invalid_syntax_failure, %{name: name}, opts)

  def from_error({:unsupported_syntax_core, _term}, opts),
    do: syntax_decode_failure(:unsupported_syntax_core, %{}, opts)

  def from_error({:invalid_syntax_attrs, _core}, opts),
    do: syntax_decode_failure(:invalid_syntax_attrs, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: syntax_decode_failure(kind, %{}, opts)

  def from_error({:closed_category_extension, categories}, opts),
    do: module_failure(:closed_category_extension, %{categories: categories}, opts)

  def from_error({:ambiguous_macro_extension, keywords}, opts),
    do: module_failure(:ambiguous_macro_extension, %{keywords: keywords}, opts)

  def from_error({:invalid_macro_family, details}, opts) when is_map(details),
    do: family_failure(details, opts)

  def from_error({kind, _detail}, opts) when kind in [:module_rule_not_fully_consumed, :not_a_module_rule],
    do: module_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :module_rule_not_fully_consumed,
             :not_a_module_rule,
             :invalid_module_rule_set,
             :invalid_module_rule_bindings,
             :invalid_macro_extension_rules,
             :invalid_macro_extension_rule
           ],
      do: module_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_macro_rules,
             :expander_without_accepts,
             :accepts_without_syntax_family,
             :accepts_without_expander,
             :multiple_accepts_declarations,
             :multiple_expands_declarations
           ],
      do: family_failure(kind, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :unknown_syntax_family,
             :duplicate_syntax_family,
             :duplicate_syntax_family_field,
             :syntax_family_cycle
           ],
      do: family_failure({kind, detail}, opts)

  def from_error({kind, _detail}, opts)
      when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
      do: diagnostic_schema_failure(kind, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_macro_segment,
             :unsupported_surface_filler,
             :missing_hole_filler,
             :invalid_repeated_hole_filler
           ],
      do: fuzz_input_failure(kind, %{detail: detail}, opts)

  def from_error(kind, opts) when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
    do: diagnostic_schema_failure(kind, opts)

  def from_error(kind, opts)
      when kind in [:not_a_nat, :invalid_macro_fuzz_rule, :invalid_macro_fuzz_bindings],
      do: fuzz_input_failure(kind, %{}, opts)

  def from_error({:missing_diagnosis, points}, opts), do: validation_failure(:missing_diagnosis, points, opts)
  def from_error({:rule_unpinned, keywords}, opts), do: validation_failure(:rule_unpinned, keywords, opts)

  def from_error({:example_mismatch, mismatches}, opts),
    do: validation_failure(:example_mismatch, mismatches, opts)

  def from_error({:example_type_mismatch, failures}, opts),
    do: validation_failure(:example_type_mismatch, failures, opts)

  def from_error({:computed_example_error, failures}, opts),
    do: validation_failure(:computed_example_error, failures, opts)

  def from_error({:source_context, {:missing_diagnosis, points}, context}, opts) when is_map(context),
    do: validation_failure(:missing_diagnosis, points, opts, context)

  def from_error({:source_context, {:rule_unpinned, keywords}, context}, opts) when is_map(context),
    do: validation_failure(:rule_unpinned, keywords, opts, context)

  def from_error({:source_context, {:example_mismatch, mismatches}, context}, opts) when is_map(context),
    do: validation_failure(:example_mismatch, mismatches, opts, context)

  def from_error({:source_context, {:example_type_mismatch, failures}, context}, opts) when is_map(context),
    do: validation_failure(:example_type_mismatch, failures, opts, context)

  def from_error({:source_context, {:computed_example_error, failures}, context}, opts) when is_map(context),
    do: validation_failure(:computed_example_error, failures, opts, context)

  def from_error({:source_context, {:reserved_syntax_field, field, keywords}, context}, opts) when is_map(context),
    do: validation_failure(:reserved_syntax_field, %{first: field, second: keywords}, opts, context)

  def from_error({:source_context, {:unsupported_hole_type, category}, context}, opts) when is_map(context),
    do: validation_failure(:unsupported_hole_type, %{detail: category}, opts, context)

  def from_error({kind, _detail}, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: syntax_decode_failure(kind, %{}, opts)

  def from_error({:macro_expansion_cycle, frames}, opts)
      when is_list(frames),
      do:
        macro_expansion_failure(
          :cycle,
          "Macro expansion is recursive and did not reach a stable result.",
          frames,
          opts
        )

  def from_error({:macro_expansion_budget, kind, frames}, opts)
      when is_atom(kind) and is_list(frames),
      do:
        macro_expansion_failure(
          {:budget, kind},
          "Macro expansion exceeded its #{kind} limit.",
          frames,
          opts
        )

  def from_error({:expansion_ill_typed, details}, opts)
      when is_map(details) do
    keyword = Map.get(details, :keyword, "computed")

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Macro expansion proof failed",
      body: Doc.paragraph("The `#{keyword}` macro generated code that does not satisfy the dependent elaborator."),
      primary:
        label(
          Keyword.get(opts, :span),
          :primary,
          "this macro invocation generated the invalid expansion"
        ),
      notes: [
        "Edit the authored macro invocation; generated code is an implementation detail."
      ],
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        keyword: keyword,
        input: Map.get(details, :input),
        expansion: Map.get(details, :expansion),
        reason:
          inspect(
            Map.get(details, :kernel_error) ||
              Map.get(details, :reason)
          )
      }
    )
  end

  def from_error(error, _opts),
    do: raise(Cure.Diagnostic.UnhandledError, error: error)

  @doc false
  def packet_failure(kind, details, opts) do
    {title, message, label_text, hint} = packet_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_packet_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def driver_failure(kind, details, opts) do
    {title, message, label_text, hint} = driver_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_driver_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp computed_macro_failure(meta, {:host_exception, exception}, opts) do
    keyword = Keyword.get(meta, :keyword, "computed")
    source_info = Metadata.source_info(meta)
    span = (source_info && source_info.whole) || Keyword.get(opts, :span)
    provenance = ((source_info && source_info.provenance) || []) ++ Keyword.get(opts, :provenance, [])
    exception_name = exception |> name_to_string() |> String.trim_leading("Elixir.")

    internal_context =
      Cure.Diagnostic.InternalContext.normalize(%{
        declaration: keyword,
        span: span,
        provenance: provenance
      })

    fingerprint =
      diagnostic_fingerprint({:computed_macro_host_exception, keyword, exception, internal_context})

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Compiler failed while running a computed macro",
      body:
        Doc.paragraph(
          "The compiler raised `#{exception_name}` while evaluating the `#{keyword}` macro. This is a compiler defect, not a type or syntax error in the generated expansion. Diagnostic fingerprint: `#{fingerprint}`."
        ),
      primary: label(span, :primary, "this invocation reached the failing compiler path"),
      notes: ["Report this internal compiler failure with the diagnostic fingerprint."],
      suggestions: [
        %Suggestion{
          message: "Report fingerprint `#{fingerprint}` together with this source file",
          applicability: :manual
        }
      ],
      provenance: provenance,
      payload:
        internal_context
        |> Map.merge(%{
          stage: :computed_macro_expansion,
          macro: keyword,
          exception: exception_name,
          fingerprint: fingerprint
        })
        |> maybe_put_meta_location(meta)
    )
  end

  defp computed_macro_failure(meta, reason, opts) do
    keyword = Keyword.get(meta, :keyword, "computed")
    payload = %{keyword: keyword, reason: computed_macro_payload(reason)} |> maybe_put_meta_location(meta)
    source_info = Metadata.source_info(meta)
    invocation_span = (source_info && source_info.whole) || Keyword.get(opts, :span)
    {span, selected_authored_syntax?} = computed_macro_primary_span(reason, invocation_span, opts)
    provenance = ((source_info && source_info.provenance) || []) ++ Keyword.get(opts, :provenance, [])
    {title, message, primary_message, note} = computed_macro_content(keyword, reason)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary:
        label(
          span,
          :primary,
          if(selected_authored_syntax?, do: "this captured syntax was rejected by the macro", else: primary_message)
        ),
      notes: [note],
      suggestions: computed_macro_suggestions(reason),
      provenance: provenance,
      payload: payload
    )
  end

  defp computed_macro_primary_span({:author_diagnostics, diagnostics}, fallback, opts)
       when is_list(diagnostics) do
    case Enum.find_value(diagnostics, &author_diagnostic_primary_span(&1, opts)) do
      %Span{} = span -> {span, true}
      _ -> {fallback, false}
    end
  end

  defp computed_macro_primary_span(_reason, fallback, _opts), do: {fallback, false}

  defp author_diagnostic_primary_span({:macro_failure, _name, arguments}, opts) when is_list(arguments) do
    Enum.find_value(arguments, &diagnostic_argument_span(&1, opts))
  end

  defp author_diagnostic_primary_span(_diagnostic, _opts), do: nil

  defp diagnostic_argument_span(
         {:diagnostic_subspan, selector_meta, [target]},
         opts
       )
       when is_list(selector_meta) do
    with start when is_integer(start) and start >= 0 <- Keyword.get(selector_meta, :relative_start),
         length when is_integer(length) and length >= 0 <- Keyword.get(selector_meta, :relative_length),
         %Span{} = base <- syntax_span(target),
         %SourceRegistry{} = registry <- Keyword.get(opts, :source_registry),
         source_id when not is_nil(source_id) <- diagnostic_source_id(registry, base.source_id, opts),
         {:ok, source} <- SourceRegistry.fetch(registry, source_id),
         true <- base.start_byte >= 0 and base.end_byte <= byte_size(source),
         fragment <- binary_part(source, base.start_byte, base.end_byte - base.start_byte),
         true <- start + length <= String.length(fragment),
         prefix <- String.slice(fragment, 0, start),
         selected <- String.slice(fragment, start, length),
         {:ok, span} <-
           SourceRegistry.span(
             registry,
             source_id,
             base.start_byte + byte_size(prefix),
             base.start_byte + byte_size(prefix) + byte_size(selected)
           ) do
      span
    else
      _ -> nil
    end
  end

  defp diagnostic_argument_span(target, _opts), do: syntax_span(target)

  defp diagnostic_source_id(registry, source_id, opts) do
    case SourceRegistry.fetch(registry, source_id) do
      {:ok, _source} ->
        source_id

      :error ->
        source_file = Keyword.get(opts, :source_file)
        if match?({:ok, _}, SourceRegistry.fetch(registry, source_file)), do: source_file, else: nil
    end
  end

  defp syntax_span({_tag, meta, _third}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %{whole: %Span{} = span} -> span
      _ -> nil
    end
  end

  defp syntax_span(_target), do: nil

  def computed_macro_error(meta, reason, opts) when is_list(meta),
    do: computed_macro_failure(meta, reason, opts)

  def lift_module_error(details, opts) when is_map(details) do
    macro = get_in(details, [:source_provenance, :macro]) || :macro
    cause = Map.get(details, :cause)

    case TypeAdapter.from_family_error(cause, details, opts) do
      {:ok, diagnostic} ->
        diagnostic

      :error ->
        cause_diagnostic = Cure.Diagnostic.Adapter.from_error(cause)

        Diagnostic.new(
          code: "E092",
          key: :macro_expansion_failed,
          severity: :error,
          title: "#{macro_title(macro)} expansion failed",
          message: macro_failure_message(macro, details.module, cause_diagnostic),
          primary:
            label(
              Keyword.get(opts, :span),
              :primary,
              "this `#{macro}` declaration generated the failing module"
            ),
          notes: [
            "The generated module is an implementation detail; edit the authored `#{macro}` declaration instead."
          ],
          provenance: provenance_frames(details, opts),
          payload: %{
            macro: name_to_string(macro),
            module: name_to_string(details.module),
            behaviour: Map.get(details, :behaviour),
            cause: %{code: cause_diagnostic.code, key: cause_diagnostic.key, payload: cause_diagnostic.payload}
          }
        )
    end
  end

  def expansion_proof_failure(details, context, opts) do
    keyword = Map.get(details, :keyword, Map.get(context, :keyword, "computed"))
    rule_kind = Map.get(context, :rule_kind)
    source = if rule_kind == :computed, do: "computed expander", else: "expansion template"

    payload = %{
      keyword: keyword,
      macro: Map.get(context, :macro),
      rule_kind: rule_kind,
      shrunk_hole: Map.get(details, :shrunk_hole)
    }

    payload =
      if Keyword.get(opts, :debug, false) do
        Map.merge(payload, %{
          generated_input: Map.get(details, :input),
          generated_bindings: Map.get(details, :generated_bindings),
          expansion: Map.get(details, :expansion),
          internal_reason: Map.get(details, :kernel_error) || Map.get(details, :reason)
        })
      else
        payload
      end

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Macro rule can generate ill-typed code",
      body:
        Doc.paragraph("The `#{keyword}` rule has a generated counterexample that the dependent elaborator rejects."),
      primary: label(Map.get(context, :span), :primary, "this #{source} produces the invalid expansion"),
      suggestions: [
        %Suggestion{
          message: "Fix the `#{keyword}` rule so every accepted input produces well-typed Cure code",
          applicability: :manual
        }
      ],
      notes: ["The generated counterexample and internal elaboration reason are available in debug output."],
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  def generated_hole_invariant_failure(details, context, opts) do
    category = Map.get(details, :category, Map.get(context, :category, "unknown"))
    hole = Map.get(details, :hole, Map.get(context, :hole))
    fingerprint = diagnostic_fingerprint({:generated_hole_not_well_typed, category, hole, Map.get(details, :term)})

    payload = %{
      kind: :generated_hole_not_well_typed,
      macro: Map.get(context, :macro),
      category: category,
      hole: hole,
      fingerprint: fingerprint
    }

    payload =
      if Keyword.get(opts, :debug, false),
        do: Map.put(payload, :generated_term, Map.get(details, :term)),
        else: payload

    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      context
      |> Map.get(:hole_spans, [])
      |> Enum.map(&label(&1, :secondary, "this hole is affected by the same generator failure"))
      |> Enum.reject(&(&1.span == primary_span))

    Diagnostic.new(
      code: "E092",
      key: :macro_validation_failed,
      severity: :error,
      title: "Macro proof generator produced an invalid value",
      body:
        Doc.paragraph(
          "The compiler's `#{name_to_string(category)}` proof generator produced a value that failed its own type check. This is not an error in the macro declaration."
        ),
      primary: label(primary_span, :primary, "proof generation failed while checking this hole"),
      secondary: secondary,
      notes: ["Internal diagnostic fingerprint: #{fingerprint}."],
      suggestions: [
        %Suggestion{
          message: "Report this compiler defect with fingerprint `#{fingerprint}`",
          applicability: :manual
        }
      ],
      payload: payload
    )
  end

  def lift_module_validation(kind, details, opts) do
    {title, message, label_text, hint} = lift_module_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :lift_module_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, Keyword.get(opts, :label, label_text)),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp lift_module_content(:invalid_lift_module, _details),
    do:
      {"Lifted module request is malformed", "BEAM emission expected a validated lifted-module request.",
       "rewrite this lifted module request", "Build the request from a valid `lift module` declaration"}

  defp lift_module_content(:invalid_lift_module_ast, _details),
    do:
      {"Lifted module syntax is malformed",
       "A lifted module must be represented by one well-formed `lift_module` syntax node.",
       "rewrite this lifted module", "Use a `lift module` declaration with a name and body"}

  defp lift_module_content(:invalid_lift_module_name, %{detail: name}),
    do:
      {"Lifted module name is outside Cure",
       "The generated module `#{name_to_string(name)}` is not beneath the `Cure` namespace required for lifted code.",
       "move this module beneath `Cure`", "Use a module name beginning with `Cure.`"}

  defp lift_module_content(:invalid_module_name, %{detail: name}),
    do:
      {"Lifted module name is invalid",
       "`#{name_to_string(name)}` is not a valid qualified module name; every segment must begin with an uppercase letter.",
       "replace this lifted module name", "Use a name such as `Cure.Generated.Worker`"}

  defp lift_module_content(:invalid_behaviour, %{detail: behaviour}),
    do:
      {"Lifted module behaviour is invalid",
       "A lifted module needs a non-empty atom naming its BEAM behaviour, but this declaration uses `#{name_to_string(behaviour)}`.",
       "replace this behaviour", "Use the atom naming the implemented BEAM behaviour"}

  defp lift_module_content(:invalid_lift_callback, _details),
    do:
      {"Lifted module callback is malformed",
       "Every lifted callback needs an atom name, a non-negative arity, parameters, return type, body, and source line.",
       "rewrite this lifted callback", "Provide a complete callback declaration matching the behaviour"}

  defp lift_module_content(:invalid_lift_declaration, _details),
    do:
      {"Lifted module declaration is malformed",
       "Every declaration copied into a lifted module must be quoted Cure syntax.", "rewrite this lifted declaration",
       "Provide quoted declaration nodes in the lifted module body"}

  defp lift_module_content(:invalid_lift_import, _details),
    do:
      {"Lifted module import is malformed", "Every lifted-module dependency must be a textual qualified module name.",
       "rewrite this lifted import", "Use qualified import names such as `Std.Actor`"}

  defp lift_module_content(:invalid_lift_inheritance, _details),
    do:
      {"Lifted module inheritance option is invalid", "The `inherit_imports` option must be either `true` or `false`.",
       "replace this inheritance option", "Use `true` to inherit enclosing imports or `false` to isolate them"}

  defp lift_module_content(:lifted_module_dependency_cycle, %{detail: name}),
    do:
      {"Lifted modules form a dependency cycle",
       "The generated module `#{name_to_string(name)}` is reached again while ordering lifted-module dependencies.",
       "break this lifted-module cycle", "Remove or redirect one dependency in the cycle"}

  defp lift_module_content(:duplicate_lifted_module, %{detail: name}),
    do:
      {"Lifted module name is repeated",
       "More than one generated declaration produces `#{name_to_string(name)}`, so the compiler cannot choose one module body.",
       "rename one lifted module", "Give every lifted module a unique qualified name"}

  defp driver_content(:invalid_driver_base, %{base: base}) do
    {"Driver base address is invalid",
     "A driver base address must be a non-negative integer, but this definition uses `#{name_to_string(base)}`.",
     "replace this base address", "Use the non-negative byte address where this device's register block begins"}
  end

  defp driver_content(:invalid_driver_register, _details) do
    {"Driver register is malformed",
     "Every register needs a name, a non-negative byte offset, an 8-, 16-, or 32-bit width, and `read`, `write`, or `read_write` access.",
     "rewrite this register declaration", "Provide `name`, `offset`, `width`, and `access` for every register"}
  end

  defp driver_content(:duplicate_driver_register, _details) do
    {"Driver register name is repeated", "Two registers have the same name, so generated accessors would collide.",
     "rename or remove this repeated register", "Give every register a unique name"}
  end

  defp driver_content(:overlapping_driver_register, _details) do
    {"Driver register ranges overlap",
     "Two registers occupy at least one of the same bytes in the device register map.",
     "move or resize one of these registers", "Choose offsets and widths whose byte ranges do not overlap"}
  end

  @doc false
  def board_failure(kind, details, opts) do
    {title, message, label_text, hint} = board_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_board_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp board_content(:invalid_board_definition, _details) do
    {"Board definition is malformed",
     "A board definition must be a map containing its chip, pins, capabilities, buses, and flash layout.",
     "rewrite this board definition",
     "Provide a board definition map with `chip`, `pins`, `capabilities`, `buses`, and `flash`"}
  end

  defp board_content(:invalid_board_name, %{detail: name}) do
    {"Board name is invalid",
     "A board name must be an atom or string, but this definition uses `#{name_to_string(name)}`.",
     "replace this board name", "Use a stable board name such as `Esp32c3`"}
  end

  defp board_content(:missing_board_chip, _details) do
    {"Board chip is missing", "The board definition does not identify the chip that owns its pins and peripherals.",
     "add this board's chip", "Add a `chip` entry such as `chip: :esp32c3`"}
  end

  defp board_content(:invalid_board_chip, %{detail: chip}) do
    {"Board chip is invalid",
     "A chip identifier must be an atom or string, but this definition uses `#{name_to_string(chip)}`.",
     "replace this chip identifier", "Use a stable chip identifier such as `esp32c3`"}
  end

  defp board_content(:invalid_board_pins, _details) do
    {"Board pin set is invalid", "Pins must be a non-negative inclusive range or a list of non-negative pin numbers.",
     "fix this pin set", "Use `{first, last}` or a list such as `[0, 1, 2]`"}
  end

  defp board_content(:unknown_board_pin, %{detail: pin}) do
    {"Capability refers to an unknown board pin",
     "Pin `#{name_to_string(pin)}` has capabilities here, but it is not present in the board's pin set.",
     "declare this pin or remove its capabilities",
     "Add pin `#{name_to_string(pin)}` to `pins`, or remove this capability entry"}
  end

  defp board_content(:invalid_board_capability, %{detail: pin}) do
    {"Board pin has an invalid capability",
     "Pin `#{name_to_string(pin)}` has a capability outside the supported GPIO, analog, strapping, USB, and touch set.",
     "fix this pin's capabilities", "Use only `input`, `output`, `adc`, `dac`, `strapping`, `usb`, or `touch`"}
  end

  defp board_content(:invalid_board_capabilities, _details) do
    {"Board capabilities are malformed",
     "Board capabilities must be a map from each pin number to a list of supported capabilities.",
     "rewrite this capability map", "Map each pin to its capabilities, for example pin `8` to `input` and `output`"}
  end

  defp board_content(:invalid_board_bus, %{detail: bus}) do
    {"Board bus wiring is invalid",
     "The `#{name_to_string(bus)}` bus needs an atom name and a map from signal names to pin numbers.",
     "rewrite this bus wiring", "Map each signal to its pin, for example `sda` to `8` and `scl` to `9`"}
  end

  defp board_content(:unknown_bus_pin, %{detail: bus}) do
    {"Board bus uses an unknown pin",
     "The `#{name_to_string(bus)}` bus assigns at least one pin that is not present in the board's pin set.",
     "fix this bus pin assignment", "Assign every `#{name_to_string(bus)}` signal to a pin declared by `pins`"}
  end

  defp board_content(:missing_bus_capability, %{detail: bus}) do
    {"Board bus pin has no capability declaration",
     "The `#{name_to_string(bus)}` bus uses a declared pin whose capabilities are missing, so generated peripheral checks cannot validate it.",
     "declare capabilities for every bus pin", "Add each `#{name_to_string(bus)}` pin to the `capabilities` map"}
  end

  defp board_content(:invalid_board_buses, _details) do
    {"Board bus table is malformed", "Board buses must be a map from bus names to signal-to-pin wiring maps.",
     "rewrite this bus table", "Map each bus name to its signal-to-pin wiring"}
  end

  defp board_content(:invalid_board_flash, _details) do
    {"Board flash layout is malformed",
     "Flash layout needs a positive total size and non-negative application and library offsets.",
     "fix this flash layout", "Provide integer `size`, `app_offset`, and `libs_offset` values"}
  end

  defp board_content(:flash_offset_out_of_bounds, _details) do
    {"Board flash offset is outside the device",
     "The application or library partition starts at or beyond the declared flash size.",
     "move this partition inside flash", "Choose `app_offset` and `libs_offset` values smaller than `size`"}
  end

  @doc false
  def unit_failure(kind, details, opts) do
    {title, message, label_text, hint} = unit_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_unit_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp unit_content(:duplicate_unit, %{suffix: suffix}) do
    {"Unit suffix is already declared",
     "The `#{name_to_string(suffix)}` suffix is registered more than once, so a literal would have two possible scales.",
     "rename or remove this unit declaration",
     "Keep exactly one declaration for the `#{name_to_string(suffix)}` suffix"}
  end

  defp unit_content(:invalid_unit, %{suffix: suffix}) do
    {"Unit declaration is invalid",
     "The `#{name_to_string(suffix)}` unit needs a text suffix, a positive numeric scale, and an atom naming its dimension.",
     "fix this unit declaration", "Use a positive scale and a stable dimension such as `duration`"}
  end

  defp unit_content(:unknown_unit, %{suffix: suffix}) do
    {"Unit suffix is unknown",
     "The `#{name_to_string(suffix)}` suffix is used by this literal, but no unit with that suffix is registered.",
     "declare this unit or change the suffix", "Register `#{name_to_string(suffix)}` before using it in a literal"}
  end

  defp unit_content(:invalid_unit_literal, %{value: value, suffix: suffix}) do
    {"Unit literal is malformed",
     "A unit literal needs a numeric value and a text suffix, but this one uses value `#{name_to_string(value)}` and suffix `#{name_to_string(suffix)}`.",
     "rewrite this unit literal", "Use a number followed by a registered text suffix"}
  end

  @doc false
  def check_failure(kind, details, opts) do
    {title, message, label_text, hint} = check_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_check_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp check_content(:invalid_check_name, %{name: name}) do
    {"Check plan name is invalid",
     "A generated check plan needs an atom or text name, but this plan uses `#{name_to_string(name)}`.",
     "replace this check plan name", "Use a stable name such as `FrameProperties`"}
  end

  defp check_content(:invalid_check_property, _details) do
    {"Check property is malformed",
     "Every check property needs a name, a supported check kind, and the expression to test.",
     "rewrite this check property",
     "Provide `name`, `kind`, and `expression`; use `round_trip`, `total`, `fault_rejection`, `exhaustive`, or `termination`"}
  end

  defp check_content(:duplicate_check_property, _details) do
    {"Check property name is repeated",
     "Two properties in this check plan have the same name, so their generated results cannot be distinguished.",
     "rename or remove this property", "Give every property in the check plan a unique name"}
  end

  @doc false
  def protocol_failure(kind, details, opts) do
    {title, message, label_text, hint} = protocol_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_protocol_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp protocol_content(:invalid_protocol_name, %{name: name}),
    do:
      {"Protocol name is invalid",
       "A protocol name must be an atom or text, but this definition uses `#{name_to_string(name)}`.",
       "replace this protocol name", "Use a stable protocol name such as `Provisioning`"}

  defp protocol_content(:protocol_role_count, %{count: count}) do
    noun = if count == 1, do: "role", else: "roles"

    {"Protocol needs exactly two roles",
     "This two-party protocol declares #{count} #{noun}, but it must declare exactly two.",
     "make this a two-party protocol", "Keep exactly two distinct role names"}
  end

  defp protocol_content(:unknown_protocol_role, %{sender: sender, receiver: receiver}),
    do:
      {"Protocol step uses an unknown role",
       "The step from `#{name_to_string(sender)}` to `#{name_to_string(receiver)}` names an endpoint outside this protocol.",
       "use the declared protocol roles", "Choose both endpoints from the protocol's two declared roles"}

  defp protocol_content(:self_protocol_step, %{role: role}),
    do:
      {"Protocol step sends to itself",
       "The `#{name_to_string(role)}` endpoint is both sender and receiver in this step.",
       "choose the opposite receiver", "Send each message from one role to the other"}

  defp protocol_content(:unknown_choice_decider, %{role: role}),
    do:
      {"Protocol choice has an unknown decider",
       "The `#{name_to_string(role)}` role decides this choice but is not an endpoint in the protocol.",
       "use a declared role as decider", "Choose one of the protocol's two roles as the decider"}

  defp protocol_content(:invalid_protocol_branches, %{role: role}),
    do:
      {"Protocol choice has no valid branches",
       "The choice decided by `#{name_to_string(role)}` needs a non-empty list of protocol-step branches.",
       "add the possible branches", "Provide at least one branch beginning with a send from the decider"}

  defp protocol_content(:unprojectable_choice, %{role: role}),
    do:
      {"Protocol choice cannot be projected",
       "Every branch decided by `#{name_to_string(role)}` must begin with that role sending a message, so the other endpoint can observe the choice.",
       "make the decider announce each branch", "Start every branch with a message sent by `#{name_to_string(role)}`"}

  defp protocol_content(:invalid_protocol_roles, _details),
    do:
      {"Protocol roles are malformed",
       "A protocol's roles must be written as a list containing its two endpoint names.", "rewrite this role list",
       "Provide exactly two distinct atom role names"}

  defp protocol_content(:invalid_protocol_role, _details),
    do:
      {"Protocol role name is invalid",
       "Every protocol role must be an atom so generated endpoint names remain stable.", "replace this role name",
       "Use atom role names such as `client` and `server`"}

  defp protocol_content(:duplicate_protocol_role, _details),
    do:
      {"Protocol role is repeated",
       "Both endpoints have the same role name, so sends and receives cannot identify opposite parties.",
       "rename one protocol role", "Give the two endpoints distinct role names"}

  defp protocol_content(:invalid_protocol_steps, _details),
    do:
      {"Protocol steps are malformed", "A protocol's message flow must be a list of ordered send steps.",
       "rewrite this step list", "Provide a list of steps with `sender`, `receiver`, and `message`"}

  defp protocol_content(:invalid_protocol_step, _details),
    do:
      {"Protocol step is malformed", "Every protocol step needs both a sender and a receiver from this protocol.",
       "rewrite this protocol step", "Provide `sender`, `receiver`, and `message` for this step"}

  defp protocol_content(:invalid_protocol_message, _details),
    do:
      {"Protocol message is missing", "This step has no message for its sender to transmit to its receiver.",
       "add this step's message", "Add a message declaration to this protocol step"}

  defp protocol_content(:invalid_protocol_options, _details),
    do:
      {"Protocol options are malformed",
       "Protocol options must be a keyword list containing optional choices and timeout settings.",
       "rewrite these protocol options", "Use keyword options such as `choices: [...]` or `timeout: 1000`"}

  defp protocol_content(:invalid_protocol_choices, _details),
    do:
      {"Protocol choices are malformed", "The protocol's choices must be a list of branching decisions.",
       "rewrite this choice list", "Provide a list of choices with `decider` and non-empty `branches`"}

  defp protocol_content(:invalid_protocol_choice, _details),
    do:
      {"Protocol choice is malformed",
       "Every protocol choice needs the role that decides it and its possible branches.",
       "rewrite this protocol choice", "Provide `decider` and a non-empty `branches` list"}

  @doc false
  def parse_failure(kind, details, opts),
    do: simple_macro_failure(:macro_parse_validation, kind, parse_content(kind, details), opts)

  @doc false
  def raw_failure(kind, details, opts),
    do: simple_macro_failure(:macro_raw_validation, kind, raw_content(kind, details), opts)

  defp simple_macro_failure(key, kind, {title, message, label_text, hint}, opts) do
    Diagnostic.new(
      code: "E092",
      key: key,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind}
    )
  end

  defp parse_content(:invalid_parse_name, %{name: name}),
    do:
      {"Parser grammar name is invalid",
       "A generated parser grammar needs an atom or text name, but this grammar uses `#{name_to_string(name)}`.",
       "replace this grammar name", "Use a stable grammar name such as `Command`"}

  defp parse_content(:invalid_parse_productions, _details),
    do:
      {"Parser productions are malformed", "A parser grammar's productions must be provided as an ordered list.",
       "rewrite this production list", "Provide a list of named parser productions"}

  defp parse_content(:invalid_parse_production, _details),
    do:
      {"Parser production is malformed",
       "Every parser production needs an atom or text name and a non-empty body of token or production names.",
       "rewrite this parser production", "Provide `name` and a non-empty `body` list"}

  defp parse_content(:duplicate_parse_production, _details),
    do:
      {"Parser production name is repeated",
       "Two productions in this grammar have the same name, so references to that production would be ambiguous.",
       "rename or remove this production", "Give every production in the grammar a unique name"}

  defp parse_content(:left_recursive_parse_production, %{names: names}) do
    rendered = Enum.map_join(names, ", ", &"`#{name_to_string(&1)}`")
    {verb, reflexive} = if length(names) == 1, do: {"begins", "itself"}, else: {"begin", "themselves"}

    {"Parser production is left-recursive",
     "#{rendered} #{verb} by invoking #{reflexive}, so recursive descent would make no progress before recurring.",
     "remove this leading self-reference", "Rewrite the production so it consumes a token before recurring"}
  end

  defp raw_content(:missing_raw_delimiter, %{delimiter: delimiter}),
    do:
      {"Raw macro input is not terminated",
       "This raw macro capture reaches the end of its input without the `#{name_to_string(delimiter)}` delimiter.",
       "close this raw macro input", "Add the `#{name_to_string(delimiter)}` delimiter after the raw input"}

  defp raw_content(:invalid_raw_delimiter, %{delimiter: delimiter}),
    do:
      {"Raw macro delimiter is invalid",
       "A raw macro delimiter must be text, but this capture uses `#{name_to_string(delimiter)}`.",
       "replace this raw delimiter", "Use a textual token or structural delimiter name"}

  defp raw_content(:invalid_raw_tokens, _details),
    do:
      {"Raw macro token stream is malformed", "Raw macro capture expected a list of lexer tokens.",
       "replace this raw token stream", "Pass the lexer tokens belonging to the raw macro input"}

  @doc false
  def reducer_failure(kind, details, opts),
    do: simple_macro_failure(:macro_reducer_validation, kind, reducer_content(kind, details), opts)

  defp reducer_content(:invalid_reducer_arms, _details),
    do:
      {"Reducer arms are malformed", "Reducer arms must be provided as a list with one arm for every constructor.",
       "rewrite this reducer arm list", "Provide a list of constructor arms"}

  defp reducer_content(:invalid_reducer_arm, _details),
    do:
      {"Reducer arm is malformed",
       "Every reducer arm needs a constructor, an optional list of text bindings, and a body expression.",
       "rewrite this reducer arm", "Provide `constructor`, `bindings`, and `body` for this arm"}

  defp reducer_content(:duplicate_reducer_constructor, _details),
    do:
      {"Reducer constructor is repeated",
       "Two reducer arms match the same constructor, so one arm can never be selected.",
       "remove or change this duplicate arm", "Keep exactly one arm for each constructor"}

  defp reducer_content(:unknown_reducer_constructor, %{constructors: constructors}) do
    rendered = Enum.map_join(constructors, ", ", &"`#{name_to_string(&1)}`")
    verb = if length(constructors) == 1, do: "does", else: "do"

    {"Reducer uses an unknown constructor",
     "The reducer refers to #{constructor_phrase(constructors, rendered)}, which #{verb} not belong to the reflected data type.",
     "replace this unknown constructor", "Use only constructors declared by the reduced data type"}
  end

  defp reducer_content(:incomplete_reducer, %{constructors: constructors}) do
    rendered = Enum.map_join(constructors, ", ", &"`#{name_to_string(&1)}`")

    {"Reducer does not cover every constructor",
     "The reducer has no arm for #{constructor_phrase(constructors, rendered)}.", "add the missing constructor arm",
     "Add one arm for every listed constructor"}
  end

  defp reducer_content(:reducer_arity, %{constructor: constructor, actual: actual, expected: expected}),
    do:
      {"Reducer arm has the wrong number of bindings",
       "The `#{name_to_string(constructor)}` arm binds #{actual} values, but its constructor carries #{expected}.",
       "make these bindings match the constructor", "Use exactly #{expected} bindings in this arm"}

  defp constructor_phrase([_one], rendered), do: "constructor #{rendered}"
  defp constructor_phrase(_many, rendered), do: "constructors #{rendered}"

  @doc false
  def syntax_integrity_failure(kind, path, opts) do
    {title, message, label_text, hint} = syntax_integrity_content(kind, path)

    Diagnostic.new(
      code: "E092",
      key: :macro_syntax_integrity,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, path: path}
    )
  end

  def syntax_integrity_content(:raw_syntax_in_expansion, path),
    do:
      {"Macro expansion contains raw syntax",
       "The generated expansion contains reflection-only raw syntax at #{syntax_path_phrase(path)}.",
       "return executable syntax here", "Build structured `Syntax`; keep `Raw` values inside reflected metadata"}

  def syntax_integrity_content(:quoted_syntax_in_expansion, path),
    do:
      {"Macro expansion contains quoted syntax",
       "The generated expansion still contains quoted syntax at #{syntax_path_phrase(path)}.",
       "unquote this generated syntax", "Splice or otherwise unquote the value before returning the expansion"}

  def syntax_integrity_content(:malformed_expansion_syntax, path),
    do:
      {"Macro expansion syntax is malformed",
       "The generated expansion does not contain a valid `Node`, `Leaf`, or accepted failure value at #{syntax_path_phrase(path)}.",
       "rebuild this generated syntax", "Return a well-formed structured `Syntax` value"}

  def syntax_integrity_content(:malformed_expansion_attribute, path),
    do:
      {"Macro expansion attribute is malformed",
       "A generated syntax attribute is not an atom-keyed literal pair at #{syntax_path_phrase(path)}.",
       "rebuild this syntax attribute", "Use an atom key and a valid syntax literal value"}

  def syntax_integrity_content(:malformed_expansion_map, path),
    do:
      {"Macro expansion map literal is malformed",
       "A generated syntax-map entry is not a key-value pair at #{syntax_path_phrase(path)}.",
       "rebuild this syntax map", "Provide valid syntax-literal key-value pairs"}

  def syntax_integrity_content(:malformed_expansion_literal, path),
    do:
      {"Macro expansion literal is malformed",
       "A generated syntax literal has the wrong shape or host value at #{syntax_path_phrase(path)}.",
       "replace this syntax literal",
       "Use a valid integer, float, string, boolean, atom, list, map, syntax, or opaque literal"}

  def syntax_integrity_content(:malformed_reflected_syntax, path),
    do:
      {"Reflected syntax value is malformed",
       "Syntax stored inside generated metadata has an invalid node shape at #{syntax_path_phrase(path)}.",
       "rebuild this reflected syntax", "Store a well-formed reflected `Syntax` value"}

  def syntax_integrity_content(:malformed_reflected_attribute, path),
    do:
      {"Reflected syntax attribute is malformed",
       "An attribute inside reflected syntax is not an atom-keyed literal pair at #{syntax_path_phrase(path)}.",
       "rebuild this reflected attribute", "Use an atom key and a valid reflected literal value"}

  def syntax_integrity_content(:malformed_reflected_map, path),
    do:
      {"Reflected syntax map is malformed",
       "A map stored inside reflected syntax contains an entry that is not a key-value pair at #{syntax_path_phrase(path)}.",
       "rebuild this reflected map", "Provide valid reflected-literal key-value pairs"}

  def syntax_integrity_content(:malformed_reflected_literal, path),
    do:
      {"Reflected syntax literal is malformed",
       "A literal stored inside reflected syntax has the wrong shape or host value at #{syntax_path_phrase(path)}.",
       "replace this reflected literal", "Use a valid reflected syntax literal"}

  def syntax_integrity_content(kind, path),
    do:
      {"Macro syntax value is invalid",
       "Generated syntax failed the `#{name_to_string(kind)}` integrity check at #{syntax_path_phrase(path)}.",
       "rebuild this generated syntax", "Return a well-formed structured `Syntax` value"}

  def syntax_path_phrase([]), do: "the expansion root"
  def syntax_path_phrase(path), do: "`#{format_syntax_path(path)}`"

  defp format_syntax_path(path) do
    path
    |> Enum.reverse()
    |> Enum.map_join(".", fn
      {:child, index} -> "child[#{index}]"
      {:attribute, key, index} -> "attribute #{key}[#{index}]"
      {:syntax_literal} -> "syntax literal"
      {:map_key} -> "map key"
      {:map_value} -> "map value"
      {:list_item} -> "list item"
      {:failure_arguments} -> "failure arguments"
      {:raw_literal} -> "raw literal"
      {:quoted_syntax} -> "quoted syntax"
      other -> inspect(other)
    end)
  end

  @doc false
  def module_failure(kind, details, opts) do
    {title, message, label_text, hint} = module_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_module_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def diagnostic_schema_failure(kind, opts) do
    {title, message, label_text, hint} = diagnostic_schema_content(kind)

    Diagnostic.new(
      code: "E092",
      key: :macro_diagnostic_schema,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind}
    )
  end

  @doc false
  def fuzz_input_failure(kind, details, opts) do
    {title, message, label_text, hint} = fuzz_input_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_fuzz_input,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: fuzz_payload(kind, details)
    )
  end

  defp fuzz_input_content(:invalid_macro_fuzz_rule, _details),
    do:
      {"Macro proof rule is malformed",
       "Proof-input assembly needs a parsed macro rule with a textual keyword and segment list.",
       "rewrite this macro rule", "Provide a parsed syntax or computed rule"}

  defp fuzz_input_content(:invalid_macro_fuzz_bindings, _details),
    do:
      {"Macro proof bindings are malformed",
       "Generated hole bindings must map each textual hole name to its sampled value.",
       "rewrite these generated bindings", "Provide a map from hole names to generated values"}

  defp fuzz_input_content(:invalid_macro_segment, _details),
    do:
      {"Macro rule contains an unsupported segment",
       "Proof-input assembly encountered a rule segment that is not a literal, hole, repetition, optional group, raw hole, or declaration body.",
       "replace this macro segment", "Use one of the supported macro rule segment forms"}

  defp fuzz_input_content(:missing_hole_filler, %{detail: name}),
    do:
      {"Generated macro input is missing a hole",
       "The proof input has no generated value for the `#{name_to_string(name)}` hole required by this rule.",
       "supply this generated hole", "Add a generated value for `#{name_to_string(name)}`"}

  defp fuzz_input_content(:invalid_repeated_hole_filler, %{detail: name}),
    do:
      {"Repeated macro hole needs a list",
       "The `#{name_to_string(name)}` hole is repeated by the rule, but its generated filler is not a list of values.",
       "replace this repeated-hole filler", "Provide a list of generated values for `#{name_to_string(name)}`"}

  defp fuzz_input_content(:unsupported_surface_filler, _details),
    do:
      {"Generated hole has no surface spelling",
       "The proof generator produced a Core value that cannot be written as authored Cure macro input.",
       "use a surface-encodable generator",
       "Generate a literal, nullary constructor, raw text, natural, boolean, or supported type value"}

  defp fuzz_input_content(:not_a_nat, _details),
    do:
      {"Generated natural number is malformed",
       "A sampled natural must be built only from `Z` and unary `S` constructors.",
       "replace this natural-number sample", "Generate `Z` or `S(previous_nat)`"}

  defp fuzz_payload(kind, %{detail: detail})
       when kind in [:missing_hole_filler, :invalid_repeated_hole_filler],
       do: %{kind: kind, hole: name_to_string(detail)}

  defp fuzz_payload(kind, _details), do: %{kind: kind}

  defp diagnostic_schema_content(:invalid_macro_diagnostics),
    do:
      {"Macro rejection list is malformed",
       "A rejected macro result must contain one author diagnostic or a proper list of author diagnostics.",
       "rebuild this macro rejection", "Return `Rejected([Failure(name, arguments), ...])`"}

  defp diagnostic_schema_content(:invalid_macro_diagnostic),
    do:
      {"Macro author diagnostic is malformed",
       "A macro author diagnostic must be a reflected `Failure` value with an atom name and syntax arguments.",
       "rebuild this author diagnostic", "Return `Failure(name, arguments)` inside `Rejected`"}

  @doc false
  def validation_failure(kind, details, opts),
    do: validation_failure(kind, details, opts, %{})

  @doc false
  def validation_failure(kind, details, opts, context) do
    span = Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :macro_validation_failed,
      severity: :error,
      title: validation_title(kind),
      body: Doc.paragraph(validation_message(kind, details)),
      primary: label(span, :primary, validation_primary_label(kind)),
      secondary: validation_secondary_labels(kind, context, span),
      suggestions: validation_suggestions(kind),
      payload: %{kind: kind, details: details, macro: Map.get(context, :macro)}
    )
  end

  defp validation_title(:missing_diagnosis), do: "Macro explanations are incomplete"
  defp validation_title(:rule_unpinned), do: "Macro rule needs a worked example"
  defp validation_title(:example_mismatch), do: "Macro example has the wrong expansion"
  defp validation_title(:example_type_mismatch), do: "Macro example has the wrong type"
  defp validation_title(:computed_example_error), do: "Computed macro example failed"
  defp validation_title(:reserved_syntax_field), do: "Macro hole uses a reserved name"
  defp validation_title(:unsupported_hole_type), do: "Macro hole cannot be generated for proofs"
  defp validation_title(_kind), do: "Macro validation failed"

  defp validation_primary_label(:missing_diagnosis), do: "add clauses for the unexplained failure points"
  defp validation_primary_label(:rule_unpinned), do: "add a worked example beneath this rule"
  defp validation_primary_label(:example_mismatch), do: "this pin does not match the actual expansion"
  defp validation_primary_label(:example_type_mismatch), do: "this pinned type does not accept the expansion"
  defp validation_primary_label(:computed_example_error), do: "this computed example could not be checked"
  defp validation_primary_label(:reserved_syntax_field), do: "this hole name is reserved for expansion context"
  defp validation_primary_label(:unsupported_hole_type), do: "the proof generator cannot construct this category"
  defp validation_primary_label(_kind), do: "this macro declaration is incomplete or inconsistent"

  defp validation_secondary_labels(:missing_diagnosis, context, primary_span),
    do:
      context
      |> Map.get(:rule_spans, [])
      |> Enum.map(&label(&1, :secondary, "this rule declares an unexplained failure point"))
      |> Enum.reject(&(&1.span == primary_span))

  defp validation_secondary_labels(:rule_unpinned, context, primary_span),
    do:
      context
      |> Map.get(:rule_spans, [])
      |> Enum.drop(1)
      |> Enum.map(&label(&1, :secondary, "this rule also needs a worked example"))
      |> Enum.reject(&(&1.span == primary_span))

  defp validation_secondary_labels(kind, context, primary_span)
       when kind in [:example_mismatch, :example_type_mismatch, :computed_example_error],
       do:
         context
         |> Map.get(:rule_spans, [])
         |> Enum.map(&label(&1, :secondary, "this rule owns the failing example"))
         |> Enum.reject(&(&1.span == primary_span))

  defp validation_secondary_labels(:reserved_syntax_field, context, primary_span),
    do:
      context
      |> Map.get(:hole_spans, [])
      |> Enum.map(&label(&1, :secondary, "this hole also uses the reserved context name"))
      |> Enum.reject(&(&1.span == primary_span))

  defp validation_secondary_labels(:unsupported_hole_type, context, primary_span),
    do:
      context
      |> Map.get(:hole_spans, [])
      |> Enum.map(&label(&1, :secondary, "this hole uses the same unsupported category"))
      |> Enum.reject(&(&1.span == primary_span))

  defp validation_secondary_labels(_kind, _context, _primary_span), do: []

  defp validation_suggestions(:missing_diagnosis),
    do: [%Suggestion{message: "Add one `explain` clause for each listed failure point", applicability: :manual}]

  defp validation_suggestions(:rule_unpinned),
    do: [
      %Suggestion{message: "Add `example use_site expands expected` beneath each listed rule", applicability: :manual}
    ]

  defp validation_suggestions(:example_mismatch),
    do: [%Suggestion{message: "Update the pinned expansion or fix the macro rule", applicability: :manual}]

  defp validation_suggestions(:example_type_mismatch),
    do: [%Suggestion{message: "Use the expansion's actual type or fix the macro rule", applicability: :manual}]

  defp validation_suggestions(:computed_example_error),
    do: [%Suggestion{message: "Fix the computed expander or its worked example", applicability: :manual}]

  defp validation_suggestions(:reserved_syntax_field),
    do: [%Suggestion{message: "Rename this hole; `context` is supplied automatically", applicability: :manual}]

  defp validation_suggestions(:unsupported_hole_type),
    do: [
      %Suggestion{
        message: "Use a generatable category, or mark the rule `contextual` when proof needs its call site",
        applicability: :manual
      }
    ]

  defp validation_suggestions(_kind), do: []

  defp validation_message(:missing_diagnosis, points),
    do: "The macro does not explain every declared failure point: #{failure_points(points)}."

  defp validation_message(:rule_unpinned, keywords),
    do: "These macro rules have no worked example: #{Enum.join(Enum.map(keywords, &name_to_string/1), ", ")}."

  defp validation_message(:example_mismatch, mismatches),
    do: "Macro example(s) do not match their actual expansions: #{example_names(mismatches)}."

  defp validation_message(:example_type_mismatch, failures),
    do: "Macro example(s) have the wrong type: #{example_names(failures)}."

  defp validation_message(:computed_example_error, failures),
    do: "A computed macro example failed while being checked: #{example_names(failures)}."

  defp validation_message(:reserved_syntax_field, %{first: field, second: keywords}),
    do:
      "The hole `#{field}` in #{rule_names(keywords)} conflicts with the reflected expansion context supplied to computed rules."

  defp validation_message(:unsupported_hole_type, %{detail: category}),
    do:
      "The generative expansion proof has no safe value generator for the `#{name_to_string(category)}` hole category."

  defp validation_message(kind, _details), do: "Macro validation failed for #{name_to_string(kind)}."

  defp failure_points(points) do
    Enum.map_join(points, ", ", fn
      {:failure, name} -> "author failure `#{name}`"
      {:hole_kind, kind} -> "#{kind} hole"
      {:keyword, keyword} -> "keyword `#{keyword}`"
      _point -> "an additional declared failure point"
    end)
  end

  defp example_names(values) when is_list(values) do
    names =
      values
      |> Enum.map(fn
        %{keyword: keyword} -> name_to_string(keyword)
        %{"keyword" => keyword} -> name_to_string(keyword)
        _ -> nil
      end)
      |> Enum.reject(&is_nil/1)

    case names do
      [] -> "the affected examples"
      names -> Enum.join(names, ", ")
    end
  end

  defp rule_names([keyword]), do: "the `#{name_to_string(keyword)}` rule"

  defp rule_names(keywords) when is_list(keywords),
    do: "the #{Enum.map_join(keywords, ", ", &"`#{name_to_string(&1)}`")} rules"

  defp module_content(:module_rule_not_fully_consumed, _details),
    do:
      {"Module macro leaves input unconsumed",
       "This module macro expands one declaration but leaves additional authored tokens outside the matched rule.",
       "match the complete module-macro input", "Extend the rule to consume the remaining tokens or remove them"}

  defp module_content(:not_a_module_rule, _details),
    do:
      {"Macro rule cannot expand a module",
       "This rule is being executed as a module macro, but it was not declared with module scope.",
       "use a module-scoped macro rule", "Declare this syntax as a module rule before executing it here"}

  defp module_content(:invalid_module_rule_set, _details),
    do:
      {"Module macro rule set is malformed",
       "Module expansion needs a list containing valid syntax rules from the same macro.",
       "rewrite this module-macro rule set", "Provide the parsed syntax rules that own this module rule"}

  defp module_content(:invalid_module_rule_bindings, _details),
    do:
      {"Module macro bindings are malformed",
       "Module-rule bindings must map each declared hole name to its captured syntax value.",
       "rewrite these module-macro bindings", "Provide a map from hole names to captured syntax"}

  defp module_content(:invalid_macro_extension_rules, _details),
    do:
      {"Macro extension lists are malformed",
       "Open-category composition needs separate lists of base rules and extension rules.",
       "rewrite these macro extension lists", "Provide one list of base rules and one list of extension rules"}

  defp module_content(:invalid_macro_extension_rule, _details),
    do:
      {"Macro extension rule is malformed", "Every base or extension rule must be a parsed macro-rule map.",
       "rewrite this macro extension rule", "Provide valid parsed macro rules in both lists"}

  defp module_content(:closed_category_extension, %{categories: categories}),
    do:
      {"Closed macro category cannot be extended",
       "The extension adds syntax to #{category_phrase(categories)}, but only categories declared open accept external rules.",
       "remove this closed-category extension", "Declare the category open or move the syntax into its owning macro"}

  defp module_content(:ambiguous_macro_extension, %{keywords: keywords}),
    do:
      {"Macro extension repeats a keyword",
       "The composed macro would contain multiple rules beginning with #{keyword_phrase(keywords)}, making dispatch ambiguous.",
       "rename this extension keyword", "Give each composed rule a distinct leading keyword"}

  defp category_phrase([one]), do: "closed category `#{name_to_string(one)}`"

  defp category_phrase(categories),
    do: "closed categories #{Enum.map_join(categories, ", ", &"`#{name_to_string(&1)}`")}"

  defp keyword_phrase([one]), do: "keyword `#{name_to_string(one)}`"
  defp keyword_phrase(keywords), do: "keywords #{Enum.map_join(keywords, ", ", &"`#{name_to_string(&1)}`")}"

  @doc false
  def family_failure(details, opts) when is_map(details) do
    reason = Map.get(details, :reason)
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      details
      |> Map.get(:related_spans, [])
      |> Enum.map(&label(&1, :secondary, family_related_label(reason)))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E092",
      key: :invalid_macro_family,
      severity: :error,
      title: family_title(reason),
      body: Doc.paragraph(family_body(reason)),
      primary: label(span, :primary, family_primary_label(reason)),
      secondary: secondary,
      suggestions: [%Suggestion{message: family_hint(reason), applicability: :manual}],
      payload: details
    )
  end

  @doc false
  def family_failure(reason, opts),
    do: simple_macro_failure(:invalid_macro_family, reason, family_content(reason), opts)

  defp family_content(reason),
    do: {family_title(reason), family_body(reason), family_primary_label(reason), family_hint(reason)}

  defp family_title({:unknown_syntax_family, _name}), do: "Included syntax family is unknown"
  defp family_title({:syntax_family_cycle, _names}), do: "Syntax families form a cycle"
  defp family_title({:duplicate_syntax_family, _names}), do: "Syntax family name is repeated"
  defp family_title({:duplicate_syntax_family_field, _pairs}), do: "Syntax-family field is duplicated"
  defp family_title(:invalid_macro_rules), do: "Macro rule list is malformed"
  defp family_title(:expander_without_accepts), do: "Macro expander has no accepted family"
  defp family_title(:accepts_without_syntax_family), do: "Accepted syntax family is not declared"
  defp family_title(:accepts_without_expander), do: "Accepted syntax family has no expander"
  defp family_title(:multiple_accepts_declarations), do: "Macro accepts more than one family"
  defp family_title(:multiple_expands_declarations), do: "Macro declares more than one expander"
  defp family_title(_reason), do: "Syntax-family declaration is invalid"

  defp family_body({:unknown_syntax_family, name}),
    do: "`#{name}` is included here, but this macro does not declare a syntax family with that name."

  defp family_body({:syntax_family_cycle, names}),
    do: "These syntax families include one another in a cycle: #{Enum.map_join(names, " → ", &to_string/1)}."

  defp family_body({:duplicate_syntax_family, names}),
    do:
      "The same syntax family name is declared more than once: #{Enum.map_join(names, ", ", &"`#{name_to_string(&1)}`")}."

  defp family_body({:duplicate_syntax_family_field, pairs}) do
    fields = Enum.map_join(pairs, ", ", fn {family, field} -> "`#{family}.#{field}`" end)
    "The same field is declared more than once: #{fields}."
  end

  defp family_body(:invalid_macro_rules), do: "Structured macro validation expected a list of well-formed macro rules."

  defp family_body(:expander_without_accepts),
    do: "This macro declares how to expand a syntax family but never declares which family it accepts."

  defp family_body(:accepts_without_syntax_family),
    do: "This macro accepts a syntax family but does not declare any syntax-family shape for that input."

  defp family_body(:accepts_without_expander),
    do: "This macro accepts structured syntax but does not declare the function that expands it."

  defp family_body(:multiple_accepts_declarations),
    do: "A structured macro can have only one `accepts` declaration, but this macro has more than one."

  defp family_body(:multiple_expands_declarations),
    do: "A structured macro can have only one `expands with` declaration, but this macro has more than one."

  defp family_body(reason), do: "The syntax-family declarations are inconsistent: #{name_to_string(reason)}."

  defp family_primary_label({:unknown_syntax_family, _name}), do: "this included family is not declared"
  defp family_primary_label({:syntax_family_cycle, _names}), do: "the inclusion cycle starts here"
  defp family_primary_label({:duplicate_syntax_family, _names}), do: "this family name is declared again"
  defp family_primary_label({:duplicate_syntax_family_field, _pairs}), do: "this field is declared again"
  defp family_primary_label(:invalid_macro_rules), do: "rewrite these macro rules"
  defp family_primary_label(:expander_without_accepts), do: "this expander has no matching `accepts` declaration"
  defp family_primary_label(:accepts_without_syntax_family), do: "this accepted family has no declaration"
  defp family_primary_label(:accepts_without_expander), do: "this accepted family has no expander"
  defp family_primary_label(:multiple_accepts_declarations), do: "remove this additional `accepts` declaration"
  defp family_primary_label(:multiple_expands_declarations), do: "remove this additional expander declaration"
  defp family_primary_label(_reason), do: "this macro family is inconsistent"

  defp family_related_label({:syntax_family_cycle, _names}), do: "this family also participates in the cycle"
  defp family_related_label({:duplicate_syntax_family, _names}), do: "the family name was first declared here"
  defp family_related_label({:duplicate_syntax_family_field, _pairs}), do: "the field was already declared here"
  defp family_related_label(:multiple_accepts_declarations), do: "another `accepts` declaration is here"
  defp family_related_label(:multiple_expands_declarations), do: "another expander declaration is here"
  defp family_related_label(_reason), do: "related family declaration"

  defp family_hint({:unknown_syntax_family, name}),
    do: "Declare `syntax family #{name}` or change `includes` to a declared family"

  defp family_hint({:syntax_family_cycle, _names}), do: "Remove one `includes` edge so the family graph is acyclic"

  defp family_hint({:duplicate_syntax_family, _names}),
    do: "Rename one family or combine their fields into a single declaration"

  defp family_hint({:duplicate_syntax_family_field, _pairs}), do: "Keep one declaration of the field"
  defp family_hint(:invalid_macro_rules), do: "Provide a list of parsed macro rules"
  defp family_hint(:expander_without_accepts), do: "Add `accepts FamilyName` for the expander's input"
  defp family_hint(:accepts_without_syntax_family), do: "Declare the accepted family with `syntax family`"
  defp family_hint(:accepts_without_expander), do: "Add `expands with function_name`"
  defp family_hint(:multiple_accepts_declarations), do: "Keep exactly one `accepts` declaration"
  defp family_hint(:multiple_expands_declarations), do: "Keep exactly one `expands with` declaration"
  defp family_hint(_reason), do: "Make the syntax-family declarations consistent"

  @doc false
  def syntax_decode_failure(kind, details, opts),
    do: simple_macro_failure(:macro_syntax_decode, kind, syntax_decode_content(kind, details), opts)

  defp syntax_decode_content(:invalid_syntax_node, _details),
    do:
      {"Generated syntax node is malformed",
       "A reflected `Node` must contain an atom tag, an attribute list, and a list of syntax children.",
       "rebuild this syntax node", "Construct `Node(tag, attributes, children)` with valid values"}

  defp syntax_decode_content(:invalid_syntax_leaf, %{tag: tag}),
    do:
      {"Generated syntax leaf is malformed",
       "The `#{name_to_string(tag)}` reflected `Leaf` does not contain a valid attribute list and syntax literal.",
       "rebuild this syntax leaf", "Construct `Leaf(tag, attributes, literal)` with valid values"}

  defp syntax_decode_content(:invalid_syntax_failure, %{name: name}),
    do:
      {"Macro failure value is malformed",
       "The `#{name_to_string(name)}` failure does not contain a valid list of reflected syntax arguments.",
       "rebuild this macro failure", "Construct `Failure(name, arguments)` with valid syntax arguments"}

  defp syntax_decode_content(:unsupported_syntax_core, _details),
    do:
      {"Macro returned a non-syntax value",
       "The computed macro returned a Core value that is not a `Std.Syntax` constructor.", "return a syntax value here",
       "Return `Node`, `Leaf`, `Raw`, `Quoted`, or `Failure` from the macro"}

  defp syntax_decode_content(:invalid_syntax_attrs, _details),
    do:
      {"Generated syntax attributes are malformed",
       "Syntax attributes must be a `Std.List` of atom-keyed `KV` entries.", "rebuild this attribute list",
       "Use `KV(atom_key, syntax_literal)` for every attribute"}

  defp syntax_decode_content(:invalid_syntax_attr, _details),
    do:
      {"Generated syntax attribute is malformed",
       "A syntax attribute must be an atom-keyed `KV` entry containing a valid syntax literal.",
       "rebuild this syntax attribute", "Use `KV(atom_key, syntax_literal)`"}

  defp syntax_decode_content(:invalid_syntax_list, _details),
    do:
      {"Generated syntax list is malformed",
       "A reflected syntax list must use the `Std.List` `Nil` and `Cons` constructors.", "rebuild this syntax list",
       "Construct a proper `Std.List` value"}

  defp syntax_decode_content(:invalid_syntax_string, _details),
    do:
      {"Generated syntax string is malformed",
       "A reflected syntax string must contain a proper list of bounded character literals.",
       "rebuild this syntax string", "Construct `SStr` from valid character values"}

  defp syntax_decode_content(:invalid_syntax_literal, _details),
    do:
      {"Generated syntax literal is malformed",
       "This value is not one of the supported `Std.Syntax` literal constructors.", "replace this syntax literal",
       "Use `SInt`, `SFloat`, `SStr`, `SBool`, `SAtom`, `SList`, `SSyntax`, `SMap`, or `SOpaque`"}

  defp syntax_decode_content(:invalid_syntax_pair, _details),
    do:
      {"Generated syntax-map pair is malformed",
       "Every entry in an `SMap` must be an `SPair` containing two valid syntax literals.",
       "rebuild this syntax-map pair", "Use `SPair(key, value)` inside `SMap`"}

  defp packet_content(:invalid_packet_name, %{detail: name}) do
    {"Packet name is invalid",
     "A packet name must be an atom or string, but this declaration uses `#{name_to_string(name)}`.",
     "replace this packet name", "Use a stable packet name such as `Frame`"}
  end

  defp packet_content(:invalid_packet_endian, %{detail: endian}) do
    {"Packet byte order is invalid",
     "`#{name_to_string(endian)}` is not a packet byte order. Multi-byte scalar fields use big-endian (`be`) or little-endian (`le`) order.",
     "choose a supported byte order", "Use `endian: :be` or `endian: :le`"}
  end

  defp packet_content(:unknown_packet_scalar, %{detail: scalar}) do
    {"Packet scalar type is unknown", "`#{name_to_string(scalar)}` is not a fixed-width packet scalar.",
     "replace this scalar type", "Use one of `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, or `byte`"}
  end

  defp packet_content(:missing_packet_endian, %{detail: field}) do
    {"Packet field needs a byte order",
     "The multi-byte `#{name_to_string(field)}` field has no byte order, so its encoded bytes would be ambiguous.",
     "declare this field's byte order", "Set `endian: :be` or `endian: :le` on the packet or this field"}
  end

  defp packet_content(:forward_packet_length, %{field: field, dependency: length_field}) do
    {"Packet length field comes too late",
     "The `#{name_to_string(field)}` field takes its length from `#{name_to_string(length_field)}`, but that length field has not been decoded yet.",
     "move the length field before this payload",
     "Declare `#{name_to_string(length_field)}` before `#{name_to_string(field)}`"}
  end

  defp packet_content(:invalid_packet_crc_fields, %{field: field, dependency: missing}) do
    names = missing |> List.wrap() |> Enum.map_join(", ", &"`#{name_to_string(&1)}`")

    {"Packet checksum references unavailable fields",
     "The `#{name_to_string(field)}` checksum includes #{names}, but those fields have not been decoded before the checksum.",
     "fix this checksum coverage",
     "List only earlier packet fields in `over`, or move the referenced fields before `#{name_to_string(field)}`"}
  end

  defp packet_content(:duplicate_packet_field, _details) do
    {"Packet field name is repeated",
     "Two packet fields have the same name, so generated accessors and layout entries would collide.",
     "rename or remove this repeated field", "Give every packet field a unique name"}
  end

  defp packet_content(:invalid_packet_field_name, _details) do
    {"Packet field has no name", "Every packet field needs a name so later length and checksum fields can refer to it.",
     "add a name to this field", "Add a unique `name` to every packet field"}
  end

  defp packet_content(:invalid_packet_field, _details) do
    {"Packet field is malformed",
     "A packet field must declare a name and one supported shape: constant, scalar, bytes, or checksum.",
     "rewrite this packet field", "Use a `const`, `scalar`, `bytes`, or `crc` field with all required properties"}
  end

  defp macro_expansion_failure(kind, message, frames, opts) do
    frame_maps = Enum.filter(frames, &is_map/1)

    provenance =
      Enum.map(frame_maps, fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword, "macro"),
          invocation: Map.get(frame, :invocation),
          definition: Map.get(frame, :definition),
          parent: Map.get(frame, :parent)
        }
      end)

    invocation_spans =
      frame_maps
      |> Enum.map(&Map.get(&1, :invocation))
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    primary_span =
      List.last(invocation_spans) || Keyword.get(opts, :span)

    secondary =
      invocation_spans
      |> Enum.reject(&(&1 == primary_span))
      |> Enum.map(
        &label(
          &1,
          :secondary,
          "this earlier invocation is in the expansion chain"
        )
      )

    suggestion =
      case kind do
        :cycle ->
          "Make recursive macro expansion consume input or terminate before invoking itself again"

        {:budget, _limit} ->
          "Reduce the generated expansion depth or split this macro into smaller steps"
      end

    chain =
      frame_maps
      |> Enum.map(&Map.get(&1, :keyword))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title:
        if(kind == :cycle,
          do: "Macro expansion cycle",
          else: "Macro expansion limit exceeded"
        ),
      body: Doc.paragraph(message),
      primary:
        label(
          primary_span,
          :primary,
          if(kind == :cycle,
            do: "this invocation closes the expansion cycle",
            else: "the expansion limit is reached here"
          )
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: suggestion, applicability: :manual}
      ],
      provenance: provenance ++ Keyword.get(opts, :provenance, []),
      payload: %{kind: kind, frames: frames, chain: chain}
    )
  end

  defp syntax_family_field_suggestions(
         %{field: field, valid_fields: fields},
         %Span{} = span
       )
       when is_list(fields),
       do:
         ranked_repair(
           field,
           fields,
           span,
           fn candidate -> "Replace it with `#{candidate}`" end,
           fn candidates ->
             "Use one of: #{Enum.map_join(candidates, ", ", fn field -> "`#{field}`" end)}"
           end
         )

  defp syntax_family_field_suggestions(_details, _span), do: []

  defp macro_capture_suggestions(
         %{capture: capture, available_captures: captures},
         %Span{} = span
       )
       when is_list(captures),
       do:
         ranked_repair(
           capture,
           captures,
           span,
           fn candidate ->
             "Replace it with the declared capture `#{candidate}`"
           end,
           fn candidates ->
             "Refer to one of this rule's captures: #{Enum.map_join(candidates, ", ", fn capture -> "`#{capture}`" end)}"
           end
         )

  defp macro_capture_suggestions(_details, _span), do: []

  defp computed_macro_content(keyword, :no_compatible_macro_input) do
    {
      "Computed macro expander does not accept its input",
      "The `#{keyword}` macro's expander cannot be applied to any supported reflection of this invocation. Its parameter type must accept the macro's generated syntax record, its direct captured fields, or generic `Syntax`.",
      "this invocation cannot be passed to its expander",
      "The invocation is authored source; change the expander's input type or the macro rule that constructs it."
    }
  end

  defp computed_macro_content(keyword, :normalization_fuel_exhausted) do
    {
      "Computed macro expansion did not terminate",
      "The `#{keyword}` macro's expander exceeded the compiler's bounded evaluation budget before producing syntax. This usually means the expander recurses without reaching a smaller input or performs unexpectedly large compile-time work.",
      "this invocation exhausted the expansion budget",
      "The compiler stopped evaluation safely; no partial generated syntax was accepted."
    }
  end

  defp computed_macro_content(keyword, reason) do
    {
      "Computed macro expansion failed",
      "The `#{keyword}` computed macro could not produce valid Cure syntax: #{computed_macro_reason(reason)}",
      "this macro invocation generated the failing syntax",
      "Edit the authored macro invocation or its rule; generated syntax is not the user-facing source."
    }
  end

  defp computed_macro_payload(:no_compatible_macro_input), do: %{kind: :incompatible_input}
  defp computed_macro_payload(:normalization_fuel_exhausted), do: %{kind: :evaluation_budget_exhausted}

  defp computed_macro_payload({:author_failure, name, _args}),
    do: %{kind: :author_failure, name: name}

  defp computed_macro_payload({:author_diagnostics, diagnostics}),
    do: %{kind: :author_diagnostics, names: author_diagnostic_names(diagnostics)}

  defp computed_macro_payload({:invalid_generated_syntax, {kind, path}}),
    do: %{kind: :invalid_generated_syntax, syntax_problem: kind, path: path}

  defp computed_macro_payload(reason), do: %{kind: :expansion_rejected, category: computed_macro_category(reason)}

  defp computed_macro_category(reason) when is_atom(reason), do: reason
  defp computed_macro_category(reason) when is_tuple(reason) and tuple_size(reason) > 0, do: elem(reason, 0)
  defp computed_macro_category(_reason), do: :unknown

  defp computed_macro_reason({:invalid_generated_syntax, {:raw_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: raw syntax is only valid for reflection, not generated Cure code at #{syntax_path_phrase(path)}"

  defp computed_macro_reason({:invalid_generated_syntax, {:quoted_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: quoted syntax must be unquoted before it is emitted as Cure code at #{syntax_path_phrase(path)}"

  defp computed_macro_reason({:invalid_generated_syntax, {kind, path}}) do
    {_title, message, _label, _hint} = syntax_integrity_content(kind, path)
    "invalid macro expansion: #{String.downcase(message)}"
  end

  defp computed_macro_reason({:author_diagnostics, diagnostics}) when is_list(diagnostics),
    do: "macro rejected expansion: #{author_diagnostic_summary(diagnostics)}"

  defp computed_macro_reason({:author_failure, name, args}) when is_list(args),
    do: "macro rejected expansion: the macro reported `#{name}`"

  defp computed_macro_reason(_reason), do: "the generated expansion was rejected by the compiler"

  defp computed_macro_suggestions({:invalid_generated_syntax, {:raw_syntax_in_expansion, _path}}),
    do: [%Suggestion{message: "Return structured `Syntax`; use raw syntax only for reflection", applicability: :manual}]

  defp computed_macro_suggestions({:invalid_generated_syntax, {:quoted_syntax_in_expansion, _path}}),
    do: [
      %Suggestion{message: "Unquote the generated syntax before returning it from the expander", applicability: :manual}
    ]

  defp computed_macro_suggestions({:invalid_generated_syntax, {kind, path}}) do
    {_title, _message, _label, hint} = syntax_integrity_content(kind, path)
    [%Suggestion{message: hint, applicability: :manual}]
  end

  defp computed_macro_suggestions({:author_diagnostics, diagnostics}),
    do: [
      %Suggestion{message: "Address #{author_diagnostic_hint(diagnostics)} at this invocation", applicability: :manual}
    ]

  defp computed_macro_suggestions({:author_failure, name, _args}),
    do: [%Suggestion{message: "Fix the `#{name}` condition reported by this macro", applicability: :manual}]

  defp computed_macro_suggestions(:no_compatible_macro_input),
    do: [
      %Suggestion{
        message: "Make the expander accept its generated syntax record, captured fields, or generic `Syntax`",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions(:normalization_fuel_exhausted),
    do: [
      %Suggestion{
        message:
          "Make recursive expansion calls structurally smaller, or move large work out of compile-time evaluation",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions(_reason),
    do: [%Suggestion{message: "Fix this invocation or the computed macro's expander", applicability: :manual}]

  defp author_diagnostic_summary(diagnostics) do
    case author_diagnostic_names(diagnostics) do
      [] -> "it reported #{length(diagnostics)} authored diagnostic(s)"
      [name] -> "it reported `#{name}`"
      names -> "it reported #{Enum.map_join(names, ", ", &"`#{&1}`")}"
    end
  end

  defp author_diagnostic_hint(diagnostics) do
    case author_diagnostic_names(diagnostics) do
      [] -> "the macro's authored diagnostics"
      [name] -> "the macro's `#{name}` diagnostic"
      names -> "the macro diagnostics #{Enum.map_join(names, ", ", &"`#{&1}`")}"
    end
  end

  defp author_diagnostic_names(diagnostics) do
    diagnostics
    |> Enum.flat_map(fn
      {:macro_failure, name, _args} -> [name_to_string(name)]
      _diagnostic -> []
    end)
    |> Enum.uniq()
  end

  defp diagnostic_fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

  defp maybe_put_meta_location(payload, meta) do
    case {Keyword.get(meta, :line), Keyword.get(meta, :col, Keyword.get(meta, :column))} do
      {line, column} when is_integer(line) and is_integer(column) -> Map.merge(payload, %{line: line, column: column})
      {line, _column} when is_integer(line) -> Map.put(payload, :line, line)
      _ -> payload
    end
  end

  defp macro_title(macro), do: macro |> name_to_string() |> String.capitalize()

  defp macro_failure_message(macro, module, %Diagnostic{} = cause) do
    "The `#{macro}` declaration could not generate `#{module}`. #{Diagnostic.message(cause)}"
  end

  defp provenance_frames(details, opts) do
    source = Map.get(details, :source_provenance) || %{}
    chain = Map.get(details, :expansion_provenance, [])
    invocation = Keyword.get(opts, :span)

    frames =
      Enum.map(chain, fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword) || "macro",
          invocation: invocation
        }
      end)

    source_frame =
      case Map.get(source, :macro) do
        nil -> []
        macro -> [%ProvenanceFrame{kind: :macro_expansion, name: macro, invocation: invocation}]
      end

    (frames ++ source_frame)
    |> Enum.uniq_by(& &1.name)
  end

  defp ranked_repair(spelling, candidates, span, unique_message, fallback_message) do
    spelling = to_string(spelling)

    ranked =
      candidates
      |> Enum.map(&{to_string(&1), Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} ->
        {distance, String.downcase(candidate), candidate}
      end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [replacement(candidate, span, unique_message)]

      [{candidate, distance}] when distance <= 2 ->
        [replacement(candidate, span, unique_message)]

      _ ->
        [
          %Suggestion{
            message: fallback_message.(candidates),
            applicability: :manual
          }
        ]
    end
  end

  defp replacement(candidate, span, message) do
    %Suggestion{
      message: message.(candidate),
      applicability: :machine_applicable,
      edits: [%TextEdit{span: span, replacement: candidate}]
    }
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp label(%Span{} = span, style, message),
    do: %Label{span: span, style: style, message: message}

  defp label(_span, _style, _message), do: nil

  defp article_for_kind(<<c, _::binary>>) when c in ~c"AEIOUaeiou", do: "an"
  defp article_for_kind(_kind), do: "a"
end
