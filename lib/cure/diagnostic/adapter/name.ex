defmodule Cure.Diagnostic.Adapter.Name do
  @moduledoc """
  Converts unresolved-name failures and owns deterministic candidate repairs.

  Candidate maps retain semantic identity, owner, namespace, visibility,
  qualification/import requirements, arity, and origin in the machine payload.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter
  alias Cure.Diagnostic.Suggest

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:import_cycle, hops}, opts) when is_list(hops) do
    chain = Enum.map_join(hops, " -> ", fn hop -> "#{hop.module} (#{hop.path}:#{hop.line})" end)

    Diagnostic.new(
      code: "W086",
      key: :import_cycle,
      severity: :warning,
      title: "Import cycle",
      message: "This warning means the modules form a `use` cycle: #{chain}.",
      primary: primary(opts, "the cycle begins here"),
      notes: ["Cycle members compile together in deterministic order; qualify cross-module calls when order matters."],
      payload: %{hops: hops}
    )
  end

  def from_error({:named_argument_mismatch, variant, details}, opts) when is_map(details),
    do: named_argument_failure(variant, details, opts)

  def from_error({:unknown_global, name}, opts), do: unknown_name(:value, name, opts)
  def from_error({:unbound_var, name}, opts), do: unknown_name(:value, name, opts)
  def from_error({:unknown_family, name}, opts), do: unknown_name(:type, name, opts)
  def from_error({:unknown_ctor, name}, opts), do: unknown_name(:constructor, name, opts)
  def from_error({:foreign_ctor, name}, opts), do: unknown_name(:constructor, name, opts)
  def from_error({:unknown_constructor, name}, opts), do: unknown_name(:constructor, name, opts)

  def from_error({:unknown_global, name, details}, opts) when is_map(details),
    do: unknown_name(:value, name, Keyword.put(opts, :kernel_context, details))

  def from_error({:unknown_name, details}, opts) when is_map(details) do
    namespace = Map.get(details, :namespace, :value)
    name = Map.get(details, :name, "<unknown>")

    unknown_name(
      namespace,
      name,
      opts
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))
      |> Keyword.put(:owner, Map.get(details, :owner))
      |> Keyword.put(:checking, Map.get(details, :checking))
      |> Keyword.put(:arity, Map.get(details, :arity))
      |> Keyword.put(:expected_namespace, Map.get(details, :expected_namespace))
      |> Keyword.put(:imported_from, Map.get(details, :imported_from))
      |> Keyword.put(:span, Map.get(details, :span))
      |> Keyword.put(:provenance, Map.get(details, :provenance, []))
    )
  end

  def from_error({:unknown_field, record, field}, opts) do
    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", Keyword.put(opts, :owner, record))
  end

  def from_error({:source_context, {:unknown_field, record, field}, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:owner, record)
      |> Keyword.put(:checking, Map.get(context, :checking))

    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", opts)
  end

  def from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
      when is_map(context) and is_list(available_fields),
      do: record_field_unknown(record, field, available_fields, context, opts)

  def from_error({:unknown_field, record, field, available_fields}, opts) when is_list(available_fields) do
    candidates =
      Enum.map(available_fields, fn candidate ->
        %{
          id: {:record_field, record, candidate},
          name: name_to_string(candidate),
          namespace: :member,
          owner: record,
          imported: true,
          origin: :record_shape
        }
      end)

    opts =
      opts
      |> Keyword.put(:owner, record)
      |> Keyword.put(:record, record)
      |> Keyword.put(:candidates, candidates)
      |> Keyword.put(:display_name, "#{name_to_string(record)}.#{name_to_string(field)}")

    unknown_name(:member, name_to_string(field), opts)
  end

  def from_error({:source_context, {:unknown_record, name, candidates}, context}, opts)
      when is_map(context) and is_list(candidates),
      do: unknown_record_failure(name, candidates, context, opts)

  def from_error({:source_context, {:unknown_record, name}, context}, opts) when is_map(context),
    do: unknown_record_failure(name, Map.get(context, :available_records, []), context, opts)

  def from_error({:source_context, {:record_field_mismatch, name}, context}, opts)
      when is_map(context) and not is_map(name),
      do: record_field_mismatch_failure(name, %{}, context, opts)

  def from_error({:source_context, {:record_field_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: record_field_mismatch_failure(Map.get(details, :record), details, context, opts)

  def from_error({:source_context, {kind, name}, context}, opts)
      when kind in [:unknown_ctor, :unknown_pattern_constructor, :unknown_family] and
             is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:candidates, Map.get(context, :name_candidates, []))
      |> Keyword.put(:available_candidates, Map.get(context, :name_candidates, []))
      |> Keyword.put(:arity, Map.get(context, :name_arity))
      |> Keyword.put(:checking, Map.get(context, :checking))

    namespace = if kind == :unknown_family, do: :type, else: :constructor
    unknown_name(namespace, name, opts)
  end

  def from_error({:source_context, {:foreign_ctor, constructor}, context}, opts) when is_map(context),
    do: foreign_constructor(constructor, context, opts)

  def from_error({:source_context, {:shadowed_ctor, info}, context}, opts) when is_map(context) and is_list(info),
    do: shadowed_constructor(info, context, opts)

  def from_error({:shadowed_ctor, info}, opts) when is_list(info),
    do: shadowed_constructor(info, %{}, opts)

  def from_error({:no_such_interface, %{interface: interface} = details}, opts) do
    opts =
      opts
      |> Keyword.put(:span, Map.get(details, :span) || Keyword.get(opts, :span))
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))

    unknown_name(:interface, interface, opts)
  end

  def from_error({:no_such_interface, interface}, opts),
    do: unknown_name(:interface, interface, opts)

  def from_error({:unknown_interface_method, interface, method}, opts),
    do: unknown_name(:member, method, Keyword.put(opts, :checking, interface))

  def from_error({:unknown_interface_method, %{interface: interface, method: method} = details}, opts) do
    opts =
      opts
      |> Keyword.put(:span, Map.get(details, :span) || Keyword.get(opts, :span))
      |> Keyword.put(:checking, interface)
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))

    unknown_name(:member, method, opts)
  end

  def from_error({:source_context, {:no_named_instance, name}, context}, opts) when is_map(context) do
    span = Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Named instance not found",
      body: Doc.paragraph("The named instance `#{name_to_string(name)}` is not available in this scope."),
      primary: pickup_label(span, :primary, "import or define this named instance"),
      payload: %{kind: :no_named_instance, name: name, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:implementation_scope, %{kind: kind} = details}, opts)
      when kind in [:member_outside, :empty],
      do: implementation_scope_failure(kind, details, opts)

  def from_error({:ambiguous_name, name, modules}, opts) when is_list(modules),
    do: ambiguous_name(name, modules, opts)

  def from_error({:ambiguous_method, method, interfaces}, opts) when is_list(interfaces),
    do: ambiguous_member(method, interfaces, opts)

  def from_error({:duplicate_module, name, paths}, opts) when is_list(paths),
    do: duplicate_module(name, paths, opts)

  def from_error({:duplicate_module_identity, name, other_path, path}, opts),
    do: duplicate_module(name, [other_path, path], opts)

  def from_error({:duplicate_module_identity, name, paths}, opts) when is_list(paths),
    do: duplicate_module(name, paths, opts)

  def from_error({:cyclic_typealiases, aliases}, opts),
    do: declaration_conflict(:cyclic_typealiases, %{aliases: aliases}, opts)

  def from_error({:module_identity_mismatch, requested, declared, path}, opts),
    do: declaration_conflict(:module_identity_mismatch, %{requested: requested, declared: declared, path: path}, opts)

  def from_error({:module_path_identity_mismatch, path, declared, requested}, opts),
    do:
      declaration_conflict(
        :module_path_identity_mismatch,
        %{path: path, declared: declared, requested: requested},
        opts
      )

  def from_error(:shadowed, opts), do: declaration_conflict(:shadowed, %{}, opts)

  def from_error({:sibling_module_collision, name, owners}, opts) when is_list(owners),
    do: sibling_module_collision(name, owners, %{}, opts)

  def from_error({:sibling_module_collision, %{name: name} = details}, opts),
    do: sibling_module_collision(name, Map.get(details, :owners, []), details, opts)

  def from_error({:precedence_cycle, %{groups: groups} = details}, opts) when is_list(groups),
    do: operator_conflict(:precedence_cycle, details, opts)

  def from_error({:precedence_cycle, groups}, opts) when is_list(groups),
    do: operator_conflict(:precedence_cycle, %{groups: groups}, opts)

  def from_error({:conflicting_operator_fixity, details}, opts) when is_map(details),
    do: operator_conflict(:conflicting_operator_fixity, details, opts)

  def from_error({:conflicting_precedence_group, details}, opts) when is_map(details),
    do: operator_conflict(:conflicting_precedence_group, details, opts)

  def from_error({:overlapping_overload, name, arity}, opts),
    do: overlapping_overload(name, arity, opts)

  def from_error({:overlapping_overload, %{name: name, first: first, second: second} = details}, opts),
    do: overlapping_overload(name, first, second, details, opts)

  def from_error({:overlapping_instance, interface, head}, opts),
    do: overlapping_instance(interface, head, opts)

  def from_error({:overlapping_instance, %{interface: interface, head: head} = details}, opts),
    do: overlapping_instance(interface, head, details, opts)

  def from_error({:overlapping_named_instance, name, interface, head}, opts),
    do: overlapping_named_instance(name, interface, head, opts)

  def from_error({:overlapping_named_instance, %{name: name} = details}, opts),
    do: overlapping_named_instance(name, details, opts)

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
      do: duplicate_declaration(kind, if(is_map(name), do: name, else: %{name: name}), opts)

  def from_error({:missing_method, interface, method}, opts),
    do: missing_method(interface, method, opts)

  def from_error({:missing_method, %{interface: interface, method: method} = details}, opts),
    do: missing_method(interface, method, details, opts)

  def from_error({:missing_method, details}, opts) when is_map(details),
    do: missing_method(Map.get(details, :interface), Map.get(details, :method), details, opts)

  def from_error({:method_signature_mismatch, interface, method}, opts),
    do: interface_failure(:method_signature_mismatch, %{interface: interface, method: method}, opts)

  def from_error({:method_signature_mismatch, %{interface: _interface, method: _method} = details}, opts),
    do: method_signature_failure(details, opts)

  def from_error({:instance_head_ill_formed, %{reason: reason} = details}, opts),
    do: instance_head_failure(reason, details, opts)

  def from_error({:instance_head_ill_formed, reason}, opts),
    do: interface_failure(:instance_head_ill_formed, %{reason: reason}, opts)

  def from_error({:missing_superinterface, interface, super_interface, head}, opts),
    do:
      interface_failure(
        :missing_superinterface,
        %{interface: interface, superinterface: super_interface, head: head},
        opts
      )

  def from_error(
        {:missing_superinterface,
         %{interface: interface, superinterface: super_interface, head: canonical_head} = details},
        opts
      ),
      do: missing_superinterface(interface, super_interface, Map.put(details, :canonical_head, canonical_head), opts)

  def from_error({:missing_superinterface, %{interface: interface, superinterface: super_interface} = details}, opts),
    do: missing_superinterface(interface, super_interface, details, opts)

  def from_error({:cannot_derive, interface}, opts),
    do: deriving_failure(:cannot_derive, %{interface: interface}, %{}, opts)

  def from_error({:deriving_needs_strings, interface}, opts),
    do: deriving_failure(:deriving_needs_strings, %{interface: interface}, %{}, opts)

  def from_error({:deriving_needs_constraints, interface, type_name}, opts),
    do: deriving_failure(:deriving_needs_constraints, %{interface: interface, type: type_name}, %{}, opts)

  def from_error({:cannot_derive_shape, interface, type_name}, opts),
    do: deriving_failure(:cannot_derive_shape, %{interface: interface, type: type_name}, %{}, opts)

  def from_error({:cannot_derive_method, interface, method, reason}, opts),
    do: deriving_failure(:cannot_derive_method, %{interface: interface, method: method, reason: reason}, %{}, opts)

  def from_error({:source_context, {:cannot_derive, interface}, context}, opts) when is_map(context),
    do: deriving_failure(:cannot_derive, %{interface: interface}, context, opts)

  def from_error({:source_context, {:deriving_needs_strings, interface}, context}, opts) when is_map(context),
    do: deriving_failure(:deriving_needs_strings, %{interface: interface}, context, opts)

  def from_error({:source_context, {:deriving_needs_constraints, interface, type_name}, context}, opts)
      when is_map(context),
      do: deriving_failure(:deriving_needs_constraints, %{interface: interface, type: type_name}, context, opts)

  def from_error({:source_context, {:cannot_derive_shape, interface, type_name}, context}, opts)
      when is_map(context),
      do: deriving_failure(:cannot_derive_shape, %{interface: interface, type: type_name}, context, opts)

  def from_error({:source_context, {:cannot_derive_method, interface, method, reason}, context}, opts)
      when is_map(context),
      do:
        deriving_failure(:cannot_derive_method, %{interface: interface, method: method, reason: reason}, context, opts)

  def from_error({:inconsistent_head_kind, interface}, opts),
    do: inconsistent_interface_head(interface, %{}, opts)

  def from_error({:source_context, {:inconsistent_head_kind, interface}, context}, opts)
      when is_map(context),
      do: inconsistent_interface_head(interface, context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :shadowed} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_guard_binding_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: reason} = details}, context},
        opts
      )
      when reason in [
             :shadowed_sub_union,
             :shadowed_literal_member,
             :shadowed_as,
             :shadowed_nested,
             :shadowed_tuple,
             :shadowed_tuple_arg,
             :shadowed_catchall,
             :shadowed_literal_catchall,
             :shadowed_default
           ] and is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  @doc false
  def ambiguous_name(name, modules, opts \\ []) do
    spelling = name_to_string(name)
    owners = Enum.map(modules, &name_to_string/1)

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Ambiguous name",
      body: Doc.paragraph("`#{spelling}` is provided by more than one imported module."),
      primary: primary(opts, "qualification is required here"),
      suggestions: [
        %Suggestion{
          message: "Qualify the name as #{Enum.map_join(owners, " or ", &"`#{&1}.#{spelling}`")}",
          applicability: :manual
        }
      ],
      payload: %{namespace: :value, name: spelling, owners: owners}
    )
  end

  @doc false
  def duplicate_module(name, paths, opts \\ []) do
    module = name_to_string(name)

    Diagnostic.new(
      code: "E087",
      key: :duplicate_module,
      severity: :error,
      title: "Duplicate module",
      message: "Module `#{module}` is declared by more than one file: #{Enum.join(paths, ", ")}.",
      primary: primary(opts, "one declaration is here"),
      payload: %{module: module, paths: paths}
    )
  end

  @doc false
  def sibling_module_collision(name, owners, details, opts) do
    name = name_to_string(name)
    spans = Map.get(details, :spans, [])
    detail = " across modules #{Enum.map_join(owners, ", ", &name_to_string/1)}"
    {primary, secondary} = declaration_labels(spans, opts, "this name is already declared in another sibling module")

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Name repeated across sibling modules",
      body:
        Doc.paragraph(
          "The name `#{name}` is declared#{detail}. Sibling modules in one source file currently share an elaboration namespace, so one declaration would overwrite the other. Rename one declaration or move the modules into separate source files."
        ),
      primary: primary,
      secondary: secondary,
      suggestions: [],
      payload: Map.merge(details, %{kind: :sibling_module_collision, name: name, owners: owners})
    )
  end

  @doc false
  def overlapping_overload(name, arity, opts) do
    name = name_to_string(name)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Declaration conflict",
      body: Doc.paragraph("The declaration `#{name}` conflicts with another visible declaration with arity #{arity}."),
      primary: primary(opts, "rename this declaration or make its identity unique"),
      suggestions: [],
      payload: %{kind: :overlapping_overload, name: name, arity: arity}
    )
  end

  def overlapping_overload(name, first, second, details, opts) do
    name = name_to_string(name)
    first_signature = overload_signature(name, first)
    second_signature = overload_signature(name, second)
    primary_span = Map.get(second, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(first, :span) do
        %Span{} = span when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "the first indistinguishable `#{name}` overload is here"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Overloads of `#{name}` cannot be distinguished",
      body:
        Doc.paragraph(
          "Both declarations accept the same parameter types and required argument labels. A call cannot provide enough information to choose between them."
        ),
      primary: pickup_label(primary_span, :primary, "this overload has the same callable signature as the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Change a parameter type or required argument label, or rename one function",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :overlapping_overload,
        name: name,
        arity: Map.get(details, :arity),
        first_signature: first_signature,
        second_signature: second_signature,
        first_id: name_to_string(Map.get(first, :id, name)),
        second_id: name_to_string(Map.get(second, :id, name))
      }
    )
  end

  @doc false
  def overlapping_instance(interface, head, opts) do
    interface = name_to_string(interface)
    head = surface_name(head)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Declaration conflict",
      body:
        Doc.paragraph(
          "The declaration `declaration` conflicts with another visible declaration for interface `#{interface}` and head `#{head}`."
        ),
      primary: primary(opts, "rename this declaration or make its identity unique"),
      suggestions: [],
      payload: %{kind: :overlapping_instance, interface: interface, head: head}
    )
  end

  def overlapping_instance(interface, head, details, opts) do
    interface = name_to_string(interface)
    canonical_head = Map.get(details, :head, head)
    head = name_to_string(Map.get(details, :second_for) || Cure.Elab.Name.base(canonical_head) || canonical_head)
    primary_span = Map.get(details, :second_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :first_span) do
        %Span{} = span when span != primary_span ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "the first `#{interface}` implementation for `#{head}` is here"
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementations overlap",
      body:
        Doc.paragraph(
          "There are two anonymous implementations of `#{interface}` for `#{head}`. Cure requires one globally coherent implementation so every call selects the same behavior."
        ),
      primary: pickup_label(primary_span, :primary, "this second implementation conflicts with the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Remove one implementation, or give one an `as` name and select it explicitly",
          applicability: :manual
        }
      ],
      payload: %{kind: :overlapping_instance, interface: interface, head: head, head_id: name_to_string(canonical_head)}
    )
  end

  def overlapping_named_instance(name, interface, head, opts) do
    name = name_to_string(name)
    interface = name_to_string(interface)
    head = surface_name(head)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Declaration conflict",
      body:
        Doc.paragraph(
          "The declaration `#{name}` conflicts with another visible declaration for named interface instance `#{name}`."
        ),
      primary: primary(opts, "rename this declaration or make its identity unique"),
      suggestions: [],
      payload: %{kind: :overlapping_named_instance, name: name, interface: interface, head: head}
    )
  end

  def overlapping_named_instance(name, details, opts) do
    name = name_to_string(name)
    first_interface = name_to_string(Map.get(details, :first_interface, "an interface"))
    second_interface = name_to_string(Map.get(details, :interface, "an interface"))
    first_head = surface_name(Map.get(details, :first_for, Map.get(details, :first_head)))
    second_head = surface_name(Map.get(details, :second_for, Map.get(details, :head)))
    primary_span = Map.get(details, :second_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :first_span) do
        %Span{} = span when span != primary_span ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "`#{name}` first names `#{first_interface}` for `#{first_head}` here"
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation name is already used",
      body:
        Doc.paragraph(
          "The name `#{name}` already selects `#{first_interface}` for `#{first_head}`, so it cannot also select `#{second_interface}` for `#{second_head}`. Named implementations must have distinct names wherever they are in scope."
        ),
      primary: pickup_label(primary_span, :primary, "this second `#{name}` conflicts with the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Choose a different name after `as` for one implementation", applicability: :manual}
      ],
      payload: %{
        kind: :overlapping_named_instance,
        name: name,
        first_interface: first_interface,
        first_head: first_head,
        second_interface: second_interface,
        second_head: second_head
      }
    )
  end

  @doc false
  def duplicate_declaration(kind, details, opts) do
    name = name_to_string(Map.get(details, :name, :declaration))

    detail =
      case kind do
        :duplicate_field ->
          if Map.has_key?(details, :operation),
            do:
              " while #{if(details.operation == :update, do: "updating", else: "constructing")} `#{surface_name(details.record)}`",
            else: ""

        _ ->
          ""
      end

    spans = Map.get(details, :spans, [])

    first_message =
      if Map.get(details, :operation),
        do: "this field was first supplied here",
        else: "the name was first declared here"

    {primary_label_value, secondary} =
      duplicate_labels(spans, opts, duplicate_primary_label(kind, details), first_message)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: duplicate_title(kind),
      body: Doc.paragraph(duplicate_message(kind, name, details, detail)),
      primary: primary_label_value,
      secondary: secondary,
      suggestions: duplicate_suggestions(kind, details),
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def missing_method(interface, method, opts) do
    interface = name_to_string(interface)
    method = name_to_string(method)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Interface method is missing",
      body: Doc.paragraph("The implementation of `#{interface}` does not define required method `#{method}`."),
      primary: primary(opts, "implement this required method"),
      suggestions: [
        %Suggestion{
          message: "Implement `#{method}` with the signature required by `#{interface}`",
          applicability: :manual
        }
      ],
      payload: %{kind: :missing_method, interface: interface, method: method}
    )
  end

  def missing_method(interface, method, details, opts) do
    interface = name_to_string(interface)
    method = name_to_string(method)
    head = name_to_string(Map.get(details, :for, Cure.Elab.Name.base(Map.get(details, :head)) || "this type"))
    head_id = name_to_string(Map.get(details, :head, head))
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation is missing `#{method}`",
      body:
        Doc.paragraph(
          "`#{interface}` requires a method named `#{method}`, but this implementation for `#{head}` does not provide it and the interface has no default implementation."
        ),
      primary: pickup_label(span, :primary, "add `#{method}` beneath this implementation"),
      suggestions: [
        %Suggestion{
          message: "Implement `#{method}` with the signature required by `#{interface}`",
          applicability: :manual
        }
      ],
      payload: %{kind: :missing_method, interface: interface, method: method, head: head, head_id: head_id}
    )
  end

  defp implementation_scope_failure(:member_outside, details, opts) do
    implementation = "#{name_to_string(details.interface)} for #{name_to_string(details.for)}"
    primary_span = Map.get(details, :member_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :implementation_span) do
        %Span{} = span -> [%Label{span: span, style: :secondary, message: "this implementation has no nested members"}]
        _ -> []
      end

    suggestions =
      case Map.get(details, :insertion_span) do
        %Span{} = span ->
          [
            %Suggestion{
              message: "Indent `#{name_to_string(details.member)}` beneath the implementation",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: span, replacement: Map.get(details, :indentation, "  ")}]
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E116",
      key: :implementation_scope,
      severity: :error,
      title: "Implementation member is outside its implementation scope",
      body:
        Doc.paragraph(
          "`#{name_to_string(details.member)}` appears to implement `#{implementation}`, but it is aligned outside that implementation. Implementation members must be indented beneath their `implementation` declaration."
        ),
      primary: pickup_label(primary_span, :primary, "indent this member so it belongs to the implementation"),
      secondary: secondary,
      suggestions: suggestions,
      payload: details
    )
  end

  defp implementation_scope_failure(:empty, details, opts) do
    span = Map.get(details, :implementation_span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E116",
      key: :implementation_scope,
      severity: :error,
      title: "Implementation has no members",
      body:
        Doc.paragraph(
          "The implementation of `#{name_to_string(details.interface)}` for `#{name_to_string(details.for)}` is empty. Every implementation must contain at least one nested member."
        ),
      primary: pickup_label(span, :primary, "add the implementation's members beneath this declaration"),
      suggestions: [
        %Suggestion{
          message: "Add and indent the required interface members beneath this implementation",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  @doc false
  def interface_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :method_signature_mismatch ->
          {"Interface method signature mismatch",
           "Method `#{name_to_string(details.method)}` does not match the signature required by `#{name_to_string(details.interface)}`.",
           "make this method match the interface signature"}

        :instance_head_ill_formed ->
          {"Instance head is not well formed",
           "The interface instance head cannot be used as a valid implementation head.",
           "use a well-formed instance head"}

        :missing_superinterface ->
          {"Required superinterface is missing",
           "Interface `#{name_to_string(details.interface)}` requires `#{name_to_string(details.superinterface)}` for this implementation.",
           "implement the required superinterface first"}
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

  @doc false
  def instance_head_failure(reason, details, opts) do
    interface = name_to_string(Map.get(details, :interface, "this interface"))
    authored_head = name_to_string(Map.get(details, :for, "this expression"))
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    {explanation, label, hint} =
      case reason do
        :not_type_head ->
          {
            "`#{authored_head}` is a value, but an implementation can only be declared for a type. Cure needs a type constructor here so it can select this implementation consistently.",
            "this is a value, not an implementation type",
            "Replace `#{authored_head}` with the name of a type that implements `#{interface}`"
          }

        :lowering_failed ->
          {
            "Cure could not interpret `#{authored_head}` as a type for this `#{interface}` implementation.",
            "this implementation head is not a valid type",
            "Use a well-formed type after `for`"
          }
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation head is not a type",
      body: Doc.paragraph(explanation),
      primary: pickup_label(span, :primary, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: :instance_head_ill_formed, reason: reason, interface: interface, authored_head: authored_head}
    )
  end

  @doc false
  def missing_superinterface(interface, super_interface, details, opts) do
    interface = name_to_string(interface)
    super_interface = name_to_string(super_interface)
    canonical_head = Map.get(details, :canonical_head, Map.get(details, :head))

    head =
      name_to_string(
        Map.get(details, :for, if(canonical_head, do: Cure.Elab.Name.base(canonical_head), else: "this type"))
      )

    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Required implementation is missing",
      body:
        Doc.paragraph(
          "`#{interface}` requires `#{super_interface}`, so implementing `#{interface}` for `#{head}` also requires an implementation of `#{super_interface}` for `#{head}`."
        ),
      primary: pickup_label(span, :primary, "this implementation also needs `#{super_interface}` for `#{head}`"),
      suggestions: [
        %Suggestion{message: "Add `implementation #{super_interface} for #{head}`", applicability: :manual}
      ],
      payload: %{
        kind: :missing_superinterface,
        interface: interface,
        superinterface: super_interface,
        head: head,
        head_id: name_to_string(canonical_head)
      }
    )
  end

  @doc false
  def method_signature_failure(details, opts) do
    interface = name_to_string(details.interface)
    method = name_to_string(details.method)
    expected_surface = if(details.expected, do: surface_type(details.expected), else: "the interface signature")
    actual_surface = if(details.actual, do: surface_type(details.actual), else: "an invalid method signature")
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation method has the wrong signature",
      body:
        Doc.stack([
          Doc.paragraph(
            "`#{method}` in this `#{interface}` implementation has a different signature from the method declared by the interface. Every parameter and the result must agree after substituting the implementation type."
          ),
          TypeAdapter.comparison_doc(details.expected || expected_surface, details.actual || actual_surface)
        ]),
      primary: pickup_label(primary_span, :primary, "this implementation provides the incompatible signature"),
      suggestions: [
        %Suggestion{
          message: "Change `#{method}` to use the parameter and result types required by `#{interface}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :method_signature_mismatch,
        interface: interface,
        method: method,
        expected_surface: expected_surface,
        actual_surface: actual_surface
      }
    )
  end

  @doc false
  def deriving_failure(kind, details, context, opts) do
    {title, message, label, hint} =
      case kind do
        :cannot_derive ->
          {"Cannot derive interface",
           "Cure cannot derive interface `#{name_to_string(details.interface)}` for this declaration.",
           "automatic derivation is unavailable for this interface",
           "Implement `#{name_to_string(details.interface)}` manually, or remove it from the deriving clause"}

        :deriving_needs_strings ->
          {"Deriving requires string support",
           "Interface `#{name_to_string(details.interface)}` can only be derived for a type with string-compatible members.",
           "this derived interface needs string-compatible members",
           "Use string-compatible members, or implement `#{name_to_string(details.interface)}` manually"}

        :deriving_needs_constraints ->
          {"Cannot derive `#{name_to_string(details.interface)}` for `#{name_to_string(details.type)}`",
           "A field of `#{name_to_string(details.type)}` uses one of the type's parameters directly. Deriving `#{name_to_string(details.interface)}` would need an interface dictionary for that parameter, which automatic derivation cannot thread yet.",
           "this derived interface needs a constraint on the type parameter",
           "Implement `#{name_to_string(details.interface)}` for `#{name_to_string(details.type)}` manually, or remove the parameter-typed field"}

        :cannot_derive_shape ->
          {"Cannot derive for this type shape",
           "Interface `#{name_to_string(details.interface)}` cannot be derived for `#{name_to_string(details.type)}` because its shape is unsupported.",
           "automatic derivation does not support this declaration shape",
           "Change the type shape, or implement `#{name_to_string(details.interface)}` manually"}

        :cannot_derive_method ->
          {"Cannot derive interface method",
           "Method `#{name_to_string(details.method)}` of `#{name_to_string(details.interface)}` cannot be generated for this type.",
           "this interface method cannot be generated", "Implement `#{name_to_string(details.method)}` explicitly"}
      end

    primary_span = Map.get(context, :deriving_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    declaration_span = Map.get(context, :declaration_name_span) || Map.get(context, :declaration_span)
    declaration_name = Map.get(context, :checking) || Map.get(details, :type)

    secondary =
      case declaration_span do
        %Span{} = span when span != primary_span ->
          message =
            if declaration_name,
              do: "this declares `#{name_to_string(declaration_name)}`",
              else: "this is the declaration being derived"

          [%Label{span: span, style: :secondary, message: message}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: pickup_label(primary_span, :primary, label) || primary(opts, label),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def inconsistent_interface_head(interface, context, opts) do
    interface = name_to_string(interface)
    parameter = name_to_string(Map.get(context, :head_parameter, "the head parameter"))
    uses = Map.get(context, :head_uses, [])
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    bare = Enum.find(uses, &(&1.kind == :bare and match?(%Span{}, &1.span)))
    applied = Enum.find(uses, &(&1.kind == :applied and match?(%Span{}, &1.span)))
    primary_span = (applied && applied.span) || primary_span

    secondary =
      case bare do
        %{span: %Span{} = span} when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "`#{parameter}` is used as a complete type here"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "`#{interface}` uses `#{parameter}` at two different kinds",
      body:
        Doc.paragraph(
          "The interface head `#{parameter}` is used both as a complete type and as a type constructor such as `#{parameter}(a)`. One interface parameter must have one consistent kind in every method signature."
        ),
      primary:
        pickup_label(primary_span, :primary, "`#{parameter}` is used as a type constructor here") ||
          primary(opts, "use this interface parameter at one consistent kind"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use `#{parameter}` consistently as either a type or a type constructor",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :inconsistent_head_kind,
        interface: interface,
        head_parameter: parameter,
        uses:
          uses
          |> Enum.filter(&(&1.kind in [:bare, :applied]))
          |> Enum.uniq_by(& &1.kind)
          |> Enum.map(&%{kind: &1.kind, method: Map.get(&1, :method)})
      }
    )
  end

  defp duplicate_title(:duplicate_parameter), do: "Duplicate parameter"
  defp duplicate_title(:duplicate_field), do: "Duplicate field"
  defp duplicate_title(:duplicate_index), do: "Duplicate index"
  defp duplicate_title(:duplicate_type), do: "Duplicate type declaration"
  defp duplicate_title(:duplicate_constructor), do: "Duplicate constructor"
  defp duplicate_title(:duplicate_ctor), do: "Duplicate constructor"
  defp duplicate_title(_kind), do: "Declaration conflict"

  defp duplicate_message(:duplicate_parameter, name, _details, _detail),
    do:
      "The parameter `#{name}` is declared more than once. Rename or remove one occurrence so every parameter has a unique name."

  defp duplicate_message(:duplicate_field, name, %{operation: operation, record: record}, _detail)
       when operation in [:construction, :update],
       do:
         "The field `#{name}` is supplied more than once while #{if(operation == :update, do: "updating", else: "constructing")} `#{surface_name(record)}`. A record value can provide each field only once."

  defp duplicate_message(:duplicate_field, name, _details, _detail),
    do:
      "The field `#{name}` is declared more than once. Rename or remove one occurrence so every record field has a unique name."

  defp duplicate_message(:duplicate_type, name, _details, _detail),
    do:
      "The type `#{name}` is declared more than once in this module. Rename or remove one declaration so the type has a unique identity."

  defp duplicate_message(kind, name, _details, _detail) when kind in [:duplicate_ctor, :duplicate_constructor],
    do:
      "The constructor `#{name}` is declared more than once in this module. Rename or remove one declaration so pattern matching stays unambiguous."

  defp duplicate_message(_kind, name, _details, detail),
    do: "The declaration `#{name}` conflicts with another visible declaration#{if(detail == "", do: "", else: detail)}."

  defp duplicate_primary_label(:duplicate_parameter, _details), do: "this parameter repeats an earlier name"

  defp duplicate_primary_label(:duplicate_field, %{operation: operation}) when operation in [:construction, :update],
    do: "this field is supplied again"

  defp duplicate_primary_label(:duplicate_field, _details), do: "this field repeats an earlier name"
  defp duplicate_primary_label(:duplicate_index, _details), do: "this index repeats an earlier name"
  defp duplicate_primary_label(:duplicate_type, _details), do: "this type repeats an earlier declaration"

  defp duplicate_primary_label(kind, _details) when kind in [:duplicate_ctor, :duplicate_constructor],
    do: "this constructor repeats an earlier declaration"

  defp duplicate_primary_label(_kind, _details), do: "rename this declaration or make its identity unique"

  defp duplicate_suggestions(:duplicate_field, %{operation: operation, name: name})
       when operation in [:construction, :update],
       do: [%Suggestion{message: "Remove one `#{name}` field", applicability: :manual}]

  defp duplicate_suggestions(_kind, _details), do: []

  defp duplicate_labels([first, second | rest], _opts, primary_message, first_message) do
    {%Label{span: second, style: :primary, message: primary_message},
     [%Label{span: first, style: :secondary, message: first_message}] ++
       Enum.map(rest, &%Label{span: &1, style: :secondary, message: "another duplicate is here"})}
  end

  defp duplicate_labels(_, opts, primary_message, _first_message), do: {primary(opts, primary_message), []}

  defp overload_signature(name, member) do
    parameters = Enum.map_join(Map.get(member, :parameters, []), ", ", &overload_type_surface/1)
    "#{name}(#{parameters})"
  end

  defp overload_type_surface(type) when is_atom(type) or is_binary(type),
    do: name_to_string(Cure.Elab.Name.base(type) || type)

  defp overload_type_surface(type), do: surface_type(type)

  defp surface_type(type) do
    Cure.Core.Printer.print(type)
  rescue
    ArgumentError -> inspect(type)
  end

  @doc false
  def declaration_conflict(kind, details, opts) do
    name = name_to_string(Map.get(details, :name, :declaration))

    detail =
      case kind do
        :overlapping_overload ->
          " with arity #{Map.get(details, :arity)}"

        :sibling_module_collision ->
          " across modules #{Enum.map_join(Map.get(details, :owners, []), ", ", &name_to_string/1)}"

        :overlapping_instance ->
          " for interface `#{name_to_string(Map.get(details, :interface))}` and head `#{surface_type(Map.get(details, :head))}`"

        :overlapping_named_instance ->
          " for named interface instance `#{name_to_string(Map.get(details, :name))}`"

        _ ->
          ""
      end

    {primary, secondary} = conflict_labels(Map.get(details, :spans, []), opts, kind, details)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: conflict_title(kind),
      body: Doc.paragraph(conflict_message(kind, name, conflict_message_detail(kind, details, detail))),
      primary: primary,
      secondary: secondary,
      suggestions: conflict_suggestions(kind, details),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp conflict_labels([first, second | rest], _opts, kind, details) do
    primary = %Label{span: second, style: :primary, message: duplicate_primary(kind, details)}

    first_message =
      if Map.get(details, :operation),
        do: "this field was first supplied here",
        else: "the name was first declared here"

    secondary =
      [%Label{span: first, style: :secondary, message: first_message}] ++
        Enum.map(rest, &%Label{span: &1, style: :secondary, message: "another duplicate is here"})

    {primary, secondary}
  end

  defp conflict_labels(_spans, opts, kind, details),
    do: {primary(opts, duplicate_primary(kind, details)), []}

  defp conflict_title(:duplicate_parameter), do: "Duplicate parameter"
  defp conflict_title(:duplicate_field), do: "Duplicate field"
  defp conflict_title(:duplicate_index), do: "Duplicate index"
  defp conflict_title(:duplicate_type), do: "Duplicate type declaration"
  defp conflict_title(:duplicate_constructor), do: "Duplicate constructor"
  defp conflict_title(:sibling_module_collision), do: "Name repeated across sibling modules"
  defp conflict_title(_kind), do: "Declaration conflict"

  defp conflict_message_detail(:duplicate_field, %{operation: operation} = details, _detail)
       when operation in [:construction, :update],
       do: details

  defp conflict_message_detail(_kind, _details, detail), do: detail

  defp conflict_message(:duplicate_parameter, name, _detail),
    do:
      "The parameter `#{name}` is declared more than once. Rename or remove one occurrence so every parameter has a unique name."

  defp conflict_message(:duplicate_field, name, %{operation: operation, record: record}) do
    action = if(operation == :update, do: "updating", else: "constructing")

    "The field `#{name}` is supplied more than once while #{action} `#{surface_name(record)}`. A record value can provide each field only once."
  end

  defp conflict_message(:duplicate_field, name, _detail),
    do:
      "The field `#{name}` is declared more than once. Rename or remove one occurrence so every record field has a unique name."

  defp conflict_message(:duplicate_type, name, _detail),
    do:
      "The type `#{name}` is declared more than once in this module. Rename or remove one declaration so the type has a unique identity."

  defp conflict_message(:duplicate_constructor, name, _detail),
    do:
      "The constructor `#{name}` is declared more than once in this module. Rename or remove one declaration so pattern matching stays unambiguous."

  defp conflict_message(:sibling_module_collision, name, detail),
    do:
      "The name `#{name}` is declared#{detail}. Sibling modules in one source file currently share an elaboration namespace, so one declaration would overwrite the other. Rename one declaration or move the modules into separate source files."

  defp conflict_message(_kind, name, detail),
    do: "The declaration `#{name}` conflicts with another visible declaration#{detail}."

  defp duplicate_primary(:duplicate_field, %{operation: operation}) when operation in [:construction, :update],
    do: "this field is supplied again"

  defp duplicate_primary(:duplicate_parameter, _details), do: "this parameter repeats an earlier name"
  defp duplicate_primary(:duplicate_field, _details), do: "this field repeats an earlier name"
  defp duplicate_primary(:duplicate_index, _details), do: "this index repeats an earlier name"
  defp duplicate_primary(:duplicate_type, _details), do: "this type repeats an earlier declaration"
  defp duplicate_primary(:duplicate_constructor, _details), do: "this constructor repeats an earlier declaration"

  defp duplicate_primary(:sibling_module_collision, _details),
    do: "this name is already declared in another sibling module"

  defp duplicate_primary(_kind, _details), do: "rename this declaration or make its identity unique"

  defp conflict_suggestions(:duplicate_field, %{operation: operation, name: name})
       when operation in [:construction, :update],
       do: [%Suggestion{message: "Remove one `#{name}` field", applicability: :manual}]

  defp conflict_suggestions(_kind, _details), do: []

  defp declaration_labels([first, second | rest], _opts, primary_message) do
    {
      %Label{span: second, style: :primary, message: primary_message},
      [%Label{span: first, style: :secondary, message: "the name was first declared here"}] ++
        Enum.map(rest, &%Label{span: &1, style: :secondary, message: "another duplicate is here"})
    }
  end

  defp declaration_labels(_, opts, primary_message),
    do: {primary(opts, primary_message), []}

  @doc false
  def operator_conflict(kind, details, opts) do
    {title, body, primary_message, secondary_message} =
      case kind do
        :precedence_cycle ->
          {"Cyclic operator precedence",
           "The precedence groups #{Enum.map_join(details.groups, ", ", &"`#{name_to_string(&1)}`")} form a cycle, so the compiler cannot decide which operators bind tighter. Remove or reverse one `higher_than`/`lower_than` relation to break the cycle.",
           "this precedence group participates in the cycle", "this precedence group also participates in the cycle"}

        :conflicting_operator_fixity ->
          {"Conflicting operator fixity",
           "The #{details.fixity} operator `#{details.operator}` is assigned to both `#{name_to_string(details.existing_group)}` and `#{name_to_string(details.new_group)}`. Keep one precedence group for this operator, or choose a different operator spelling.",
           "this declaration assigns `#{details.operator}` to `#{name_to_string(details.new_group)}`",
           "the conflicting assignment is here"}

        :conflicting_precedence_group ->
          {"Conflicting precedence group",
           "The precedence group `#{name_to_string(details.name)}` is declared with incompatible associativity or ordering rules. Give the declarations identical bodies, or rename one group.",
           "this declaration conflicts with the earlier group", "the incompatible group declaration is here"}
      end

    {primary, secondary} =
      operator_conflict_labels(Map.get(details, :spans, []), opts, primary_message, secondary_message)

    Diagnostic.new(
      code: "E106",
      key: :operator_declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary,
      secondary: secondary,
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def operator_conflict_labels([first, second | rest], _opts, primary_message, secondary_message) do
    {%Label{span: second, style: :primary, message: primary_message},
     [%Label{span: first, style: :secondary, message: secondary_message}] ++
       Enum.map(rest, &%Label{span: &1, style: :secondary, message: secondary_message})}
  end

  def operator_conflict_labels([span], _opts, primary_message, _secondary_message),
    do: {%Label{span: span, style: :primary, message: primary_message}, []}

  def operator_conflict_labels([], opts, primary_message, _secondary_message),
    do: {primary(opts, primary_message), []}

  @doc false
  def ambiguous_member(method, interfaces, opts \\ []),
    do: ambiguous_member(method, interfaces, %{}, opts)

  def ambiguous_member(method, interfaces, context, opts) do
    spelling = name_to_string(method)
    owners = Enum.map(interfaces, &name_to_string/1)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    declarations =
      context
      |> Map.get(:method_declarations, [])
      |> Enum.filter(&match?(%{span: %Span{}}, &1))

    secondary =
      declarations
      |> Enum.reject(&(&1.span == primary_span))
      |> Enum.map(fn declaration ->
        %Label{
          span: declaration.span,
          style: :secondary,
          message: "`#{spelling}` is also declared by `#{name_to_string(declaration.interface)}` here"
        }
      end)

    primary_owner =
      Enum.find_value(declarations, fn declaration ->
        if declaration.span == primary_span, do: name_to_string(declaration.interface)
      end)

    owner_list = Enum.map_join(owners, " and ", &"`#{&1}`")

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Method `#{spelling}` is declared by multiple interfaces",
      body:
        Doc.paragraph(
          "Both #{owner_list} declare `#{spelling}`. Interface methods share one unqualified namespace, so Cure could not determine which declaration an unqualified `#{spelling}(...)` call should use."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message:
              if(primary_owner,
                do: "`#{primary_owner}` repeats the interface method `#{spelling}`",
                else: "this repeats the interface method `#{spelling}`"
              )
          },
          else: primary(opts, "rename this interface method")
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Rename `#{spelling}` in one interface so every interface method has a unique name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :ambiguous_method,
        method: spelling,
        interfaces: owners,
        declarations:
          Enum.map(declarations, fn declaration ->
            %{interface: name_to_string(declaration.interface)}
          end)
      }
    )
  end

  @doc false
  def shadowed_guard_binding_failure(details, context, opts) do
    name = name_to_string(details.name)
    site = Map.get(details, :site)
    outer_span = Map.get(details, :span)
    shadow_span = Map.get(details, :shadow_span)
    pattern_span = Map.get(details, :pattern_span)
    primary_span = shadow_span || outer_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        case outer_span do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this guard pattern binds `#{name}`")

          _ ->
            nil
        end,
        case pattern_span do
          %Span{} = span when span != primary_span and span != outer_span ->
            pickup_label(span, :secondary, "this is the guarded pattern")

          _ ->
            nil
        end
      ]
      |> Enum.reject(&is_nil/1)

    {title, body} =
      case site do
        :body ->
          {"Fallback branch shadows `#{name}`",
           "This fallback branch substitutes the matched value for `#{name}`, but a binder inside the branch uses the same name. That substitution could capture the inner value."}

        :constructor_branch ->
          {"Guarded constructor branch shadows `#{name}`",
           "This guarded constructor branch renames its pattern field `#{name}` during lowering, but a binder inside the branch uses the same name. That renaming could capture the inner value."}

        _ ->
          {"Guard branch shadows `#{name}`",
           "This guard branch substitutes the matched value for `#{name}`, but a binder inside the branch uses the same name. That substitution could capture the inner value."}
      end

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, "rename this inner binder so it does not shadow `#{name}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give the nested binder a different name and update its branch expression",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :shadowed,
        name: name,
        site: site,
        checking: Map.get(context, :checking)
      }
    )
  end

  @doc false
  def shadowed_sub_union_pattern_failure(details, context, opts) do
    name = name_to_string(details.name)
    reason = Map.get(details, :reason)
    outer_span = Map.get(details, :span)
    shadow_span = Map.get(details, :shadow_span)
    type_span = Map.get(details, :type_span)
    primary_span = shadow_span || outer_span || Map.get(context, :span) || Keyword.get(opts, :span)

    {body, type_message} = shadowing_text(reason, name)

    secondary =
      [
        case outer_span do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this outer pattern binds `#{name}`")

          _ ->
            nil
        end,
        case type_span do
          %Span{} = span when span != primary_span and span != outer_span ->
            pickup_label(span, :secondary, type_message)

          _ ->
            nil
        end
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Nested pattern shadows `#{name}`",
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, "rename this inner binder so it does not shadow `#{name}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give the nested binder a different name and update its branch body",
          applicability: :manual
        }
      ],
      payload: %{kind: :unsupported_pattern, reason: reason, name: name, checking: Map.get(context, :checking)}
    )
  end

  defp shadowing_text(reason, name) do
    case reason do
      :shadowed_catchall ->
        {"This catch-all pattern binds the complete matched value as `#{name}`. A binder inside the branch uses the same name, so substituting the scrutinee could capture the inner value.",
         "this is the value bound by the catch-all"}

      :shadowed_literal_catchall ->
        {"After the preceding literal patterns fail, this catch-all binds the remaining value as `#{name}`. A binder inside the branch uses the same name, so substituting the scrutinee could capture the inner value.",
         "this is the value tested by the literal patterns"}

      :shadowed_default ->
        {"This fallback pattern binds every constructor not handled above as `#{name}`. A binder inside the fallback branch uses the same name, so reconstructing an omitted constructor could capture the inner value.",
         "this fallback receives the constructors not handled above"}

      :shadowed_tuple_arg ->
        {"This tuple pattern inside a constructor binds `#{name}` to one of the field's positions. A binder inside the branch uses the same name, so substituting the projection could capture the inner value.",
         "this constructor field is destructured as a tuple"}

      :shadowed_tuple ->
        {"This tuple pattern binds `#{name}` to one of the tuple's positions. A binder inside the branch uses the same name, so substituting the projection could capture the inner value.",
         "this tuple pattern is projected before its branch is checked"}

      :shadowed_nested ->
        {"This nested constructor pattern binds `#{name}`. A binder inside its branch uses the same name, so lowering the nested pattern could capture the inner value.",
         "this nested pattern is lowered before its branch is checked"}

      :shadowed_as ->
        {"The outer `#{name}` binds the complete value matched by this as-pattern. A nested binder uses the same name, so substituting the reconstructed value could capture the inner binding.",
         "this is the pattern reconstructed for the outer binding"}

      :shadowed_literal_member ->
        {"The outer `#{name}` stands for a literal union member. This nested pattern binds another value with the same name, so rewriting uses of the literal could capture the inner value.",
         "this branch names a literal union member"}

      _ ->
        {"The outer `#{name}` represents a narrowed union value. This nested pattern binds another value with the same name, so rewriting uses of the outer value could capture the inner one.",
         "this branch keeps the remaining union members"}
    end
  end

  defp pickup_label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp pickup_label(_, _style, _message), do: nil

  @doc false
  def record_field_unknown(record, field, available_fields, context, opts) do
    record_name = surface_name(record)
    field = name_to_string(field)
    field_span = Map.get(context, :field_span) || Map.get(context, :span)
    receiver_span = Map.get(context, :receiver_span)

    candidates =
      Enum.map(available_fields, fn candidate ->
        %{
          id: {:record_field, record, candidate},
          name: name_to_string(candidate),
          namespace: :member,
          owner: record,
          imported: true,
          origin: :record_shape
        }
      end)

    ranking_opts =
      opts
      |> Keyword.put(:span, field_span)
      |> Keyword.put(:owner, record)
      |> Keyword.put(:record, record)

    candidate_details = rank_candidates(candidates, field, :member, ranking_opts)

    secondary =
      case receiver_span do
        %Span{} = span when span != field_span ->
          [%Label{span: span, style: :secondary, message: "this value has record type `#{record_name}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "`#{record_name}` has no field `#{field}`",
      body: Doc.paragraph("The record `#{record_name}` does not declare a field named `#{field}`."),
      primary:
        if(field_span,
          do: %Label{span: field_span, style: :primary, message: "`#{record_name}` has no field named `#{field}`"}
        ),
      secondary: secondary,
      suggestions: candidate_suggestions(candidate_details, field, ranking_opts),
      payload: %{
        namespace: :member,
        name: field,
        owner: record,
        record: record,
        candidates: Enum.map(candidate_details, & &1.name),
        candidate_details: candidate_details,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp unknown_record_failure(name, available_records, context, opts) do
    spelling = name_to_string(name)
    name_span = Map.get(context, :record_name_span) || Map.get(context, :span)

    candidates =
      Enum.map(available_records, fn candidate ->
        %{
          id: {:record, candidate},
          name: surface_name(candidate),
          namespace: :record,
          owner: record_owner(candidate),
          imported: true,
          visibility: :public,
          origin: :record_declaration
        }
      end)

    ranking_opts = Keyword.put(opts, :span, name_span)
    candidate_details = rank_candidates(candidates, spelling, :record, ranking_opts)

    suggestions =
      case candidate_suggestions(candidate_details, spelling, ranking_opts) do
        [] ->
          [
            %Suggestion{
              message: "Declare `rec #{spelling}` or import the module that defines it",
              applicability: :manual
            }
          ]

        ranked ->
          ranked
      end

    Diagnostic.new(
      code: "E021",
      key: :unknown_record,
      severity: :error,
      title: "Cannot find record `#{spelling}`",
      body: Doc.paragraph("No record named `#{spelling}` is available in this module or its imports."),
      primary: pickup_label(name_span, :primary, "this record name is not in scope"),
      suggestions: suggestions,
      payload: %{
        record: name,
        candidates: Enum.map(candidate_details, & &1.name),
        candidate_details: candidate_details,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp record_owner(name) do
    case name_to_string(name) |> String.split("#", parts: 2) do
      [owner, _name] -> owner
      [_name] -> nil
    end
  end

  defp record_field_mismatch_failure(name, details, context, opts) do
    unknown = Map.get(details, :unknown, [])
    missing = Map.get(details, :missing, [])
    declared = Map.get(details, :declared, [])
    record = name || Map.get(details, :record)
    field_spans = Map.get(context, :field_spans, %{})
    offending = List.first(unknown)
    field_span = Map.get(field_spans, offending) || Map.get(field_spans, name_to_string(offending))
    record_name_span = Map.get(context, :record_name_span)
    closer_span = Map.get(context, :closer_span)
    primary_span = if(offending, do: field_span, else: closer_span || Map.get(context, :span))

    opts =
      if primary_span,
        do: Keyword.put(opts, :span, primary_span),
        else: Keyword.put_new(opts, :span, Map.get(context, :span))

    candidates = record_field_candidates(offending, declared, record)
    unique_candidate = unique_record_field_candidate(offending, candidates)

    body =
      cond do
        offending && unique_candidate ->
          Doc.paragraph(
            "`#{name_to_string(offending)}` is not a field of `#{name_to_string(record)}`. Did you mean `#{unique_candidate.name}`?"
          )

        offending ->
          Doc.paragraph(
            "`#{name_to_string(offending)}` is not a field of `#{name_to_string(record)}`. Available fields are #{field_list(declared)}."
          )

        missing != [] ->
          Doc.paragraph("This `#{name_to_string(record)}` value is missing #{field_list(missing)}.")

        true ->
          Doc.paragraph("The supplied fields do not match `#{name_to_string(record)}`.")
      end

    suggestions =
      if offending,
        do: record_field_suggestions(offending, candidates, field_span),
        else: missing_record_field_suggestions(missing)

    operation = Map.get(context, :expectation_origin)

    secondary =
      [
        record_operation_label(record_name_span, primary_span, record, operation),
        record_update_base_label(Map.get(context, :base_span), primary_span, operation)
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E022",
      key: :record_field_mismatch,
      severity: :error,
      title: if(offending, do: "Unknown record field", else: "Missing record field"),
      body: body,
      primary:
        pickup_label(
          Keyword.get(opts, :span),
          :primary,
          if(offending,
            do: "this field is not declared by the record",
            else: "add #{missing_field_label(missing)} before this closing brace"
          )
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        record: record,
        declared: declared,
        provided: Map.get(details, :provided, []),
        unknown: unknown,
        missing: missing,
        candidates: candidates,
        checking: Map.get(context, :checking),
        operation: operation
      }
    )
  end

  defp record_field_candidates(nil, _declared, _record), do: []

  defp record_field_candidates(field, declared, record) do
    declared
    |> Enum.map(fn field_name ->
      %{
        id: {record, field_name},
        name: name_to_string(field_name),
        namespace: :field,
        owner: record,
        visibility: :public,
        imported: true,
        origin: :record_shape
      }
    end)
    |> Suggest.rank(name_to_string(field), :field)
  end

  defp record_field_suggestions(field, [%{name: candidate} = first | rest], %Span{} = span) do
    unique? =
      Enum.all?(rest, fn other ->
        Suggest.distance(name_to_string(field), first.name) < Suggest.distance(name_to_string(field), other.name)
      end)

    if unique?,
      do: [
        %Suggestion{
          message: "Replace it with `#{candidate}`",
          applicability: :machine_applicable,
          edits: [%TextEdit{span: span, replacement: candidate}]
        }
      ],
      else: []
  end

  defp record_field_suggestions(_field, _candidates, _span), do: []

  defp unique_record_field_candidate(field, [%{name: candidate} = first | rest]) when not is_nil(field) do
    distance = Suggest.distance(name_to_string(field), candidate)
    if Enum.all?(rest, &(distance < Suggest.distance(name_to_string(field), &1.name))), do: first
  end

  defp unique_record_field_candidate(_field, _candidates), do: nil

  defp record_operation_label(%Span{} = span, primary_span, record, operation) when span != primary_span do
    action =
      if(operation == :record_update,
        do: "this is a `#{surface_name(record)}` update",
        else: "this constructs `#{surface_name(record)}`"
      )

    %Label{span: span, style: :secondary, message: action}
  end

  defp record_operation_label(_span, _primary_span, _record, _operation), do: nil

  defp record_update_base_label(%Span{} = span, primary_span, :record_update) when span != primary_span,
    do: %Label{span: span, style: :secondary, message: "unchanged fields come from this value"}

  defp record_update_base_label(_span, _primary_span, _operation), do: nil

  defp missing_record_field_suggestions([]), do: []

  defp missing_record_field_suggestions(fields) do
    [%Suggestion{message: "Add #{missing_field_label(fields)} before the closing `}`", applicability: :manual}]
  end

  defp missing_field_label([field]), do: "the missing field `#{name_to_string(field)}`"
  defp missing_field_label(fields), do: "the missing fields " <> Enum.map_join(fields, ", ", &"`#{name_to_string(&1)}`")
  defp field_list([field]), do: "`#{name_to_string(field)}`"
  defp field_list(fields), do: Enum.map_join(fields, ", ", &"`#{name_to_string(&1)}`")

  @doc """
  A bare constructor spelling that names an imported family's constructor, in a
  module whose own type declaration has taken that family's name.

  This is distinct from `foreign_constructor/3`: there the constructor simply
  belongs to another type, and the fix is to use one of the scrutinee's own. Here
  the two families share a bare name, so the author almost certainly believed the
  bare constructor still referred to the imported one — and the qualified
  spelling is a real second option, not just a workaround.
  """
  @spec shadowed_constructor(keyword(), map(), keyword()) :: Diagnostic.t()
  def shadowed_constructor(info, context, opts) do
    constructor = Keyword.fetch!(info, :ctor)
    constructor_name = surface_name(constructor)
    module = Keyword.fetch!(info, :shadowed_module)
    local_family_id = Keyword.fetch!(info, :local_family)
    local_family = surface_name(local_family_id)
    qualified = Keyword.get(info, :hint, "#{module}.#{constructor_name}")
    local_constructors = info |> Keyword.get(:local_ctors, []) |> Enum.map(&surface_name/1)

    # Prefer the offending pattern's own span over the whole match, exactly as
    # `foreign_constructor/3` does, so the caret sits on the constructor the
    # author has to change rather than underlining every arm.
    primary_span =
      constructor_pattern_span(context, constructor_name) || Map.get(context, :span) || Keyword.get(opts, :span)

    body =
      Doc.stack([
        Doc.paragraph(
          "`#{constructor_name}` is a constructor of `#{module}`'s `#{local_family}`, " <>
            "but this module declares its own `#{local_family}`. The local declaration takes the bare " <>
            "spelling of the type, so its constructors are the only ones `#{constructor_name}` could name here."
        ),
        available_constructors_paragraph(local_family, local_constructors)
      ])

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "`#{constructor_name}` is shadowed by this module's own `#{local_family}`",
      body: body,
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this names a constructor of `#{module}`, not of the local `#{local_family}`"
          },
          else: primary(opts, "this constructor comes from `#{module}`")
        ),
      suggestions:
        [
          %Suggestion{
            message: "Write `#{qualified}` to name `#{module}`'s constructor explicitly",
            applicability: :manual
          }
        ] ++ local_constructor_suggestions(local_family, local_constructors),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        kind: :shadowed_ctor,
        constructor: constructor_name,
        shadowed_module: module,
        local_family: local_family,
        local_family_id: name_to_string(local_family_id),
        local_constructors: local_constructors,
        qualified_spelling: qualified
      }
    )
  end

  defp constructor_pattern_span(context, constructor_name) do
    context
    |> Map.get(:branch_patterns, [])
    |> Enum.find_value(fn pattern ->
      if name_to_string(Map.get(pattern, :name)) == constructor_name,
        do: Map.get(pattern, :pattern_span) || Map.get(pattern, :span)
    end)
  end

  defp available_constructors_paragraph(_local_family, []),
    do: Doc.paragraph("The local declaration has no constructors of its own.")

  defp available_constructors_paragraph(local_family, constructors),
    do: Doc.paragraph("The local `#{local_family}` provides #{Enum.map_join(constructors, ", ", &"`#{&1}`")}.")

  defp local_constructor_suggestions(_local_family, []), do: []

  defp local_constructor_suggestions(local_family, constructors),
    do: [
      %Suggestion{
        message:
          "Or match a constructor of the local `#{local_family}`: " <>
            Enum.map_join(constructors, ", ", &"`#{&1}`"),
        applicability: :manual
      }
    ]

  @doc false
  def foreign_constructor(constructor, context, opts) do
    constructor_id = name_to_string(constructor)
    constructor_name = surface_name(constructor)
    actual_family_id = Map.get(context, :actual_family)
    expected_family_id = Map.get(context, :expected_family)
    actual_family = surface_name(actual_family_id)
    expected_family = surface_name(expected_family_id)

    pattern_span =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.find_value(fn pattern ->
        if name_to_string(Map.get(pattern, :name)) == constructor_name,
          do: Map.get(pattern, :pattern_span) || Map.get(pattern, :span)
      end)

    primary_span = pattern_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :expectation_span) do
        %Span{} = span when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this match expects constructors from `#{expected_family}`"}]

        _ ->
          []
      end

    expected_constructor_ids = Map.get(context, :expected_constructors, [])
    expected_constructors = Enum.map(expected_constructor_ids, &surface_name/1)

    suggestions =
      case {expected_constructors, primary_span} do
        {[replacement], %Span{} = span} ->
          [
            %Suggestion{
              message: "Replace `#{constructor_name}` with `#{replacement}`",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: span, replacement: replacement <> "()"}]
            }
          ]

        {[_ | _] = constructors, _span} ->
          [
            %Suggestion{
              message: "Use one of #{Enum.map_join(constructors, ", ", &"`#{&1}`")}",
              applicability: :manual
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "`#{constructor_name}` does not belong to `#{expected_family}`",
      body:
        Doc.paragraph(
          "`#{constructor_name}` is a constructor of `#{actual_family}`, but this match scrutinizes `#{expected_family}`. Every constructor pattern must come from the scrutinee's type."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this constructor belongs to `#{actual_family}`, not `#{expected_family}`"
          },
          else: primary(opts, "use a constructor from the matched type")
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        kind: :foreign_ctor,
        constructor: constructor_name,
        constructor_id: constructor_id,
        actual_family: actual_family,
        actual_family_id: name_to_string(actual_family_id),
        expected_family: expected_family,
        expected_family_id: name_to_string(expected_family_id),
        expected_constructors: expected_constructors,
        expected_constructor_ids: Enum.map(expected_constructor_ids, &name_to_string/1)
      }
    )
  end

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []) do
    spelling = name_to_string(name)
    candidate_details = rank_candidates(Keyword.get(opts, :candidates, []), spelling, namespace, opts)
    candidates = Enum.map(candidate_details, & &1.name)
    available_candidates = Keyword.get(opts, :available_candidates, [])
    available_names = available_candidates |> Enum.map(&suggestion_name/1) |> Enum.uniq()

    body =
      case available_names do
        [] ->
          Doc.paragraph(
            "`#{Keyword.get(opts, :display_name, spelling)}` is not available in this #{namespace} namespace."
          )

        names ->
          Doc.stack([
            Doc.paragraph(
              "`#{Keyword.get(opts, :display_name, spelling)}` is not available in this #{namespace} namespace."
            ),
            Doc.paragraph("The matched type provides #{Enum.map_join(names, ", ", &"`#{&1}`")}.")
          ])
      end

    suggestions =
      case {candidate_suggestions(candidate_details, spelling, opts), available_names} do
        {[], [_ | _] = names} ->
          [
            %Suggestion{
              message: "Use one of the matched type's constructors: #{Enum.map_join(names, ", ", &"`#{&1}`")}",
              applicability: :manual
            }
          ]

        {ranked, _names} ->
          ranked
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "Unknown #{namespace_title(namespace)}",
      body: body,
      primary: primary(opts, "`#{spelling}` was not found"),
      notes: Keyword.get(opts, :notes, []),
      suggestions: suggestions,
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        namespace: namespace,
        name: spelling,
        candidates: candidates,
        candidate_details: candidate_details,
        available_candidates: available_candidates,
        owner: Keyword.get(opts, :owner),
        record: Keyword.get(opts, :record),
        checking: Keyword.get(opts, :checking),
        arity: Keyword.get(opts, :arity),
        expected_namespace: Keyword.get(opts, :expected_namespace),
        imported_from: Keyword.get(opts, :imported_from),
        kernel_context: Keyword.get(opts, :kernel_context)
      }
    )
  end

  @doc false
  def rank_candidates(candidates, spelling, namespace, opts \\ []),
    do: Suggest.rank(candidates, spelling, namespace, opts)

  @doc false
  def candidate_suggestions([], _spelling, _opts), do: []

  def candidate_suggestions(candidates, spelling, opts) do
    candidates = Enum.filter(candidates, &(Suggest.distance(spelling, candidate_spelling_name(&1)) <= 2))

    if candidates == [] do
      []
    else
      build_candidate_suggestion(candidates, spelling, opts)
    end
  end

  defp build_candidate_suggestion(candidates, spelling, opts) do
    names = Enum.map(candidates, &suggestion_name/1)

    qualification_hint =
      if Enum.any?(candidates, &requires_qualification?/1), do: " Qualify it or import its module.", else: ""

    {applicability, edits} = unique_name_repair(candidates, spelling, opts)

    [
      %Suggestion{
        message: "Did you mean #{Enum.map_join(names, ", ", &"`#{&1}`")}?#{qualification_hint}",
        applicability: applicability,
        edits: edits
      }
    ]
  end

  defp unique_name_repair(
         [%{name: replacement, imported: imported, requires_import: requires_import}],
         spelling,
         opts
       ) do
    case Keyword.get(opts, :span) do
      %Span{} = span when imported != false and requires_import != true and replacement != spelling ->
        {:machine_applicable, [%TextEdit{span: span, replacement: replacement}]}

      _ ->
        {:maybe_incorrect, []}
    end
  end

  defp unique_name_repair(_candidates, _spelling, _opts), do: {:maybe_incorrect, []}

  defp requires_qualification?(%{imported: false}), do: true
  defp requires_qualification?(%{requires_import: true}), do: true
  defp requires_qualification?(_candidate), do: false

  defp named_argument_failure(variant, details, opts) do
    {title, message, label} =
      case variant do
        :unknown_label ->
          {"Unknown named argument", "`#{details.label}` is not a parameter label of this call target.",
           "this name does not match a parameter"}

        :duplicate_label ->
          {"Named argument is supplied twice", "`#{details.label}` fills a parameter that already has an argument.",
           "this parameter was already filled"}

        :positional_after_named ->
          {"Positional argument follows a named argument",
           "Positional arguments must come first; named arguments may follow in any order.",
           "move this positional argument before the named arguments"}

        :missing_label ->
          {"Required named argument is missing",
           "The parameter `#{details.label}` must be supplied by its declared argument name.",
           "write `#{details.label}:` for this argument"}

        :ambiguous_label ->
          {"Named arguments do not select one overload",
           "These names fit more than one candidate, or fail differently across the remaining candidates.",
           "make the target or argument names unambiguous"}
      end

    Diagnostic.new(
      code: "E115",
      key: :named_argument_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: named_argument_primary(details, opts, label),
      secondary: named_argument_labels(details),
      suggestions: named_argument_suggestions(variant, details),
      payload: Map.put(details, :kind, variant)
    )
  end

  defp named_argument_primary(details, opts, message) do
    index = named_argument_index(details)
    span = Enum.at(Map.get(details, :label_spans, []), index) || Enum.at(Map.get(details, :argument_spans, []), index)

    case span || Keyword.get(opts, :span) do
      %Span{} = primary -> %Label{span: primary, style: :primary, message: message}
      _ -> nil
    end
  end

  defp named_argument_labels(details) do
    primary_index = named_argument_index(details)
    label = Map.get(details, :label)

    duplicate_labels =
      details
      |> Map.get(:written, [])
      |> List.wrap()
      |> Enum.with_index()
      |> Enum.flat_map(fn
        {^label, index} when index != primary_index ->
          case Enum.at(Map.get(details, :label_spans, []), index) do
            %Span{} = span -> [%Label{span: span, style: :secondary, message: "`#{label}` is also supplied here"}]
            _ -> []
          end

        _ ->
          []
      end)

    argument_label =
      case Enum.at(Map.get(details, :argument_spans, []), primary_index) do
        %Span{} = span -> [%Label{span: span, style: :secondary, message: "argument value"}]
        _ -> []
      end

    parameter_labels =
      Map.get(details, :parameter_spans, [])
      |> Enum.flat_map(fn
        %Span{} = span -> [%Label{span: span, style: :secondary, message: "parameter declared here"}]
        _ -> []
      end)

    duplicate_labels ++ argument_label ++ parameter_labels
  end

  defp named_argument_index(%{argument_index: index}) when is_integer(index), do: index
  defp named_argument_index(%{parameter_index: index, written: nil}) when is_integer(index), do: index

  defp named_argument_index(details) do
    written = Map.get(details, :written) || []
    label = Map.get(details, :label)
    Enum.find_index(written, &(&1 == label)) || 0
  end

  defp named_argument_suggestions(:missing_label, %{label: label} = details) when is_binary(label) do
    index = named_argument_index(details)
    written = Map.get(details, :written)

    case {written == nil or Enum.at(written, index) == nil, Enum.at(Map.get(details, :argument_spans, []), index)} do
      {true, %Span{} = span} ->
        insertion = %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

        [
          %Suggestion{
            message: "Add the required `#{label}:` argument name",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: insertion, replacement: "#{label}: "}]
          }
        ]

      _ ->
        []
    end
  end

  defp named_argument_suggestions(:unknown_label, %{label: bad, telescope: telescope} = details)
       when is_binary(bad) do
    declared = telescope |> Enum.map(fn {_kind, name} -> name end) |> Enum.reject(&is_nil/1) |> Enum.uniq()

    case {declared, Enum.at(Map.get(details, :label_spans, []), named_argument_index(details))} do
      {[replacement], %Span{} = span} ->
        [
          %Suggestion{
            message: "Replace `#{bad}` with the declared argument name `#{replacement}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: replacement}]
          }
        ]

      _ ->
        []
    end
  end

  defp named_argument_suggestions(_variant, _details), do: []

  defp suggestion_name(%{name: name, owner: owner, imported: false}) when not is_nil(owner),
    do: "#{name_to_string(owner)}.#{name}"

  defp suggestion_name(%{name: name}), do: name
  defp suggestion_name(name), do: name_to_string(name)

  defp candidate_spelling_name(%{name: name}), do: name_to_string(name)
  defp candidate_spelling_name(name), do: name_to_string(name)

  defp primary(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}

      nil ->
        nil
    end
  end

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(:interface), do: "interface"
  defp namespace_title(other), do: to_string(other)

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp surface_name(name) do
    name
    |> name_to_string()
    |> String.split("#")
    |> List.last()
  end
end
