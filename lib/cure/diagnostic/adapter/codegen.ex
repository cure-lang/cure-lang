defmodule Cure.Diagnostic.Adapter.Codegen do
  @moduledoc """
  Converts failures from the trusted Core/BEAM emission boundary.

  Ordinary source failures must be converted before they reach this module.
  Every diagnostic produced here is therefore E101 and carries enough stable
  context to report the compiler defect without exposing a stacktrace.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span}
  alias Cure.Diagnostic.InternalContext

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error({:codegen_failure, details}, opts) when is_map(details) do
    opts =
      opts
      |> Keyword.put(:codegen_stage, Map.get(details, :stage))
      |> Keyword.put(:codegen_module, Map.get(details, :module))
      |> Keyword.put(:source_file, Map.get(details, :file, Keyword.get(opts, :source_file)))
      |> Keyword.put(:failure_context, details)
      |> put_detail_opt(:span, details)
      |> put_detail_opt(:provenance, details)

    failure(Map.get(details, :reason), opts)
  end

  def from_error({:codegen_error, reason}, opts), do: failure(reason, opts)
  def from_error({:beam_lint_error, errors, warnings}, opts), do: failure({:beam_lint, errors, warnings}, opts)
  def from_error({:beam_lint_error, errors}, opts), do: failure({:beam_lint, errors}, opts)
  def from_error({:final_core_violation, rejections}, opts), do: final_core(nil, rejections, opts)
  def from_error({:final_core_violation, name, rejections}, opts), do: final_core(name, rejections, opts)
  def from_error({:expected_module, _ast}, opts), do: failure(:expected_module, opts)
  def from_error({:unsupported_container, type}, opts), do: failure({:unsupported_container, type}, opts)
  def from_error({:cannot_emit, reason}, opts), do: failure({:cannot_emit, reason}, opts)

  defp failure(reason, opts) do
    {title, body, kind} = failure_content(reason)
    failure_context = context(reason, Keyword.get(opts, :failure_context, %{}))
    stage = Keyword.get(opts, :codegen_stage) || stage(reason)
    module = Keyword.get(opts, :codegen_module) || Map.get(failure_context, :module)
    file = source_file(opts)
    reason_text = reason_text(reason)
    diagnostic_context = InternalContext.normalize(failure_context)
    fingerprint = fingerprint({stage, module, file, reason, diagnostic_context})

    context =
      [
        "Stage: `#{name(stage)}`.",
        if(module, do: "Module: `#{name(module)}`."),
        if(file, do: "Source: `#{file}`."),
        context_sentence(diagnostic_context),
        "Underlying reason: #{reason_text}.",
        "Diagnostic fingerprint: `#{fingerprint}`."
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: title,
      body: Doc.stack([Doc.paragraph(body), Doc.paragraph(context)]),
      primary: primary(opts, "code generation failed here"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      provenance: Keyword.get(opts, :provenance, Map.get(failure_context, :provenance, [])),
      payload:
        Map.merge(diagnostic_context, %{
          kind: context_kind(reason, kind),
          stage: stage,
          module: module,
          file: file,
          reason: reason_text,
          fingerprint: fingerprint
        })
    )
  end

  defp final_core(name, rejections, opts) when is_list(rejections) do
    clauses = Enum.map(rejections, &Map.get(&1, :clause))
    messages = Enum.map(rejections, &Map.get(&1, :message))
    stage = Keyword.get(opts, :codegen_stage, :final_core_validation)
    module = Keyword.get(opts, :codegen_module)
    file = source_file(opts)

    nodes = Enum.map(rejections, &Map.get(&1, :node)) |> Enum.reject(&is_nil/1)

    diagnostic_context = %{
      declaration: name,
      span: Keyword.get(opts, :span),
      core_term: InternalContext.bounded_term(List.first(nodes)),
      core_trace: nodes,
      expected_type: rejections |> first_present(:expected_type) |> InternalContext.bounded_term(),
      inferred_type: rejections |> first_present(:inferred_type) |> InternalContext.bounded_term(),
      unresolved_global: Enum.find_value(nodes, &unresolved_global/1),
      closure_path: [],
      provenance: Keyword.get(opts, :provenance, [])
    }

    fingerprint = fingerprint({stage, module, file, name, rejections, diagnostic_context})

    context =
      [
        "Stage: `#{name(stage)}`.",
        if(module, do: "Module: `#{name(module)}`."),
        if(file, do: "Source: `#{file}`."),
        context_sentence(diagnostic_context),
        "Diagnostic fingerprint: `#{fingerprint}`."
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Final-Core validation failed",
      body:
        Doc.stack([
          Doc.paragraph(
            "The compiler rejected an internal Core term at the trusted boundary (#{Enum.join(Enum.map(messages, &to_string/1), "; ")})."
          ),
          Doc.paragraph(context)
        ]),
      primary: primary(opts, "this definition produced invalid internal Core"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      provenance: diagnostic_context.provenance,
      payload:
        Map.merge(diagnostic_context, %{
          kind: :final_core_violation,
          name: name,
          clauses: clauses,
          messages: messages,
          stage: stage,
          module: module,
          file: file,
          fingerprint: fingerprint
        })
    )
  end

  defp stage({:beam_lint, _errors}), do: :beam_writer
  defp stage({:beam_lint, _errors, _warnings}), do: :beam_writer
  defp stage({:missing_stdlib_module, _module, _message}), do: :module_resolution
  defp stage(_reason), do: :codegen

  defp failure_content(:expected_module) do
    {"Module emission failed", "The compiler expected a module definition before emitting a BEAM artifact.",
     :expected_module}
  end

  defp failure_content({:unsupported_container, type}) do
    {"Unsupported container", "The compiler cannot emit the `#{name(type)}` container in this context.",
     :unsupported_container}
  end

  defp failure_content({:beam_lint, errors, warnings}) when is_list(errors) and is_list(warnings) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s), #{length(warnings)} warning(s)).",
     :beam_lint}
  end

  defp failure_content({:beam_lint, errors}) when is_list(errors) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s)).", :beam_lint}
  end

  defp failure_content({:missing_stdlib_module, module, message}) do
    {"Stdlib module resolution failed",
     "The compiler could not resolve `#{name(module)}` while generating the BEAM artifact. #{message}",
     :missing_stdlib_module}
  end

  defp failure_content({kind, _details})
       when kind in [:emission_closure_missing, :emission_closure_incomplete, :emission_closure_invalid] do
    {"Invalid emission closure",
     "The compiler found an invalid canonical definition edge before emitting the BEAM artifact.", kind}
  end

  defp failure_content(_reason) do
    {"Code generation failed", "The compiler could not produce a valid BEAM artifact for this source.", :codegen}
  end

  defp reason_text({:beam_lint, errors}), do: beam_diagnostics(errors)

  defp reason_text({:beam_lint, errors, warnings}) do
    errors_text = beam_diagnostics(errors)
    warnings_text = beam_diagnostics(warnings)
    if warnings_text == "no details", do: errors_text, else: errors_text <> "; warnings: " <> warnings_text
  end

  defp reason_text({:compilation_failed, errors}), do: beam_diagnostics(errors)
  defp reason_text(reason), do: human_reason(reason)

  defp beam_diagnostics(diagnostics) do
    diagnostics
    |> List.wrap()
    |> Enum.flat_map(fn
      {_file, entries} when is_list(entries) -> entries
      entry -> [entry]
    end)
    |> Enum.take(3)
    |> Enum.map_join("; ", &beam_diagnostic/1)
    |> case do
      "" -> "no details"
      text -> text
    end
  end

  defp beam_diagnostic({location, formatter, detail}) when is_atom(formatter) do
    message =
      try do
        formatter.format_error(detail) |> IO.iodata_to_binary() |> String.trim()
      rescue
        _ -> human_reason(detail)
      end

    "#{human_reason(location)}: #{message}"
  end

  defp beam_diagnostic(other), do: human_reason(other)

  defp human_reason(value) when is_binary(value), do: value
  defp human_reason(value) when is_atom(value), do: Atom.to_string(value)
  defp human_reason(value) when is_number(value), do: to_string(value)
  defp human_reason(value) when is_list(value), do: value |> Enum.take(3) |> Enum.map_join(", ", &human_reason/1)

  defp human_reason(value) when is_tuple(value) do
    value |> Tuple.to_list() |> Enum.take(4) |> Enum.map_join(": ", &human_reason/1)
  end

  defp human_reason(%_{} = value), do: value |> Map.from_struct() |> human_reason()

  defp human_reason(value) when is_map(value) do
    value
    |> Enum.sort_by(fn {key, _value} -> to_string(key) end)
    |> Enum.take(4)
    |> Enum.map_join(", ", fn {key, nested} -> "#{key}=#{human_reason(nested)}" end)
  end

  defp human_reason(value), do: inspect(value, limit: 4, printable_limit: 120)

  defp source_file(opts) do
    Keyword.get(opts, :source_file) ||
      case Keyword.get(opts, :span) do
        %Span{path: path} -> path
        _ -> nil
      end
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      nil -> nil
    end
  end

  defp put_detail_opt(opts, key, details) do
    case Map.get(details, key) do
      nil -> opts
      value -> Keyword.put(opts, key, value)
    end
  end

  defp context({kind, details}, outer)
       when kind in [:emission_closure_missing, :emission_closure_incomplete, :emission_closure_invalid] and
              is_map(details) do
    outer
    |> Map.merge(details)
    |> Map.put_new(:declaration, Map.get(details, :referenced_by))
    |> Map.put_new(:unresolved_global, Map.get(details, :definition))
    |> Map.put_new_lazy(:closure_path, fn ->
      [Map.get(details, :referenced_by), Map.get(details, :definition)] |> Enum.reject(&is_nil/1)
    end)
  end

  defp context(_reason, outer) when is_map(outer), do: outer

  defp context_sentence(context) do
    parts =
      [
        if(context.declaration, do: "Declaration: `#{name(context.declaration)}`."),
        if(context.unresolved_global, do: "Unresolved global: `#{name(context.unresolved_global)}`."),
        if(context.closure_path != [], do: "Closure path: `#{Enum.map_join(context.closure_path, " -> ", &name/1)}`."),
        if(context.core_term, do: "Failing Core term: `#{context.core_term}`."),
        if(context.expected_type, do: "Expected type: `#{context.expected_type}`."),
        if(context.inferred_type, do: "Inferred type: `#{context.inferred_type}`.")
      ]
      |> Enum.reject(&is_nil/1)

    if parts == [], do: nil, else: Enum.join(parts, " ")
  end

  defp context_kind({kind, _details}, _fallback)
       when kind in [:emission_closure_missing, :emission_closure_incomplete, :emission_closure_invalid],
       do: kind

  defp context_kind(_reason, fallback), do: fallback

  defp first_present(maps, key), do: Enum.find_value(maps, &Map.get(&1, key))

  defp unresolved_global({:global, name}), do: name

  defp unresolved_global(term) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.find_value(&unresolved_global/1)
  end

  defp unresolved_global(terms) when is_list(terms), do: Enum.find_value(terms, &unresolved_global/1)
  defp unresolved_global(_term), do: nil

  defp fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
