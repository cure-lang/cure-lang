defmodule Cure.Diagnostic.Host do
  @moduledoc "Single presentation boundary for compiler and host command output."

  alias Cure.Diagnostic.Sink
  alias Cure.Diagnostic.Adapter.Operational

  @artifact_failure_tags [
    :artifact_set_invalid,
    :no_verified_artifact_set,
    :artifact_kind_mismatch,
    :artifact_manifest_empty,
    :artifact_lock_failed,
    :artifact_sweep_failed,
    :artifact_load_failed,
    :artifact_verification_failed,
    :artifact_modules_missing,
    :duplicate_artifact_modules,
    :artifact_copy_failed,
    :copied_artifact_root_mismatch,
    :resident_artifact_mismatch,
    :dependency_artifact_set_missing,
    :dependency_artifact_set_invalid,
    :dependency_generation_mismatch,
    :stdlib_load_failed,
    :stdlib_repair_failed,
    :stdlib_sources_unavailable
  ]
  @artifact_failure_atoms [
    :manifest_missing,
    :manifest_unreadable,
    :manifest_invalid,
    :manifest_version_unsupported,
    :manifest_root_mismatch
  ]

  @doc "Render a compiler or host failure with its authored source context."
  @spec render(term(), String.t(), String.t() | nil) :: String.t()
  def render(reason, file, source \\ nil) when is_binary(file) do
    {diagnostic, registry} = to_diagnostic(reason, file, source)

    Sink.new(format: :plain, registry: registry)
    |> Sink.render(diagnostic)
  end

  @doc "Convert a host or compiler failure without selecting an output format."
  @spec to_diagnostic(term(), String.t(), String.t() | nil) ::
          {Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t() | nil}
  def to_diagnostic(reason, file, source \\ nil) when is_binary(file) do
    source = source || read_source(file)

    case convert(reason, file, source) do
      {:ok, diagnostic, registry} -> {diagnostic, registry}
    end
  end

  @doc "Render an already-structured diagnostic through the shared sink."
  @spec render_diagnostic(Cure.Diagnostic.t(), keyword()) :: String.t()
  def render_diagnostic(%Cure.Diagnostic{} = diagnostic, opts \\ []) do
    Sink.new(
      format: :plain,
      color: Keyword.get(opts, :color, :auto),
      width: Keyword.get(opts, :width, 80),
      registry: Keyword.get(opts, :registry)
    )
    |> Sink.render(diagnostic)
  end

  @doc "Emit a structured diagnostic through the shared sink."
  @spec emit_diagnostic(Cure.Diagnostic.t(), keyword()) :: {:ok, Sink.t()} | {:error, term()}
  def emit_diagnostic(%Cure.Diagnostic{} = diagnostic, opts \\ []) do
    Sink.new(
      format: :terminal,
      color: Keyword.get(opts, :color, :auto),
      width: Keyword.get(opts, :width, 80),
      output_device: Keyword.get(opts, :output_device, :standard_error),
      registry: Keyword.get(opts, :registry)
    )
    |> Sink.emit(diagnostic)
    |> Sink.flush()
  end

  defp convert(reason, _file, _source) when is_struct(reason, Cure.Diagnostic) do
    {:ok, reason, nil}
  end

  defp convert(reason, file, source) do
    if operational_reason?(reason) do
      diagnostic = Operational.from_error(reason)

      case source do
        source when is_binary(source) and byte_size(source) > 0 ->
          registry =
            Cure.Diagnostic.SourceRegistry.new()
            |> Cure.Diagnostic.SourceRegistry.register(file, source, file)

          {:ok, remap_operational_span(diagnostic, registry, file), registry}

        _ ->
          {:ok, diagnostic, nil}
      end
    else
      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, file, source)
      {:ok, diagnostic, registry}
    end
  rescue
    Cure.Diagnostic.UnhandledError ->
      {underlying_reason, internal_context} = unregistered_context(reason)

      {:ok,
       Operational.impossible_return(
         :unregistered_diagnostic,
         underlying_reason,
         Map.to_list(internal_context)
       ), nil}
  end

  defp unregistered_context({:source_context, reason, context}) when is_map(context) do
    declaration = Map.get(context, :declaration) || Map.get(context, :checking)

    internal_context =
      context
      |> Map.take([
        :span,
        :core_term,
        :core_trace,
        :expected_type,
        :inferred_type,
        :unresolved_global,
        :closure_path,
        :provenance
      ])
      |> Map.put(:declaration, declaration)

    {reason, internal_context}
  end

  defp unregistered_context(reason), do: {reason, %{}}

  defp read_source(file) do
    case File.read(file) do
      {:ok, source} -> source
      {:error, _reason} -> ""
    end
  end

  defp remap_operational_span(
         %Cure.Diagnostic{primary: %Cure.Diagnostic.Label{span: %Cure.Diagnostic.Span{} = span} = label} =
           diagnostic,
         registry,
         source_id
       ) do
    length = if span.end_line == span.start_line, do: max(span.end_column - span.start_column, 0), else: 0

    case Cure.Diagnostic.SourceRegistry.span_at(
           registry,
           source_id,
           span.start_line,
           span.start_column,
           length
         ) do
      {:ok, remapped} -> %{diagnostic | primary: %{label | span: remapped}}
      {:error, _} -> diagnostic
    end
  end

  defp remap_operational_span(
         %Cure.Diagnostic{primary: nil, payload: %{line: line} = payload} = diagnostic,
         registry,
         source_id
       )
       when is_integer(line) and line > 0 do
    {column, length} = operational_line_range(registry, source_id, line, Map.get(payload, :column))

    case Cure.Diagnostic.SourceRegistry.span_at(registry, source_id, line, column, length) do
      {:ok, span} ->
        label = %Cure.Diagnostic.Label{
          span: span,
          style: :primary,
          message: operational_location_message(payload)
        }

        %{diagnostic | primary: label}

      {:error, _} ->
        diagnostic
    end
  end

  defp remap_operational_span(diagnostic, _registry, _source_id), do: diagnostic

  defp operational_line_range(registry, source_id, line, explicit_column) do
    with nil <- explicit_column,
         {:ok, source} <- Cure.Diagnostic.SourceRegistry.fetch(registry, source_id),
         text when is_binary(text) <- Enum.at(String.split(source, "\n", trim: false), line - 1) do
      leading = text |> String.codepoints() |> Enum.take_while(&(&1 in [" ", "\t"])) |> Enum.join()
      content = text |> String.trim_leading() |> String.trim_trailing("\r")
      {String.length(leading) + 1, max(String.length(content), 1)}
    else
      _ -> {explicit_column || 1, 0}
    end
  end

  defp operational_location_message(%{rule: rule}), do: "rule #{rule} applies here"
  defp operational_location_message(_payload), do: "warning applies here"

  defp operational_reason?({:file_read_error, _, _}), do: true
  defp operational_reason?({:file_write_error, _, _}), do: true
  defp operational_reason?({:dependency_resolution_failed, _}), do: true
  defp operational_reason?({:command_failed, _, _}), do: true
  defp operational_reason?({:migration_warning, details}) when is_map(details), do: true
  defp operational_reason?({:compiler_warning, details}) when is_map(details), do: true
  defp operational_reason?({:export_unmappable, _}), do: true
  defp operational_reason?({:snap_missing, _}), do: true
  defp operational_reason?({:configuration_warning, _}), do: true
  defp operational_reason?({:usage_error, _}), do: true
  defp operational_reason?({:artifact_error, _}), do: true
  defp operational_reason?({:artifact_error, _, details}) when is_map(details), do: true
  defp operational_reason?({:proof_file_missing, _}), do: true
  defp operational_reason?({:proof_verification_failed, _}), do: true
  defp operational_reason?({:proof_schema_incompatible, _}), do: true
  defp operational_reason?({:snap_schema_incompatible, _}), do: true
  defp operational_reason?({:registry_signature_invalid, _}), do: true
  defp operational_reason?({:transparency_log_unreachable, _}), do: true
  defp operational_reason?({:registry_fetch_failed, _}), do: true
  defp operational_reason?({:registry_hash_mismatch, _}), do: true
  defp operational_reason?({:registry_package_not_found, _}), do: true
  defp operational_reason?({:version_conflict, _, _}), do: true
  defp operational_reason?({:invalid_dependency, _}), do: true
  defp operational_reason?({:invalid_constraint, _, _}), do: true
  defp operational_reason?({:no_versions, _}), do: true
  defp operational_reason?({:dependency_clone_failed, _, _}), do: true
  defp operational_reason?({:dependency_edition_error, _, _}), do: true
  defp operational_reason?({:unknown_watch_action, _}), do: true
  defp operational_reason?({:file_error, _}), do: true
  defp operational_reason?({:decode_failed, _}), do: true
  defp operational_reason?({:parse, _}), do: true
  defp operational_reason?({:fetch_failed, _, _}), do: true
  defp operational_reason?({:hash_mismatch, _}), do: true
  defp operational_reason?({:package_not_found, _}), do: true
  defp operational_reason?({:unreachable, _}), do: true
  defp operational_reason?({:chain_broken, _}), do: true
  defp operational_reason?({:app_resource_write_failed, _, _}), do: true
  defp operational_reason?({:write_failed, _, _}), do: true
  defp operational_reason?({:load_failed, _}), do: true
  defp operational_reason?({:compilation_failed, _}), do: true
  defp operational_reason?({:duplicate_app, _}), do: true
  defp operational_reason?({:app_name_mismatch, _, _}), do: true
  defp operational_reason?({:compile_failed, _}), do: true
  defp operational_reason?({:release_build_failed, _}), do: true
  defp operational_reason?({:release_app_missing, _, _}), do: true
  defp operational_reason?({:sys_config_read_failed, _, _}), do: true
  defp operational_reason?({:vm_args_read_failed, _, _}), do: true
  defp operational_reason?({:undocumented_public_function, _, _}), do: true
  defp operational_reason?(reason) when reason in @artifact_failure_atoms, do: true

  defp operational_reason?(reason)
       when is_tuple(reason) and tuple_size(reason) > 0 and
              elem(reason, 0) in @artifact_failure_tags,
       do: true

  defp operational_reason?(_), do: false
end
