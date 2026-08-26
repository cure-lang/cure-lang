defmodule Cure.Diagnostic.Adapter.Operational do
  @moduledoc "Explicit diagnostics for failures outside elaboration."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.Label

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

  @doc "Convert an operational failure tuple at a host boundary."
  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, _opts \\ [])

  def from_error({:file_read_error, path, reason}, _opts), do: file_read(path, reason)
  def from_error({:file_write_error, path, reason}, _opts), do: file_write(path, reason)
  def from_error({:dependency_resolution_failed, reason}, _opts), do: dependency(reason)
  def from_error({:command_failed, command, reason}, _opts), do: command_failure(command, reason)
  def from_error({:unknown_watch_action, action}, _opts), do: unknown_watch_action(action)
  def from_error({:migration_warning, details}, _opts) when is_map(details), do: migration_warning(details)
  def from_error({:migration_failed, kind, details}, _opts) when is_map(details), do: migration_failure(kind, details)
  def from_error({:compiler_warning, details}, _opts) when is_map(details), do: compiler_warning(details)
  def from_error({:export_unmappable, reason}, _opts), do: export_unmappable(reason)
  def from_error({:snap_missing, path}, _opts), do: snap_missing(path)
  def from_error({:configuration_warning, message}, _opts), do: configuration_warning(message)

  def from_error({:destructive_format_warning, details}, _opts) when is_map(details),
    do: destructive_format_warning(details)

  def from_error({:usage_error, message}, _opts), do: usage(message)
  def from_error({:artifact_error, message}, _opts), do: artifact_error(message)
  def from_error({:artifact_error, message, details}, _opts), do: artifact_error(message, details)
  def from_error({:proof_file_missing, detail}, _opts), do: proof_file_missing(detail)
  def from_error({:proof_verification_failed, detail}, _opts), do: proof_verification_failed(detail)
  def from_error({:proof_schema_incompatible, detail}, _opts), do: proof_schema_incompatible(detail)
  def from_error({:snap_schema_incompatible, detail}, _opts), do: snap_schema_incompatible(detail)
  def from_error({:registry_signature_invalid, detail}, _opts), do: registry_signature_invalid(detail)
  def from_error({:transparency_log_unreachable, detail}, _opts), do: transparency_log_unreachable(detail)
  def from_error({:registry_fetch_failed, detail}, _opts), do: registry_fetch_failed(detail)
  def from_error({:registry_hash_mismatch, detail}, _opts), do: registry_hash_mismatch(detail)
  def from_error({:registry_package_not_found, detail}, _opts), do: registry_package_not_found(detail)
  def from_error({:fetch_failed, _path, detail}, _opts), do: registry_fetch_failed(detail)
  def from_error({:hash_mismatch, detail}, _opts), do: registry_hash_mismatch(detail)
  def from_error({:package_not_found, name}, _opts), do: registry_package_not_found(name)
  def from_error({:version_conflict, name, constraints}, _opts), do: package_version_conflict(name, constraints)
  def from_error({:invalid_dependency, name}, _opts), do: dependency_failure(:invalid_dependency, %{name: name})

  def from_error({:invalid_constraint, name, reason}, _opts),
    do: dependency_failure(:invalid_constraint, %{name: name, reason: reason})

  def from_error({:no_versions, name}, _opts), do: dependency_failure(:no_versions, %{name: name})

  def from_error({:dependency_clone_failed, name, output}, _opts),
    do: dependency_failure(:dependency_clone_failed, %{name: name, output: output})

  def from_error({:dependency_edition_error, name, reason}, _opts),
    do: dependency_failure(:dependency_edition_error, %{name: name, reason: reason})

  def from_error({:file_error, reason}, _opts), do: command_failure("project", reason)
  def from_error({:edition_error, reason}, _opts), do: command_failure("project", reason)
  def from_error({:decode_failed, reason}, _opts), do: command_failure("registry", reason)
  def from_error({:parse, reason}, _opts), do: command_failure("project", reason)
  def from_error({:unreachable, reason}, _opts), do: transparency_log_unreachable(reason)
  def from_error({:chain_broken, index}, _opts), do: transparency_log_unreachable("chain at #{index}")

  def from_error({:app_resource_write_failed, path, reason}, _opts),
    do: file_write(path, reason)

  def from_error({:write_failed, path, reason}, _opts), do: file_write(path, reason)
  def from_error({:load_failed, reason}, _opts), do: command_failure("beam loader", reason)
  def from_error({:compilation_failed, errors}, _opts), do: command_failure("beam compiler", errors)

  def from_error({:duplicate_app, applications}, _opts),
    do: project_artifact_failure(:duplicate_app, %{applications: applications})

  def from_error({:app_name_mismatch, expected, actual}, _opts),
    do: project_artifact_failure(:app_name_mismatch, %{expected: expected, actual: actual})

  def from_error({:compile_failed, reason}, opts),
    do: Cure.Diagnostic.Adapter.from_error(reason, opts)

  def from_error({:release_build_failed, details}, _opts),
    do:
      diagnostic("E098", :command_failure, "Release script generation failed.", %{
        kind: :release_build,
        details: details
      })

  def from_error({:release_app_missing, app, reason}, _opts),
    do:
      diagnostic("E100", :artifact_error, "Release application `#{app}` is missing: #{file_reason(reason)}", %{
        kind: :release_app_missing,
        app: app,
        reason: reason
      })

  def from_error({:sys_config_read_failed, path, reason}, _opts), do: file_read(path, reason)
  def from_error({:vm_args_read_failed, path, reason}, _opts), do: file_read(path, reason)

  def from_error({:undocumented_public_function, file, line}, _opts), do: undocumented_public_function(file, line)

  def from_error({:dependency_artifact_set_missing, {:package, name}}, _opts) do
    Diagnostic.new(
      code: "E100",
      key: :artifact_error,
      severity: :error,
      title: "Dependency is not built",
      message:
        "The compiled artifact set for dependency `#{name}` is missing. Run `cure deps` from this project before compiling it.",
      payload: %{kind: :dependency_artifact_set_missing, package: name},
      notes: ["Cure only loads dependencies from complete, verified artifact generations."]
    )
  end

  def from_error(error, _opts)
      when is_tuple(error) and tuple_size(error) > 0 and
             elem(error, 0) in @artifact_failure_tags do
    artifact_error("A Cure artifact set failed integrity verification.", %{
      kind: elem(error, 0),
      reason: inspect(error)
    })
  end

  def from_error(error, _opts) when error in @artifact_failure_atoms do
    artifact_error("A Cure artifact manifest failed integrity verification.", %{
      kind: error
    })
  end

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  def file_read(path, reason),
    do:
      diagnostic("E095", :file_read, "Cannot read `#{path}`: #{file_reason(reason)}", %{
        path: path,
        reason: inspect(reason)
      })

  def file_write(path, reason),
    do:
      diagnostic("E096", :file_write, "Cannot write `#{path}`: #{file_reason(reason)}", %{
        path: path,
        reason: inspect(reason)
      })

  def dependency(reason),
    do:
      diagnostic("E097", :dependency_resolution, "Failed to resolve dependencies: #{file_reason(reason)}", %{
        reason: inspect(reason)
      })

  def command_failure(command, reason),
    do:
      diagnostic("E098", :command_failure, "#{command} failed: #{file_reason(reason)}", %{
        command: command,
        reason: inspect(reason)
      })

  def migration_failure(kind, details) when is_atom(kind) and is_map(details) do
    message =
      case {kind, details} do
        {:project_downgrade, %{target: target, current: current}} ->
          "Cannot migrate to edition `#{target}` because the project uses newer edition `#{current}`."

        {:invalid_project_edition, %{edition: edition, path: path}} ->
          "The edition `#{edition}` declared in `#{path}` is not supported."

        {:unknown_target_edition, %{edition: edition}} ->
          "The migration target edition `#{edition}` is not supported."

        {:git_guard, %{path: path, reason: reason}} ->
          "Cannot migrate `#{path}` because it is #{migration_guard_reason(reason)}."

        {:file_downgrade, %{path: path, from: from, target: target}} ->
          "Cannot migrate `#{path}` from edition `#{from}` to older edition `#{target}`."

        {:preflight, %{path: path}} ->
          "Could not migrate `#{path}` without producing invalid syntax or changing its comments."

        {:manual_required, %{path: path, rules: rules}} ->
          "`#{path}` needs a manual migration for #{format_rules(rules)}."

        {:strict_warning, %{path: path, rules: rules}} ->
          "`#{path}` has fixable migration warnings rejected by `--strict`: #{format_rules(rules)}."

        _ ->
          "Migration failed (#{kind})."
      end

    diagnostic("E098", :command_failure, message, Map.put(details, :kind, kind))
  end

  def unknown_watch_action(action),
    do: diagnostic("E098", :command_failure, "unknown watch action `#{display_value(action)}`", %{action: action})

  def migration_warning(%{rule: rule, file: file, line: line, message: message} = details) do
    Diagnostic.new(
      code: "W001",
      key: :migration_warning,
      severity: :warning,
      title: "Migration warning",
      message: message,
      primary: warning_primary(details, "deprecated syntax appears here"),
      suggestions: Map.get(details, :suggestions, []),
      payload: %{rule: rule, file: file, line: line}
    )
  end

  def compiler_warning(%{file: file, line: line, message: message} = details) do
    Diagnostic.new(
      code: "W000",
      key: :compiler_warning,
      severity: :warning,
      title: "Compiler warning",
      message: message,
      primary: warning_primary(details, "compiler warning applies here"),
      payload: %{file: file, line: line}
    )
  end

  defp warning_primary(%{span: %Cure.Diagnostic.Span{} = span}, message),
    do: %Label{span: span, style: :primary, message: message}

  defp warning_primary(_details, _message), do: nil

  def export_unmappable(reason),
    do: diagnostic("E068", :export_type_unmappable, "Export type cannot be represented: #{reason}", %{reason: reason})

  def snap_missing(path),
    do: diagnostic("E070", :snap_path_missing, "Snap loaded path no longer exists: #{path}", %{path: path})

  def configuration_warning(message), do: diagnostic("W002", :configuration_warning, message, %{})

  def destructive_format_warning(details \\ %{}) when is_map(details) do
    Diagnostic.new(
      code: "W003",
      key: :destructive_format_warning,
      severity: :warning,
      title: title(:destructive_format_warning),
      message:
        "`cure fmt --aggressive` rebuilds source from the AST, so plain `#` comments and non-canonical whitespace may be removed.",
      notes: [Cure.Diagnostic.Doc.paragraph("Commit or copy these files before continuing.")],
      payload: Map.put_new(details, :mode, :aggressive)
    )
  end

  def usage(message), do: diagnostic("E099", :usage_error, message, %{})

  def artifact_error(message, details \\ %{}) when is_map(details),
    do: diagnostic("E100", :artifact_error, message, details)

  def proof_file_missing(detail),
    do: diagnostic("E065", :proof_file_missing, "Proof file is missing: #{detail}", %{detail: detail})

  def proof_verification_failed(detail),
    do: diagnostic("E066", :proof_verification_failed, "Proof verification failed: #{detail}", %{detail: detail})

  def proof_schema_incompatible(detail),
    do: diagnostic("E067", :proof_schema_incompatible, "Proof schema is incompatible: #{detail}", %{detail: detail})

  def snap_schema_incompatible(detail),
    do: diagnostic("E069", :snap_schema_incompatible, "Snap schema is incompatible: #{detail}", %{detail: detail})

  def registry_signature_invalid(detail),
    do: diagnostic("E041", :registry_signature_invalid, "Registry signature is invalid: #{detail}", %{detail: detail})

  def transparency_log_unreachable(detail),
    do:
      diagnostic("E042", :transparency_log_unreachable, "Transparency log is unreachable: #{detail}", %{detail: detail})

  def registry_fetch_failed(detail),
    do: diagnostic("E038", :registry_fetch_failed, "Registry fetch failed: #{detail}", %{detail: detail})

  def registry_hash_mismatch(detail),
    do: diagnostic("E039", :registry_hash_mismatch, "Registry hash mismatch: #{detail}", %{detail: detail})

  def registry_package_not_found(detail),
    do: diagnostic("E040", :registry_package_not_found, "Registry package not found: #{detail}", %{detail: detail})

  def package_version_conflict(name, constraints),
    do:
      diagnostic(
        "E030",
        :package_version_conflict,
        "Package version conflict for #{name}: #{display_constraints(constraints)}",
        %{
          package: name,
          constraints: constraints
        }
      )

  defp dependency_failure(kind, details) do
    message =
      case kind do
        :invalid_dependency ->
          "Dependency `#{details.name}` has an invalid source declaration."

        :invalid_constraint ->
          "Dependency `#{details.name}` has an invalid version constraint: #{file_reason(details.reason)}."

        :no_versions ->
          "No published versions are available for dependency `#{details.name}`."

        :dependency_clone_failed ->
          "Cloning dependency `#{details.name}` failed: #{details.output}."

        :dependency_edition_error ->
          "Dependency `#{details.name}` declares an unsupported edition: #{file_reason(details.reason)}."
      end

    diagnostic("E097", :dependency_resolution, message, Map.put(details, :kind, kind))
  end

  defp project_artifact_failure(kind, details) do
    message =
      case kind do
        :duplicate_app ->
          "The project contains more than one application module: #{display_names(details.applications)}."

        :app_name_mismatch ->
          "The application module name `#{details.actual}` does not match the project name `#{details.expected}`."
      end

    diagnostic("E100", :artifact_error, message, Map.put(details, :kind, kind))
  end

  def undocumented_public_function(file, line) do
    Diagnostic.new(
      code: "E008",
      key: :undocumented_public_function,
      severity: :information,
      title: "Undocumented public function",
      message: "Public function on line #{line} in #{file} has no ## doc comment.",
      payload: %{file: file, line: line},
      notes: ["Prepend a `##` doc comment describing the function."]
    )
  end

  @doc "Build E101 only for a caught exception at an explicit compiler boundary."
  def internal_exception(exception, stacktrace, opts \\ []) when is_exception(exception) and is_list(stacktrace) do
    internal_context = Cure.Diagnostic.InternalContext.normalize(opts)

    fingerprint =
      fingerprint({exception.__struct__, Exception.message(exception), stack_head(stacktrace), internal_context})

    payload =
      Map.merge(internal_context, %{
        fingerprint: fingerprint,
        exception: inspect(exception.__struct__),
        context: Keyword.get(opts, :context)
      })

    payload = if Keyword.get(opts, :debug, false), do: Map.put(payload, :stacktrace, stacktrace), else: payload

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Internal compiler error",
      message: "The compiler failed unexpectedly. Please report fingerprint `#{fingerprint}`.",
      primary: internal_primary(internal_context.span),
      provenance: internal_context.provenance,
      payload: payload
    )
  end

  @doc "Build E101 for a return shape that violates an internal boundary contract."
  def impossible_return(context, value, opts \\ []) do
    internal_context = Cure.Diagnostic.InternalContext.normalize(opts)
    fingerprint = fingerprint({context, value, internal_context})
    impossible_shape = Cure.Diagnostic.InternalContext.bounded_term(value)

    evidence =
      [
        "Boundary: `#{context}`.",
        if(internal_context.declaration, do: "Declaration: `#{internal_context.declaration}`."),
        if(internal_context.core_term, do: "Failing Core term: `#{internal_context.core_term}`."),
        if(internal_context.expected_type, do: "Expected type: `#{internal_context.expected_type}`."),
        if(internal_context.inferred_type, do: "Inferred type: `#{internal_context.inferred_type}`."),
        if(internal_context.unresolved_global,
          do: "Unresolved global: `#{internal_context.unresolved_global}`."
        ),
        "Received: `#{impossible_shape}`."
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Internal compiler error",
      message: "The compiler reached an impossible state. #{evidence} Please report fingerprint `#{fingerprint}`.",
      primary: internal_primary(internal_context.span),
      provenance: internal_context.provenance,
      payload:
        Map.merge(internal_context, %{
          fingerprint: fingerprint,
          context: context,
          impossible_shape: impossible_shape
        })
    )
  end

  defp internal_primary(nil), do: nil

  defp internal_primary(span),
    do: %Cure.Diagnostic.Label{span: span, style: :primary, message: "the compiler failed here"}

  defp diagnostic(code, key, message, payload) do
    Diagnostic.new(
      code: code,
      key: key,
      severity: if(String.starts_with?(code, "W"), do: :warning, else: :error),
      title: title(key),
      message: message,
      payload: payload
    )
  end

  defp title(:file_read), do: "Could not read file"
  defp title(:file_write), do: "Could not write file"
  defp title(:dependency_resolution), do: "Dependency resolution failed"
  defp title(:command_failure), do: "Command failed"
  defp title(:export_type_unmappable), do: "Type cannot cross this boundary"
  defp title(:snap_path_missing), do: "Saved path is missing"
  defp title(:configuration_warning), do: "Invalid configuration"
  defp title(:destructive_format_warning), do: "Formatting may discard source details"
  defp title(:usage_error), do: "Invalid command usage"
  defp title(:artifact_error), do: "Invalid build artifact"
  defp title(:proof_file_missing), do: "Proof file missing"
  defp title(:proof_verification_failed), do: "Proof verification failed"
  defp title(:proof_schema_incompatible), do: "Proof schema incompatible"
  defp title(:snap_schema_incompatible), do: "Snap schema incompatible"
  defp title(:registry_signature_invalid), do: "Registry signature invalid"
  defp title(:transparency_log_unreachable), do: "Transparency log unreachable"
  defp title(:registry_fetch_failed), do: "Registry fetch failed"
  defp title(:registry_hash_mismatch), do: "Registry hash mismatch"
  defp title(:registry_package_not_found), do: "Registry package not found"
  defp title(:package_version_conflict), do: "Package version conflict"

  defp migration_guard_reason(:dirty), do: "modified"
  defp migration_guard_reason(:untracked), do: "not tracked by git"
  defp migration_guard_reason(reason), do: display_value(reason)

  defp format_rules(rules), do: Enum.map_join(rules, ", ", &"`#{&1}`")

  defp fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

  defp stack_head([{module, function, arity, location} | _]), do: {module, function, arity, location}
  defp stack_head(_), do: nil

  defp file_reason(reason) when is_atom(reason), do: :file.format_error(reason)
  defp file_reason({kind, detail}) when is_atom(kind), do: "#{kind}: #{file_reason(detail)}"
  defp file_reason(reason) when is_binary(reason), do: reason
  defp file_reason(_reason), do: "an unexpected operating-system error"

  defp display_value(value) when is_binary(value), do: value
  defp display_value(value) when is_atom(value), do: Atom.to_string(value)
  defp display_value(value) when is_number(value), do: to_string(value)
  defp display_value(_value), do: "an unsupported value"

  defp display_constraints(values) when is_list(values),
    do: Enum.map_join(values, ", ", &display_value/1)

  defp display_constraints(value), do: display_value(value)

  defp display_names(values) when is_list(values),
    do: Enum.map_join(values, ", ", &display_value/1)

  defp display_names(value), do: display_value(value)
end
