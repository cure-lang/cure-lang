defmodule Cure.Diagnostic.Operational do
  @moduledoc """
  Compatibility facade for operational diagnostics.

  New converter ownership lives in `Cure.Diagnostic.Adapter.Operational`.
  Existing callers may continue constructing the same diagnostics through this
  module while they migrate to the shared host boundary.
  """

  alias Cure.Diagnostic.Adapter.Operational

  def from_error(error, opts \\ []), do: Operational.from_error(error, opts)
  defdelegate file_read(path, reason), to: Operational
  defdelegate file_write(path, reason), to: Operational
  defdelegate dependency(reason), to: Operational
  defdelegate command_failure(command, reason), to: Operational
  defdelegate migration_failure(kind, details), to: Operational
  defdelegate unknown_watch_action(action), to: Operational
  defdelegate migration_warning(details), to: Operational
  defdelegate compiler_warning(details), to: Operational
  defdelegate export_unmappable(reason), to: Operational
  defdelegate snap_missing(path), to: Operational
  defdelegate configuration_warning(message), to: Operational
  def destructive_format_warning(details \\ %{}), do: Operational.destructive_format_warning(details)
  defdelegate usage(message), to: Operational
  def artifact_error(message, details \\ %{}), do: Operational.artifact_error(message, details)
  defdelegate proof_file_missing(detail), to: Operational
  defdelegate proof_verification_failed(detail), to: Operational
  defdelegate proof_schema_incompatible(detail), to: Operational
  defdelegate snap_schema_incompatible(detail), to: Operational
  defdelegate registry_signature_invalid(detail), to: Operational
  defdelegate transparency_log_unreachable(detail), to: Operational
  defdelegate registry_fetch_failed(detail), to: Operational
  defdelegate registry_hash_mismatch(detail), to: Operational
  defdelegate registry_package_not_found(detail), to: Operational
  defdelegate package_version_conflict(name, constraints), to: Operational
  defdelegate undocumented_public_function(file, line), to: Operational

  def internal_exception(exception, stacktrace, opts \\ []),
    do: Operational.internal_exception(exception, stacktrace, opts)

  def impossible_return(context, value, opts \\ []),
    do: Operational.impossible_return(context, value, opts)
end
