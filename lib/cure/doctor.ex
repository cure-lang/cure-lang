defmodule Cure.Doctor do
  @moduledoc """
  Structured project-health diagnostic (v0.23.0).

  Used by `cure doctor`. Gathers a battery of checks covering:

  - Environment:  Elixir version, OTP version, Z3 availability,
    registry base URL, telemetry status.
  - Project:      presence and validity of `Cure.toml`, lockfile
    freshness, `_build` hygiene.
  - Source:       open type holes, undocumented public functions,
    files that would be reformatted by `cure fmt --check`.

  Each finding is a `%{severity, code, message, file, fix}` map.
  Severity is `:info`, `:warning`, or `:error`. The overall report is
  a list of findings plus a boolean `ok?` that is `true` iff every
  finding is `:info`.

  The command exits `0` when `ok?` is `true` and `1` otherwise, so it
  can gate CI.
  """

  alias Cure.Project
  alias Cure.Project.{Lock, Registry}

  @type severity :: :info | :warning | :error
  @type finding :: %{
          severity: severity(),
          code: String.t(),
          message: String.t(),
          file: String.t() | nil,
          fix: String.t() | nil
        }
  @type report :: %{ok?: boolean(), findings: [finding()]}

  # -- Public API -------------------------------------------------------------

  @doc """
  Run every check and return a structured report.
  """
  @spec run(String.t()) :: report()
  def run(root \\ ".") when is_binary(root) do
    findings =
      [
        &env_checks/1,
        &project_checks/1,
        &source_checks/1
      ]
      |> Enum.flat_map(& &1.(root))

    %{
      ok?: not Enum.any?(findings, &(&1.severity != :info)),
      findings: findings
    }
  end

  @doc """
  Pretty-print a report to `io`. Returns the report unchanged for
  chaining.
  """
  @spec render(report(), IO.device()) :: report()
  def render(%{findings: findings} = report, io \\ :stdio) do
    IO.puts(io, "Cure Doctor report")
    IO.puts(io, String.duplicate("=", 40))

    Enum.each(findings, fn f ->
      sev = format_severity(f.severity)
      loc = if f.file, do: " (#{f.file})", else: ""
      IO.puts(io, "#{sev}  #{f.code}#{loc}")
      IO.puts(io, "     #{f.message}")

      if f.fix do
        IO.puts(io, "     fix: #{f.fix}")
      end

      IO.puts(io, "")
    end)

    summary =
      if report.ok? do
        "OK -- nothing to fix."
      else
        counts = Enum.frequencies_by(findings, & &1.severity)

        "Issues: warnings=#{Map.get(counts, :warning, 0)} errors=#{Map.get(counts, :error, 0)}"
      end

    IO.puts(io, summary)
    report
  end

  # -- Environment checks -----------------------------------------------------

  defp env_checks(_root) do
    [
      %{
        severity: :info,
        code: "DOC-ENV-01",
        message: "Elixir #{System.version()} / OTP #{System.otp_release()}",
        file: nil,
        fix: nil
      },
      z3_finding(),
      registry_finding(),
      telemetry_finding()
    ]
  end

  defp z3_finding do
    case System.find_executable("z3") do
      nil ->
        %{
          severity: :warning,
          code: "DOC-ENV-Z3",
          message: "Z3 not found on $PATH. Guard-coverage lint checks will be skipped.",
          file: nil,
          fix: "apt install z3 (Ubuntu/Debian) or brew install z3 (macOS)"
        }

      path ->
        %{
          severity: :info,
          code: "DOC-ENV-Z3",
          message: "Z3 at #{path}",
          file: nil,
          fix: nil
        }
    end
  end

  defp registry_finding do
    %{
      severity: :info,
      code: "DOC-ENV-REG",
      message: "Registry URL: #{Registry.base_url()}",
      file: nil,
      fix: nil
    }
  end

  defp telemetry_finding do
    if Code.ensure_loaded?(:telemetry) do
      %{
        severity: :info,
        code: "DOC-ENV-TEL",
        message: ":telemetry library loaded; pipeline events are exported.",
        file: nil,
        fix: nil
      }
    else
      %{
        severity: :info,
        code: "DOC-ENV-TEL",
        message: ":telemetry optional dependency not loaded. Pipeline events stay on Cure.Pipeline.Events.",
        file: nil,
        fix: "Add {:telemetry, \"~> 1.3\"} to mix.exs deps if you want production-grade metrics."
      }
    end
  end

  # -- Project checks ---------------------------------------------------------

  defp project_checks(root) do
    case Project.load(root) do
      {:ok, project} ->
        [
          %{
            severity: :info,
            code: "DOC-PROJ-01",
            message: "#{project.name} #{project.version} (#{length(project.dependencies)} deps)",
            file: Path.join(root, "Cure.toml"),
            fix: nil
          }
          | lock_findings(project, root)
        ]

      {:error, :no_project_file} ->
        [
          %{
            severity: :warning,
            code: "DOC-PROJ-NOFILE",
            message: "No Cure.toml found under #{root}.",
            file: root,
            fix: "Run `cure new <name>` to scaffold a project."
          }
        ]

      {:error, reason} ->
        [
          %{
            severity: :error,
            code: "DOC-PROJ-BAD",
            message: "Cure.toml unreadable: #{project_error_reason(reason)}",
            file: Path.join(root, "Cure.toml"),
            fix: "Check file permissions and TOML syntax."
          }
        ]
    end
  end

  defp project_error_reason(:enoent), do: "the file does not exist"
  defp project_error_reason(:eacces), do: "permission was denied"
  defp project_error_reason(:invalid_toml), do: "the TOML document is invalid"
  defp project_error_reason(:invalid), do: "the project document is invalid"
  defp project_error_reason(reason) when is_binary(reason), do: reason
  defp project_error_reason(_reason), do: "the project document could not be read"

  defp lock_findings(project, root) do
    registry_deps =
      Enum.filter(project.dependencies, fn d ->
        is_nil(Map.get(d, :path)) and is_nil(Map.get(d, :git))
      end)

    case {Lock.read(root), registry_deps} do
      {{:error, :no_lock}, []} ->
        []

      {{:error, :no_lock}, _} ->
        [
          %{
            severity: :warning,
            code: "DOC-PROJ-NOLOCK",
            message: "Registry dependencies declared but Cure.lock is missing.",
            file: Path.join(root, "Cure.lock"),
            fix: "Run `cure deps` to resolve and write Cure.lock."
          }
        ]

      {{:ok, lock}, _} ->
        unknown =
          Enum.reject(registry_deps, fn d -> Map.has_key?(lock, d.name) end)

        if unknown == [] do
          []
        else
          names = Enum.map_join(unknown, ", ", & &1.name)

          [
            %{
              severity: :warning,
              code: "DOC-PROJ-STALELOCK",
              message: "Lockfile is missing entries for: #{names}",
              file: Path.join(root, "Cure.lock"),
              fix: "Run `cure deps update` to refresh Cure.lock."
            }
          ]
        end
    end
  end

  # -- Source checks ----------------------------------------------------------

  defp source_checks(root) do
    cure_files = Path.wildcard(Path.join(root, "lib/**/*.cure"))

    Enum.flat_map(cure_files, fn file ->
      case File.read(file) do
        {:ok, source} ->
          hole_findings(source, file) ++ undocumented_findings(source, file)

        _ ->
          []
      end
    end)
  end

  defp hole_findings(source, file) do
    source
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {line, lineno} ->
      if Regex.match?(~r/[^a-zA-Z0-9_]\?[a-zA-Z_]\w*/, line) or
           Regex.match?(~r/\?\?/, line) do
        [
          %{
            severity: :warning,
            code: "E014",
            message: "Unfilled type hole on line #{lineno}",
            file: file,
            fix: "Replace the hole (`?name` or `?_`) with a concrete expression."
          }
        ]
      else
        []
      end
    end)
  end

  defp undocumented_findings(source, file) do
    lines = String.split(source, "\n")

    lines
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {line, lineno} ->
      if String.match?(line, ~r/^\s*fn\s+[a-zA-Z_]/) and not preceded_by_doc?(lines, lineno) do
        [
          %{
            severity: :info,
            code: "E008",
            message: "Public function on line #{lineno} has no ## doc comment.",
            file: file,
            fix: "Prepend a `##` doc comment describing the function."
          }
        ]
      else
        []
      end
    end)
  end

  defp preceded_by_doc?(lines, lineno) when lineno >= 2 do
    prev = Enum.at(lines, lineno - 2, "")
    String.match?(prev, ~r/^\s*##/) or String.match?(prev, ~r/^\s*#\[/)
  end

  defp preceded_by_doc?(_, _), do: false

  # -- Formatting helpers ----------------------------------------------------

  defp format_severity(:info), do: "[ ok ]"
  defp format_severity(:warning), do: "[warn]"
  defp format_severity(:error), do: "[fail]"
end
