defmodule Mix.Tasks.Cure.Verify do
  @moduledoc """
  Verify `.cureproof` artifacts in a package tarball or installed
  dependency directory (v0.32.0).

  ## Usage

      mix cure.verify [path]

  Without a `path`, verifies the current project's own proofs by running
  `cure publish --dry-run` in proof-collect mode and replaying the
  collected certificates.

  With a path to:

    * A `.tar.gz` file -- extracts in memory, locates `*.cureproof`
      entries, deserializes, and calls `Cure.Project.Proof.verify/1`.
    * A directory -- recursively locates `*.cureproof` files, then
      verifies each one.

  ## Flags

    * `--strict` -- treat a missing `.cureproof` file as an error (E065).
      Without this flag the absence of a proof artifact is a warning.

  ## Exit codes

    * `0` -- all certificates verified successfully (or no artifact
      found and `--strict` was not set).
    * `1` -- at least one verification failure, or a missing artifact with
      `--strict`.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Verify .cureproof artifacts in a package tarball or dependency directory"

  @impl Mix.Task
  def run(args) do
    {opts, rest, invalid} =
      OptionParser.parse(args, strict: [strict: :boolean])

    if invalid != [] or length(rest) > 1 do
      usage_error("Usage: mix cure.verify [path] [--strict]")
    end

    strict? = Keyword.get(opts, :strict, false)
    path = List.first(rest)

    Application.ensure_all_started(:cure)

    cond do
      is_nil(path) ->
        verify_current_project(strict?)

      String.ends_with?(path, ".tar.gz") or String.ends_with?(path, ".tgz") ->
        verify_tarball(path, strict?)

      File.dir?(path) ->
        verify_directory(path, strict?)

      true ->
        Mix.shell().error(
          render_diagnostic(Cure.Diagnostic.Operational.artifact_error("#{path} is not a .tar.gz file or directory"))
        )

        exit({:shutdown, 1})
    end
  end

  # -- Verification paths -------------------------------------------------------

  defp verify_current_project(strict?) do
    root = File.cwd!()
    Mix.shell().info("Collecting proofs from #{root}...")

    case Cure.Project.Proof.collect(root) do
      {:ok, []} ->
        handle_missing(strict?, "(current project)")

      {:ok, certs} ->
        run_verification(certs, "(current project)")
    end
  end

  defp verify_tarball(path, strict?) do
    Mix.shell().info("Verifying #{path}...")

    case :erl_tar.extract(String.to_charlist(path), [:compressed, :memory]) do
      {:ok, entries} ->
        proof_entries =
          Enum.filter(entries, fn {name, _bytes} ->
            name
            |> to_string()
            |> String.ends_with?(".cureproof")
          end)

        if proof_entries == [] do
          handle_missing(strict?, path)
        else
          Enum.each(proof_entries, fn {name, bytes} ->
            label = to_string(name)
            verify_bytes(bytes, label)
          end)
        end

      {:error, reason} ->
        Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason)))

        exit({:shutdown, 1})
    end
  end

  defp verify_directory(dir, strict?) do
    proof_files = Path.wildcard(Path.join(dir, "**/*.cureproof"))

    if proof_files == [] do
      handle_missing(strict?, dir)
    else
      Enum.each(proof_files, fn file ->
        Mix.shell().info("Verifying #{file}...")
        bytes = File.read!(file)
        verify_bytes(bytes, file)
      end)
    end
  end

  defp verify_bytes(bytes, label) do
    case Cure.Project.Proof.deserialize(bytes) do
      {:ok, certs} ->
        run_verification(certs, label)

      {:error, :E067} ->
        Mix.shell().error(
          render_diagnostic(
            Cure.Diagnostic.Operational.proof_schema_incompatible(
              "#{label}: update Cure or ask the publisher to re-publish"
            )
          )
        )

        exit({:shutdown, 1})

      {:error, :corrupt} ->
        Mix.shell().error(
          render_diagnostic(
            Cure.Diagnostic.Operational.proof_verification_failed("#{label}: proof file is corrupt or truncated")
          )
        )

        exit({:shutdown, 1})
    end
  end

  defp run_verification(certs, label) do
    Mix.shell().info("  #{label}: #{length(certs)} certificate(s) found")

    case Cure.Project.Proof.verify(certs) do
      {:ok, count} ->
        Mix.shell().info("  #{label}: all #{count} certificate(s) verified")

      {:error, failures} ->
        Mix.shell().error(
          render_diagnostic(
            Cure.Diagnostic.Operational.proof_verification_failed("#{label}: #{length(failures)} certificate(s) failed")
          )
        )

        Enum.each(failures, fn {mod, _statement, reason} ->
          Mix.shell().error(
            render_diagnostic(
              Cure.Diagnostic.Operational.proof_verification_failed(
                "#{label}: certificate from #{mod} failed: #{verification_reason(reason)}"
              )
            )
          )
        end)

        exit({:shutdown, 1})
    end
  end

  defp handle_missing(true, label) do
    Mix.shell().error(
      render_diagnostic(Cure.Diagnostic.Operational.artifact_error("no .cureproof artifact found in #{label} (E065)"))
    )

    exit({:shutdown, 1})
  end

  defp handle_missing(false, label) do
    Mix.shell().info("cure.verify: no .cureproof artifact found in #{label} (use --strict to treat as error)")
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.usage(message)))
    exit({:shutdown, 1})
  end

  defp verification_reason(reason) when is_binary(reason), do: reason
  defp verification_reason(reason) when is_atom(reason), do: reason |> Atom.to_string() |> String.replace("_", " ")
  defp verification_reason(%{__exception__: true} = reason), do: Exception.message(reason)
  defp verification_reason(_reason), do: "the certificate witness was rejected"
end
