defmodule Cure.Compiler.BeamWriter do
  @moduledoc """
  Compiles Erlang abstract forms to BEAM bytecode and writes `.beam` files.

  Wraps `:compile.forms/2` with structured error handling and pipeline
  event emission.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:codegen, :beam_written, module, meta}` -- after `.beam` file is written
  - `{:codegen, :error, error, meta}` -- on compilation or write errors
  """

  alias Cure.Pipeline.Events

  @doc """
  Compile Erlang abstract forms into BEAM bytecode.

  Returns `{:ok, module, binary, warnings}` on success,
  `{:error, errors, warnings}` on failure.
  """
  @spec compile_forms(list(), keyword()) ::
          {:ok, module(), binary(), list()} | {:error, list(), list()}
  def compile_forms(forms, opts \\ []) do
    compile_opts = [:return_errors, :return_warnings | Keyword.get(opts, :compile_opts, [])]

    case :compile.forms(forms, compile_opts) do
      {:ok, module, binary} ->
        {:ok, module, binary, []}

      {:ok, module, binary, warnings} ->
        {:ok, module, binary, warnings}

      {:error, errors, warnings} ->
        {:error, errors, warnings}

      :error ->
        {:error, [{:unknown_compilation_error, forms}], []}
    end
  end

  @doc """
  Convert warnings from `:compile.forms/2` into the public compiler-warning
  schema consumed by diagnostic sinks.

  BEAM compilation operates on generated forms and commonly reports the
  synthetic filename `nofile`. The authored Cure path is therefore retained
  as the honest source boundary.
  """
  @spec normalize_warnings(list(), String.t()) :: [
          %{file: String.t(), line: pos_integer(), message: String.t()}
        ]
  def normalize_warnings(warnings, source_file) when is_list(warnings) and is_binary(source_file) do
    Enum.flat_map(warnings, fn
      {_generated_file, entries} when is_list(entries) ->
        Enum.map(entries, &normalize_warning(&1, source_file))

      entry ->
        [normalize_warning(entry, source_file)]
    end)
  end

  defp normalize_warning({location, formatter, detail}, source_file) when is_atom(formatter) do
    %{
      file: source_file,
      line: warning_line(location),
      message: format_warning(formatter, detail)
    }
  end

  defp normalize_warning(_unknown, source_file) do
    %{
      file: source_file,
      line: 1,
      message: "The BEAM compiler reported an unclassified warning while validating generated code."
    }
  end

  defp warning_line({line, _column}) when is_integer(line) and line > 0, do: line
  defp warning_line(line) when is_integer(line) and line > 0, do: line
  defp warning_line(_location), do: 1

  defp format_warning(formatter, detail) do
    formatter.format_error(detail)
    |> IO.iodata_to_binary()
  rescue
    _ -> "The BEAM compiler reported a warning while validating generated code."
  end

  @doc """
  Write a compiled BEAM binary to disk.

  Creates the output directory if it does not exist. Emits a
  `:codegen, :beam_written` event on success.
  """
  @spec write_beam(module(), binary(), String.t(), keyword()) :: :ok | {:error, term()}
  def write_beam(module, binary, output_dir, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    File.mkdir_p!(output_dir)
    beam_path = Path.join(output_dir, "#{beam_basename(module)}.beam")

    case File.write(beam_path, binary) do
      :ok ->
        if emit? do
          Events.emit(:codegen, :beam_written, module, Events.meta(file, 1))
        end

        :ok

      {:error, reason} ->
        if emit? do
          Events.emit(:codegen, :error, {:write_failed, beam_path, reason}, Events.meta(file, 1))
        end

        {:error, {:write_failed, beam_path, reason}}
    end
  end

  @doc """
  Compile forms and load the resulting module into the VM without writing to disk.

  Useful for testing and REPL scenarios.
  """
  @spec compile_and_load(list()) :: {:ok, module()} | {:error, term()}
  def compile_and_load(forms) do
    case compile_forms(forms) do
      {:ok, module, binary, _warnings} ->
        with :ok <- verify_cure_binary(module, binary) do
          case :code.load_binary(module, ~c"nofile", binary) do
            {:module, ^module} -> {:ok, module}
            {:error, reason} -> {:error, {:load_failed, reason}}
          end
        end

      {:error, errors, _warnings} ->
        {:error, {:compilation_failed, errors}}
    end
  end

  defp verify_cure_binary(module, binary) do
    if String.starts_with?(Atom.to_string(module), "Cure.") do
      Cure.Compiler.Artifacts.verify_binary(binary, module)
    else
      :ok
    end
  end

  defp beam_basename(module) when is_atom(module) do
    module
    |> Atom.to_string()
    |> String.replace_prefix("Elixir.", "")
  end
end
