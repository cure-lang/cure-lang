defmodule Mix.Tasks.Cure.Check.Examples do
  @moduledoc """
  Regression task: compiles every supported `.cure` file under `examples/` and runs
  the ones with a `fn main/0`, comparing output against expectations.

  Invoke as:

      mix cure.check.examples

  Every fixture is declared in the manifest below. When a new example is
  added, add an entry keyed by the example's basename (without the `.cure`
  suffix). The `expect` value is one of:

  - `:compile_only` -- the file must compile; its `main/0` (if any) is
    not executed.
  - a string -- `main/0` is executed and its `inspect/1` output must
    match exactly.

  ## Exit code

  Unclassified fixtures and stale manifest entries are errors, as is any
  unexpected compilation, execution, or output failure.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}

  @shortdoc "Compile and run every .cure example and check their output"

  @examples_dir "examples"

  @expected %{
    "adt" => "42",
    "adt_fn_payload" => :compile_only,
    "assert_type_demo" => "42",
    "binary_comprehension" => :compile_only,
    "binary_destructuring" => :compile_only,
    "defaults" => :compile_only,
    "dependent_types" => "6",
    "derived_show" => "1",
    "destructuring" => "0",
    "doctest_demo" => "25",
    "fenced_docs" => "240",
    "ffi" => "42",
    "fsm_pipeline" => :compile_only,
    "hello" => "42",
    "holes_demo" => "0",
    # Two things moved since this said `~c"{}"`. `@derive(ToJSON)` now builds the
    # structured `Value.Object` its docstring describes instead of an empty one,
    # and `String` became nominal — so `main()` returns the derived object inside
    # the `{String, code_points}` constructor rather than a bare charlist.
    "json_derive" => ~S({:String, ~c"{\"name\":\"Ada\",\"age\":36}"}),
    "json_tree" => "48",
    "lambda_block" => "54",
    "lazy_iter" => "55",
    "length_indexed" => "{:succ_len, {:succ_len, :zero_len}}",
    "let_destructuring" => "22",
    "list_basics" => "15",
    "match_showcase" => "200",
    "math" => :compile_only,
    "multi_head_cons" => "6",
    "multi_line_adt" => :compile_only,
    "mutual_recursion" => "1",
    "pattern_guards" => "0",
    "proof_laws" => :compile_only,
    "property_test" => ":ok",
    "protocols" => "0",
    "records" => "2",
    "recursion" => "3628800",
    "result_handling" => "0",
    "sigma_pairs" => :compile_only,
    "sigma_vector" => "5",
    "test_showcase" => ":ok",
    "totality" => "120",
    "totality_enforcement" => "142",
    "traffic_light" => :compile_only
  }

  @impl Mix.Task
  def run(args) do
    if args != [] do
      usage_error("Usage: mix cure.check.examples")
    end

    # Make sure stdlib beams are on the path and loaded.
    Application.ensure_all_started(:cure)
    ensure_stdlib_compiled()
    preload_stdlib()

    files = Path.wildcard(Path.join(@examples_dir, "*.cure")) |> Enum.sort()
    validate_manifest!(files)
    reject_emitter_owned_example_names!()

    results = Enum.map(files, &run_one/1)

    passed = Enum.count(results, &match?({:pass, _}, &1))
    failed = Enum.filter(results, &match?({:fail, _}, &1))

    if failed == [] do
      IO.puts("\nexamples: #{passed} passed, 0 skipped, 0 failed")
      :ok
    else
      IO.puts("\nexamples: #{passed} passed, #{length(failed)} failed")

      exit({:shutdown, 1})
    end
  end

  # -- Per-file logic ---------------------------------------------------------

  defp run_one(path) do
    name = Path.basename(path, ".cure")

    # Temporary directories used by the task's diagnostic tests deliberately
    # contain synthetic fixtures. The real repository is made exhaustive by
    # `validate_manifest!/1`; outside it, an unknown fixture is compile-only.
    expected = Map.get(@expected, name, :compile_only)

    case {expected, main_fn?(path)} do
      {:compile_only, _} -> compile_only(name, path)
      {_, false} -> compile_only(name, path)
      {val, true} when is_binary(val) -> run_and_compare(name, path, val)
    end
  end

  defp compile_only(name, path) do
    case normalized_source(path) do
      {:ok, source} ->
        case Cure.Compiler.compile_and_load(source,
               file: path,
               output_dir: "_build/cure/ex_ebin",
               emit_events: false
             ) do
          {:ok, _module} ->
            IO.puts("  ok  #{pad(name)} (compile)")
            {:pass, name}

          {:error, reason} ->
            IO.puts("  FAIL #{pad(name)} compilation failed")
            emit_host_diagnostic(reason, path, source)
            {:fail, name}
        end

      {:error, reason} ->
        IO.puts("  FAIL #{pad(name)} could not read source")
        emit_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason))
        {:fail, name}
    end
  end

  defp run_and_compare(name, path, expected) do
    case File.read(path) do
      {:ok, src} ->
        {src, _legacy_otp_changed?} = Cure.Migrate.LegacyOtp.normalize(src)

        case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
          {:ok, module} ->
            try do
              actual = inspect(module.main())

              if actual == expected do
                IO.puts("  ok  #{pad(name)} => #{actual}")
                {:pass, name}
              else
                msg = "expected #{expected}, got #{actual}"
                IO.puts("  FAIL #{pad(name)} output differed")
                emit_diagnostic(Cure.Diagnostic.Operational.command_failure("example #{name}", msg))
                {:fail, name}
              end
            catch
              kind, reason ->
                IO.puts("  FAIL #{pad(name)} execution failed")

                emit_diagnostic(
                  Cure.Diagnostic.Operational.command_failure(
                    "example #{name}",
                    Exception.format_banner(kind, reason)
                  )
                )

                {:fail, name}
            end

          {:error, reason} ->
            IO.puts("  FAIL #{pad(name)} compilation failed")
            emit_host_diagnostic(reason, path, src)
            {:fail, name}
        end

      {:error, reason} ->
        IO.puts("  FAIL #{pad(name)} could not read source")
        emit_diagnostic(Cure.Diagnostic.Operational.file_read(path, reason))
        {:fail, name}
    end
  end

  defp normalized_source(path) do
    with {:ok, source} <- File.read(path) do
      {source, _legacy_otp_changed?} = Cure.Migrate.LegacyOtp.normalize(source)
      {:ok, source}
    end
  end

  defp main_fn?(path) do
    case File.read(path) do
      {:ok, src} -> String.match?(src, ~r/\bfn\s+main\b/)
      _ -> false
    end
  end

  defp pad(name), do: String.pad_trailing(name, 26)

  defp validate_manifest!(files) do
    if File.exists?("mix.exs") do
      discovered = MapSet.new(files, &Path.basename(&1, ".cure"))
      declared = MapSet.new(Map.keys(@expected))
      new = MapSet.difference(discovered, declared)
      stale = MapSet.difference(declared, discovered)

      if MapSet.size(new) > 0 or MapSet.size(stale) > 0 do
        details =
          [
            if(MapSet.size(new) > 0, do: "unlisted: #{Enum.join(Enum.sort(new), ", ")}"),
            if(MapSet.size(stale) > 0, do: "stale: #{Enum.join(Enum.sort(stale), ", ")}")
          ]
          |> Enum.reject(&is_nil/1)
          |> Enum.join("; ")

        usage_error("Example manifest mismatch (#{details})")
      else
        :ok
      end
    else
      :ok
    end
  end

  # Lifted-module declarations are source names, not precomputed BEAM names.
  # A bare name is qualified by its lexical owner (`Main` at top level); an
  # authored `Cure.*` prefix bakes emitter policy back into the language and
  # recreates the pre-dependent global-namespace coupling.
  defp reject_emitter_owned_example_names! do
    offenders =
      (Path.wildcard(Path.join(@examples_dir, "**/*.cure")) ++
         Path.wildcard(Path.join(@examples_dir, "**/*.md")))
      |> Enum.uniq()
      |> Enum.flat_map(fn path ->
        path
        |> File.stream!()
        |> Stream.with_index(1)
        |> Enum.flat_map(fn {line, line_number} ->
          if Regex.match?(~r/^\s*(actor|fsm|sup|app|behavior)\s+Cure\./, line),
            do: ["#{path}:#{line_number}"],
            else: []
        end)
      end)

    if offenders == [] do
      :ok
    else
      usage_error(
        "Example declarations must use source-level names; remove authored Cure.* prefixes at " <>
          Enum.join(offenders, ", ")
      )
    end
  end

  defp emit_host_diagnostic(reason, path, source) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path, source)

    emit_diagnostic(diagnostic, registry)
  end

  defp emit_diagnostic(diagnostic, registry \\ nil) do
    rendered =
      Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
      |> Sink.render(diagnostic)

    Mix.shell().error(rendered)
  end

  defp usage_error(message) do
    emit_diagnostic(Cure.Diagnostic.Operational.usage(message))
    exit({:shutdown, 1})
  end

  # -- Stdlib preload ---------------------------------------------------------

  defp ensure_stdlib_compiled do
    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           package: "stdlib",
           kind: :stdlib,
           output_dir: "_build/cure/ebin",
           repair: false,
           verification: :cached
         ) do
      {:ok, _result} ->
        :ok

      {:error, _validation_reason} ->
        repair_stdlib()
    end
  end

  defp repair_stdlib do
    case Cure.Stdlib.Paths.source_dir() do
      nil ->
        emit_diagnostic(
          Cure.Diagnostic.Operational.command_failure(
            "compile standard library",
            "no standard-library source directory is available"
          )
        )

        exit({:shutdown, 1})

      source_root ->
        case Cure.Compiler.Artifacts.sweep(
               module_pipeline: :canonical,
               package: "stdlib",
               kind: :stdlib,
               source_roots: [source_root],
               output_dir: "_build/cure/ebin",
               repair: true,
               compile_opts: [emit_events: false]
             ) do
          {:ok, _result} ->
            :ok

          {:error, reason} ->
            emit_host_diagnostic(reason, source_root, "")
            exit({:shutdown, 1})
        end
    end
  end

  defp preload_stdlib do
    # Load only `Cure.*.beam` files by name (no `:code.add_patha`) so
    # stale lowercase artifacts under `_build/cure/ebin` cannot shadow
    # OTP modules like `:math` while the examples are being exercised.
    # Explicit `kind: :all` preserves the historical "load everything"
    # behaviour now that `Preload.preload/1` defaults to `:none`.
    Cure.Stdlib.Preload.preload(examples: true, kind: :all)
  end
end
