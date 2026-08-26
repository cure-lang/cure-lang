defmodule Mix.Tasks.Cure.Check.Docs do
  @moduledoc """
  Compile every `cure` fenced code block in tracked Markdown documents and
  `.cure` docstrings.

      mix cure.check.docs

  Snippets may be complete modules, declarations, or expressions. Add `expr`
  or `declarations` to a fence's info string when automatic classification is
  ambiguous:

      ```cure expr
      map([1, 2], fn x -> x + 1)
      ```

  Use the expected diagnostic code for an intentionally rejected example, such
  as `cure E093`. It passes only when the compiler returns that exact code; a
  different error, compiler crash, or unexpected successful compilation fails
  the check.

  A `W` code, such as `cure W000`, documents a snippet that compiles but cannot
  be written warning-free — the macro expanders that emit modules are the usual
  case. It passes only when compilation succeeds *and* emits that warning, so
  the warning stays part of the documented behaviour instead of being waived.
  An untagged fence must still compile with no warnings at all.

  Note that every warning the BEAM linter raises is reported as `W000`, so a
  `W000` tag pins *that a warning happens*, not which one. It cannot yet
  distinguish `behaviour none undefined` from an unrelated new warning in the
  same snippet.

  There is deliberately no way to opt a `cure` fence out of checking. An
  incomplete design sketch is not Cure source; give it a plain `text` fence and
  it is never extracted in the first place.

  The declaration-only support surface in `priv/doc_snippets/support.cure` is
  appended to synthetic modules. It is intentionally small: documentation
  should use real standard-library imports for public APIs.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}
  alias Cure.Doc.Snippets

  @shortdoc "Compile every Cure code fence in repository documentation"
  @support_path "priv/doc_snippets/support.cure"

  @impl Mix.Task
  def run(args) do
    verbose? = parse_args!(args)

    Application.ensure_all_started(:cure)
    support = File.read!(@support_path)

    root = File.cwd!()
    # Compile snippets in the same environment as a project build.  The
    # resolver consults CURE_LIB for `use Std.*` modules; without it every
    # standard-library docstring is reported as a missing module even when the
    # preloaded BEAM is present.
    stdlib_source = Path.expand("lib/std", root)

    stdlib_ebin =
      case Application.get_env(:cure, :stdlib_beam_dir) do
        dir when is_binary(dir) -> Path.expand(dir, root)
        _ -> Path.expand("_build/cure/ebin", root)
      end

    System.put_env("CURE_LIB", stdlib_ebin)
    Application.put_env(:cure, :stdlib_source_dir, stdlib_source)
    Application.put_env(:cure, :stdlib_beam_dir, stdlib_ebin)

    if File.dir?(stdlib_source) do
      Cure.Stdlib.Preload.preload(kind: :all, stdlib_ebin: stdlib_ebin, source_jit: false)
    end

    snippets =
      Enum.flat_map(Snippets.markdown_files(root), &extract_markdown/1) ++
        Enum.flat_map(Snippets.cure_files(root), &extract_cure/1)

    results = Enum.map(snippets, &check(&1, support, stdlib_source, stdlib_ebin, verbose?))
    passed = Enum.count(results, &(&1 == :pass))
    failed = Enum.count(results, &(&1 == :fail))

    IO.puts("\ndoc snippets: #{passed} passed, #{failed} failed")

    if failed > 0 do
      exit({:shutdown, 1})
    end
  end

  defp extract_markdown(path) do
    case Snippets.extract_file(path) do
      {:ok, found} -> found
      {:error, reason} -> Mix.raise("cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp extract_cure(path) do
    case Snippets.extract_cure_file(path) do
      {:ok, found} -> found
      {:error, reason} -> Mix.raise("cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp check(snippet, support, stdlib_source, stdlib_ebin, verbose?) do
    label = relative_label(snippet)
    source = Snippets.source(snippet, support)

    case Snippets.expected_diagnostic(snippet) do
      {:error, codes} ->
        IO.puts("  FAIL #{label} (multiple expected error codes: #{Enum.join(codes, ", ")})")
        :fail

      expected ->
        compile_and_classify(
          snippet,
          support,
          stdlib_source,
          stdlib_ebin,
          source,
          label,
          expected,
          verbose?
        )
    end
  end

  defp compile_and_classify(
         snippet,
         support,
         stdlib_source,
         stdlib_ebin,
         source,
         label,
         expected,
         verbose?
       ) do
    try do
      case Snippets.compile(snippet,
             support: support,
             source_roots: [Path.expand("lib", File.cwd!()), stdlib_source],
             stdlib_ebin: stdlib_ebin
           ) do
        {:ok, _module, []} when expected != nil ->
          {:ok, code} = expected
          IO.puts("  FAIL #{label} (#{unmet_expectation(code)})")
          :fail

        {:ok, _module, []} ->
          if verbose?, do: IO.puts("  ok  #{label}")
          :pass

        {:ok, _module, warnings} when warnings != [] ->
          classify_warnings(warnings, snippet.path, source, label, expected, verbose?)

        {:error, reason} ->
          classify_error(reason, snippet.path, source, label, expected, verbose?)
      end
    rescue
      error ->
        IO.puts("  FAIL #{label} (compiler crashed)")
        Mix.shell().error(Exception.format(:error, error, __STACKTRACE__))
        :fail
    catch
      kind, reason ->
        IO.puts("  FAIL #{label} (compiler #{kind})")
        Mix.shell().error(Exception.format(kind, reason, __STACKTRACE__))
        :fail
    end
  end

  # A warning-tagged fence documents a construct with no warning-free form, so
  # the warning is part of the claim: it must still be emitted, and it must be
  # the one the fence names.
  defp classify_warnings(warnings, path, source, label, expected, verbose?) do
    codes = Enum.map(warnings, &warning_code(&1, path, source))

    case expected do
      {:ok, code} ->
        if code in codes do
          if verbose?, do: IO.puts("  ok  #{label} (#{code} as documented)")
          :pass
        else
          IO.puts("  FAIL #{label} (expected #{code}, got #{codes |> Enum.uniq() |> Enum.join(", ")})")
          report_warnings(warnings, path, source)
          :fail
        end

      nil ->
        IO.puts("  FAIL #{label} (#{length(warnings)} warning(s))")
        report_warnings(warnings, path, source)
        :fail
    end
  end

  defp warning_code(warning, path, source) do
    {diagnostic, _registry} = Host.to_diagnostic({:compiler_warning, warning}, path, source)
    diagnostic.code
  end

  defp report_warnings(warnings, path, source) do
    Enum.each(warnings, fn warning ->
      Mix.shell().error(render({:compiler_warning, warning}, path, source))
    end)
  end

  defp unmet_expectation("W" <> _ = code), do: "expected #{code} but compiled without warnings"
  defp unmet_expectation(code), do: "expected #{code} but compiled"

  defp classify_error(reason, path, source, label, {:ok, expected}, verbose?) do
    {diagnostic, _registry} = Host.to_diagnostic(reason, path, source)

    if diagnostic.code == expected do
      if verbose?, do: IO.puts("  ok  #{label} (#{expected} as documented)")
      :pass
    else
      IO.puts("  FAIL #{label} (expected #{expected}, got #{diagnostic.code})")
      Mix.shell().error(render(reason, path, source))
      :fail
    end
  end

  defp classify_error(reason, path, source, label, nil, _verbose?) do
    IO.puts("  FAIL #{label}")
    Mix.shell().error(render(reason, path, source))
    :fail
  end

  defp parse_args!([]), do: false
  defp parse_args!(["--verbose"]), do: true
  defp parse_args!(_), do: usage_error("Usage: mix cure.check.docs [--verbose]")

  defp relative_label(snippet) do
    path = Path.relative_to_cwd(snippet.path)
    "#{path}:#{snippet.line}"
  end

  defp render(reason, path, source) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path, source)

    Sink.new(format: :plain, color: :auto, width: 100, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
    |> Mix.shell().error()

    exit({:shutdown, 1})
  end
end
