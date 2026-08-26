defmodule Cure.Doc.Doctests do
  @moduledoc """
  Doctest harvester and runner for Cure.

  Any `## ` doc-comment block immediately above a function whose body
  contains `cure>` / `=>` pairs is treated as a doctest.

  ## Format

  ```
  ## Sums two integers.
  ##
  ##   cure> Demo.add(2, 3)
  ##   => 5
  ##
  ##   cure> Demo.add(0, 0)
  ##   => 0
  fn add(a: Int, b: Int) -> Int = a + b
  ```

  Each `cure> EXPR` line followed by an `=> EXPECTED` line becomes a
  test case. The expression is wrapped in a synthetic module, compiled,
  evaluated, and compared (via `inspect/1`) to the expected value.

  ## Public API

  - `extract/1` -- parse a `.cure` file and return the harvested cases.
  - `run_one/2` -- run a single case and return `:ok` or a structured diagnostic.
  """

  @type test_case :: %{name: String.t(), expr: String.t(), expected: String.t()}

  @doc """
  Extract every doctest case from the given file.
  """
  @spec extract(String.t()) :: [test_case()]
  def extract(path) do
    case File.read(path) do
      {:ok, content} -> extract_from_source(content)
      _ -> []
    end
  end

  @doc """
  Extract doctests from raw source text (used by tests).
  """
  @spec extract_from_source(String.t()) :: [test_case()]
  def extract_from_source(source) do
    source
    |> String.split("\n")
    |> harvest([], nil, [])
  end

  defp harvest([], cases, _ctx, _block), do: Enum.reverse(cases)

  defp harvest([line | rest], cases, ctx, block) do
    trimmed = String.trim(line)

    cond do
      String.starts_with?(trimmed, "##") ->
        body = trimmed |> String.replace_prefix("##", "") |> String.trim()
        harvest(rest, cases, ctx, block ++ [body])

      String.starts_with?(trimmed, "fn ") ->
        name = parse_fn_name(trimmed)
        new_cases = extract_pairs(block, name)
        harvest(rest, Enum.reverse(new_cases) ++ cases, name, [])

      trimmed == "" ->
        harvest(rest, cases, ctx, block)

      true ->
        harvest(rest, cases, ctx, [])
    end
  end

  defp parse_fn_name(line) do
    case Regex.run(~r/fn\s+([a-z_][a-zA-Z0-9_]*)/, line) do
      [_, n] -> n
      _ -> "unknown"
    end
  end

  defp extract_pairs(block, fn_name) do
    block
    |> Enum.with_index()
    |> Enum.filter(fn {l, _i} -> String.starts_with?(l, "cure>") end)
    |> Enum.map(fn {l, i} ->
      expr = l |> String.replace_prefix("cure>", "") |> String.trim()

      expected =
        case Enum.at(block, i + 1) do
          nil ->
            ""

          next ->
            cond do
              String.starts_with?(next, "=>") ->
                next |> String.replace_prefix("=>", "") |> String.trim()

              true ->
                ""
            end
        end

      %{name: "#{fn_name}_#{i}", expr: expr, expected: expected}
    end)
    |> Enum.reject(fn %{expected: e} -> e == "" end)
  end

  @doc """
  Run a single doctest case.

  Returns `:ok` if the expression's value matches the expected text via
  `inspect/1`. Failures retain a diagnostic and its source registry so callers
  can choose terminal, JSON, or editor presentation without parsing strings.
  """
  @spec run_one(String.t(), String.t(), String.t()) ::
          :ok
          | {:fail, Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t() | nil}
  def run_one(expr, expected, file \\ "doctest.cure") do
    mod = "Doctest_#{:erlang.unique_integer([:positive])}"

    source = """
    mod #{mod}
      fn main() = #{expr}
    """

    case Cure.Compiler.compile_and_load(source, file: file, emit_events: false) do
      {:ok, module} ->
        try do
          actual = inspect(module.main())

          if actual == expected do
            :ok
          else
            diagnostic =
              Cure.Diagnostic.Operational.command_failure(
                "doctest",
                "expected #{expected}, got #{actual}"
              )

            {:fail, diagnostic, nil}
          end
        catch
          kind, reason ->
            {diagnostic, registry} =
              Cure.Diagnostic.Host.to_diagnostic(
                {:command_failed, "doctest", {kind, reason}},
                file,
                source
              )

            {:fail, diagnostic, registry}
        end

      {:error, reason} ->
        {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)
        {:fail, diagnostic, registry}
    end
  end
end
