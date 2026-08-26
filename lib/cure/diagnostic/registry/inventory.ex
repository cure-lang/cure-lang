defmodule Cure.Diagnostic.Registry.Inventory do
  @moduledoc """
  Read-only inventory of deliberate diagnostic boundaries and host presentation sites.

  The inventory is intentionally source-oriented: it makes new error constructors,
  raises, formatters, and direct output sites visible to the registry gate without
  pretending that a regular expression can infer their semantic ownership.
  """

  @type site :: %{path: Path.t(), line: pos_integer(), text: String.t()}

  @spec scan([Path.t()]) :: %{
          error_constructors: [site()],
          deliberate_raises: [site()],
          formatter_consumers: [site()],
          stderr_sites: [site()]
        }
  def scan(paths \\ default_paths()) when is_list(paths) do
    sites = Enum.flat_map(paths, &scan_file/1)

    %{
      error_constructors: Enum.filter(sites, &match_site?(&1, ~r/\{:error\s*,/)),
      deliberate_raises: Enum.filter(sites, &match_site?(&1, ~r/\braise\b/)),
      formatter_consumers: Enum.filter(sites, &match_site?(&1, ~r/format_error|format_with_source|Renderer\./)),
      stderr_sites: Enum.filter(sites, &match_site?(&1, ~r/IO\.(puts|write)|Mix\.shell\(\)\.(error|info)/))
    }
  end

  @spec default_paths() :: [Path.t()]
  def default_paths do
    Path.wildcard("lib/**/*.ex") ++ Path.wildcard("site/lib/**/*.ex")
  end

  @doc "Validate inventory invariants required by the shared output boundary."
  @spec validate(map()) :: :ok | {:error, term()}
  def validate(inventory) when is_map(inventory) do
    direct_renderer_sites =
      Enum.filter(inventory.formatter_consumers, fn %{text: text, path: path} ->
        String.contains?(text, "Renderer.plain") and
          path not in ["lib/cure/diagnostic/sink.ex", "lib/cure/diagnostic/registry/inventory.ex"]
      end)

    legacy_formatter_sites =
      Enum.filter(inventory.formatter_consumers, fn %{text: text, path: path} ->
        (String.contains?(text, "Cure.Compiler.Errors.format_error(") or
           String.contains?(text, "Cure.Compiler.Errors.format_with_source(")) and
          path not in [
            "lib/cure/compiler/errors.ex",
            "lib/cure/diagnostic/registry/inventory.ex"
          ]
      end)

    cond do
      direct_renderer_sites != [] -> {:error, {:direct_renderer_bypass, direct_renderer_sites}}
      legacy_formatter_sites != [] -> {:error, {:legacy_formatter_path, legacy_formatter_sites}}
      true -> :ok
    end
  end

  defp scan_file(path) do
    case File.read(path) do
      {:ok, source} ->
        source
        |> String.split("\n")
        |> Enum.with_index(1)
        |> Enum.map(fn {text, line} -> %{path: path, line: line, text: text} end)

      {:error, _reason} ->
        []
    end
  end

  defp match_site?(%{text: text}, pattern), do: Regex.match?(pattern, text)
end
