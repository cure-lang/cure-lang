defmodule Cure.Cover do
  @compile {:no_warn_undefined, :cover}
  @moduledoc """
  Test coverage reporting for Cure projects (v0.23.0).

  Powers `cure test --cover`. Instruments every compiled module under
  `_build/cure/ebin/` via OTP's `:cover`, runs the test suite with the
  instrumented beams, and emits an HTML report under
  `_build/cure/cover/` plus a plain-text summary.

  The implementation is intentionally small: `:cover` does all the
  heavy lifting. We only own the beam discovery, the per-module HTML
  rendering, and the index page.
  """

  @type result :: %{
          module: module(),
          coverage: float(),
          lines_covered: non_neg_integer(),
          lines_total: non_neg_integer()
        }

  # -- Public API -------------------------------------------------------------

  @doc """
  Start `:cover` and compile every beam under `ebin_dir` (default
  `_build/cure/ebin`) for coverage analysis.
  """
  @spec start(String.t()) :: :ok
  def start(ebin_dir \\ "_build/cure/ebin") do
    ensure_cover_started()
    _ = :cover.reset()

    case Cure.Compiler.Artifacts.open_verified_set(ebin_dir) do
      {:ok, set} ->
        set.modules
        |> Map.values()
        |> Enum.flat_map(&Map.fetch!(&1, :artifacts))
        |> Enum.each(fn artifact ->
          beam = Path.join(set.artifact_root, artifact.path)
          _ = :cover.compile_beam(String.to_charlist(beam))
        end)

        :ok

      {:error, reason} ->
        raise ArgumentError, "cannot instrument an unverified Cure artifact set: #{inspect(reason)}"
    end
  end

  @doc """
  Collect coverage results for every compiled module.
  """
  @spec collect() :: [result()]
  def collect do
    modules = :cover.modules()

    Enum.map(modules, fn m ->
      case :cover.analyse(m, :coverage, :module) do
        {:ok, {_, {covered, not_covered}}} ->
          total = covered + not_covered
          pct = if total == 0, do: 100.0, else: covered * 100.0 / total

          %{module: m, coverage: Float.round(pct, 1), lines_covered: covered, lines_total: total}

        _ ->
          %{module: m, coverage: 0.0, lines_covered: 0, lines_total: 0}
      end
    end)
  end

  @doc """
  Write an HTML report to `output_dir` (default `_build/cure/cover`).
  Includes a per-module page via `:cover.analyse_to_file/2`.
  """
  @spec report([result()], String.t()) :: :ok
  def report(results, output_dir \\ "_build/cure/cover") do
    File.mkdir_p!(output_dir)

    Enum.each(results, fn %{module: m} ->
      out = Path.join(output_dir, "#{m}.html") |> String.to_charlist()
      _ = :cover.analyse_to_file(m, out, [:html])
    end)

    index = render_index(results)
    File.write!(Path.join(output_dir, "index.html"), index)
    :ok
  end

  @doc """
  Print a compact text summary to `io`. Returns the totals.
  """
  @spec summary([result()], IO.device()) :: %{lines_covered: non_neg_integer(), lines_total: non_neg_integer()}
  def summary(results, io \\ :stdio) do
    totals =
      Enum.reduce(results, %{covered: 0, total: 0}, fn %{lines_covered: c, lines_total: t}, acc ->
        %{covered: acc.covered + c, total: acc.total + t}
      end)

    IO.puts(io, "Coverage summary")
    IO.puts(io, String.duplicate("=", 40))

    results
    |> Enum.sort_by(& &1.coverage)
    |> Enum.each(fn r ->
      IO.puts(io, "#{pct(r.coverage)}  #{r.module}  (#{r.lines_covered}/#{r.lines_total})")
    end)

    overall = if totals.total == 0, do: 100.0, else: totals.covered * 100.0 / totals.total
    IO.puts(io, String.duplicate("-", 40))
    IO.puts(io, "total: #{Float.round(overall, 1)}% (#{totals.covered}/#{totals.total})")

    %{lines_covered: totals.covered, lines_total: totals.total}
  end

  # -- Internals --------------------------------------------------------------

  defp ensure_cover_started do
    case :cover.start() do
      {:ok, _} -> :ok
      {:error, {:already_started, _}} -> :ok
      _ -> :ok
    end
  end

  defp render_index(results) do
    rows =
      results
      |> Enum.sort_by(& &1.module)
      |> Enum.map_join("\n", fn r ->
        ~s|<tr><td><a href="#{r.module}.html">#{r.module}</a></td><td>#{pct(r.coverage)}</td><td>#{r.lines_covered}/#{r.lines_total}</td></tr>|
      end)

    """
    <!DOCTYPE html>
    <html><head><meta charset="utf-8"><title>Cure coverage</title>
    <style>
    body { font-family: system-ui, sans-serif; margin: 2em; }
    table { border-collapse: collapse; }
    th, td { border: 1px solid #ccc; padding: 0.4em 0.8em; }
    th { background: #f0f0f0; }
    </style>
    </head><body>
    <h1>Cure coverage report</h1>
    <table>
      <tr><th>Module</th><th>Coverage</th><th>Lines</th></tr>
      #{rows}
    </table>
    </body></html>
    """
  end

  defp pct(f), do: "#{Float.round(f * 1.0, 1)}%"
end
