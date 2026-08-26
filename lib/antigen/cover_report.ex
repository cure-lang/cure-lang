defmodule Antigen.CoverReport do
  @moduledoc """
  Renders a deterministic kernel-coverage report from `Antigen.Cover` data:
  a per-module summary table + cold lines grouped by enclosing function
  (`function_index/1`, via `:beam_lib` abstract code).
  """

  @doc """
  Maps each source line of `module` to its enclosing `{name, arity}`, from the
  module's abstract code. Keys are PLAIN INTEGER lines (via `:erl_anno.line/1`
  normalization) so they align with `:cover.analyse`'s integer line keys — the
  raw abstract-code annotation is `{Line, Column}` on current OTP, not a bare
  integer.
  """
  @spec function_index(module()) :: %{integer() => {atom(), arity()}}
  def function_index(module) do
    module
    |> abstract_forms()
    |> Enum.reduce(%{}, fn
      {:function, _anno, name, arity, _clauses} = form, idx ->
        form
        |> collect_lines(MapSet.new())
        |> Enum.reduce(idx, fn line, i -> Map.put_new(i, line, {name, arity}) end)

      _other, idx ->
        idx
    end)
  end

  @doc "Deterministic markdown report: summary table + cold lines by function."
  @spec render(%{module() => map()}, %{module() => map()}) :: String.t()
  def render(coverage_map, fn_indexes) do
    modules = coverage_map |> Map.keys() |> Enum.sort()
    render_summary(modules, coverage_map) <> "\n" <> render_cold(modules, coverage_map, fn_indexes)
  end

  # -- report sections --------------------------------------------------------

  defp render_summary(modules, covmap) do
    header = "# Kernel Coverage\n\n| Module | Covered | Total | % |\n|---|---:|---:|---:|\n"

    rows =
      Enum.map(modules, fn m ->
        %{covered: cov, total: total} = covmap[m]
        pct = if total > 0, do: Float.round(length(cov) * 100 / total, 1), else: 0.0
        "| #{inspect(m)} | #{length(cov)} | #{total} | #{pct} |\n"
      end)

    header <> Enum.join(rows)
  end

  defp render_cold(modules, covmap, fn_indexes) do
    sections =
      Enum.map(modules, fn m ->
        idx = Map.get(fn_indexes, m, %{})

        groups =
          covmap[m].cold
          |> Enum.group_by(fn line -> Map.get(idx, line, :"module-level") end)
          |> Enum.sort_by(fn {fa, _lines} -> fa_label(fa) end)

        lines =
          Enum.map(groups, fn {fa, ls} ->
            "  - #{fa_label(fa)}: #{ls |> Enum.sort() |> Enum.join(", ")}\n"
          end)

        "## #{inspect(m)} cold lines\n\n" <> Enum.join(lines)
      end)

    "## Cold lines\n\n" <> Enum.join(sections, "\n")
  end

  defp fa_label({name, arity}), do: "#{name}/#{arity}"
  defp fa_label(:"module-level"), do: "module-level"

  # -- abstract-code walk -----------------------------------------------------

  defp abstract_forms(module) do
    beam = :code.which(module)

    {:ok, {^module, [{:abstract_code, {:raw_abstract_v1, forms}}]}} =
      :beam_lib.chunks(beam, [:abstract_code])

    forms
  end

  # Collect every line number annotated anywhere under an AST node.
  defp collect_lines(t, acc) when is_tuple(t) do
    acc =
      if tuple_size(t) >= 2 and is_atom(elem(t, 0)) do
        case anno_line(elem(t, 1)) do
          nil -> acc
          line -> MapSet.put(acc, line)
        end
      else
        acc
      end

    t |> Tuple.to_list() |> Enum.reduce(acc, &collect_lines/2)
  end

  defp collect_lines(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_lines/2)
  defp collect_lines(_other, acc), do: acc

  # Normalize the three raw-abstract anno forms to a plain integer line.
  defp anno_line(a) when is_integer(a) and a > 0, do: a
  defp anno_line({l, c}) when is_integer(l) and is_integer(c), do: l

  defp anno_line(a) when is_list(a) do
    case :erl_anno.line(a) do
      line when is_integer(line) and line > 0 -> line
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp anno_line(_other), do: nil
end
