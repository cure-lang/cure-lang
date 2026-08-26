defmodule CureSpline do
  @moduledoc """
  Ergonomic Elixir API over a natural cubic spline implemented in Cure.

  The heavy lifting lives in `cure_src/spline.cure`, which compiles to the
  BEAM module `:"Cure.Spline"`. This module is a thin wrapper that:

    * accepts knot data as a plain list of `{x, y}` tuples,
    * converts to the map shape the Cure record produces,
    * unwraps `Result` tuples for functions that can fail,
    * exposes `demo/0`, which fits a spline to eleven samples of
      `sin(x)` over `[0, 2π]` and draws an ASCII plot of the result.

  ## Example

      iex> {:ok, spline} = CureSpline.fit([{0.0, 0.0}, {1.0, 1.0}, {2.0, 4.0}, {3.0, 9.0}])
      iex> {:ok, y} = CureSpline.evaluate(spline, 0.5)
      iex> y
      0.35

  `fit/1` returns `{:error, reason}` when fewer than two knots are supplied
  or the x coordinates are not strictly increasing.
  """

  @spline_module :"Cure.Spline"

  # The Cure-compiled module is loaded from `_build/cure/ebin/` at runtime,
  # long after the Elixir compiler has finished checking this file. Silence
  # the otherwise-correct "module not available" warnings.
  @compile {:no_warn_undefined, @spline_module}

  @typedoc "A control point passed to `fit/1`."
  @type knot :: {number(), number()}

  @typedoc "Opaque spline structure returned by `fit/1`."
  @type spline :: %{
          required(:__struct__) => :spline,
          required(:segments) => list(map()),
          required(:x_min) => float(),
          required(:x_max) => float()
        }

  # -- Fitting ----------------------------------------------------------------

  @doc """
  Fit a natural cubic spline through the supplied knots.

  Each knot is a `{x, y}` pair; x coordinates must be strictly increasing and
  there must be at least two knots.
  """
  @spec fit([knot()]) :: {:ok, spline()} | {:error, String.t()}
  def fit(knots) when is_list(knots) do
    knots
    |> Enum.map(&to_knot/1)
    |> @spline_module.fit()
  end

  # -- Evaluation -------------------------------------------------------------

  @doc """
  Evaluate the spline at `x`.

  Returns `{:error, _}` when `x` is outside the fitted domain.
  """
  @spec evaluate(spline(), number()) :: {:ok, float()} | {:error, String.t()}
  def evaluate(spline, x), do: @spline_module.evaluate(spline, x * 1.0)

  @doc """
  Evaluate the spline at `x`, clamping to the fitted domain.

  For `x < x_min` returns `S(x_min)`; for `x > x_max` returns `S(x_max)`.
  """
  @spec evaluate_clamped(spline(), number()) :: float()
  def evaluate_clamped(spline, x), do: @spline_module.evaluate_clamped(spline, x * 1.0)

  @doc "First derivative of the spline at `x`."
  @spec derivative(spline(), number()) :: {:ok, float()} | {:error, String.t()}
  def derivative(spline, x), do: @spline_module.derivative(spline, x * 1.0)

  @doc """
  Sample `n` evenly spaced points between `x_min` and `x_max`.

  Returns a list of `{x, y}` 2-tuples.
  """
  @spec sample(spline(), pos_integer()) :: [{float(), float()}]
  def sample(spline, n) when is_integer(n) and n >= 1,
    do: @spline_module.sample(spline, n)

  # -- Accessors --------------------------------------------------------------

  @doc "Number of cubic pieces (always `knots - 1`)."
  @spec n_segments(spline()) :: non_neg_integer()
  def n_segments(spline), do: @spline_module.n_segments(spline)

  @doc "Lower bound of the spline's domain."
  @spec x_min(spline()) :: float()
  def x_min(spline), do: @spline_module.x_min(spline)

  @doc "Upper bound of the spline's domain."
  @spec x_max(spline()) :: float()
  def x_max(spline), do: @spline_module.x_max(spline)

  # -- Demo -------------------------------------------------------------------

  @doc """
  Fit a natural cubic spline to eleven samples of `sin(x)` over `[0, 2π]`
  and print an ASCII plot. Returns the fitted spline.
  """
  @spec demo() :: spline()
  def demo do
    pi2 = 2.0 * :math.pi()
    knots = for i <- 0..10, do: {i * pi2 / 10.0, :math.sin(i * pi2 / 10.0)}

    {:ok, spline} = fit(knots)

    IO.puts("cure_spline demo: natural cubic spline through 11 samples of sin(x)")
    IO.puts("domain: [0.0, 2pi], segments: #{n_segments(spline)}")
    IO.puts("")

    samples = sample(spline, 61)
    IO.puts(ascii_plot(samples, knots))

    spline
  end

  # ASCII plot rendering helper --------------------------------------------

  @plot_rows 15

  defp ascii_plot(samples, knots) do
    xs = Enum.map(samples, &elem(&1, 0))
    ys = Enum.map(samples, &elem(&1, 1))
    y_min = Enum.min(ys)
    y_max = Enum.max(ys)
    y_span = max(y_max - y_min, 1.0e-12)

    width = length(samples)

    # Build a grid indexed by [row][col] where row 0 is the top.
    grid =
      for _row <- 0..(@plot_rows - 1) do
        for _col <- 0..(width - 1), do: " "
      end

    grid = draw_curve(grid, ys, y_min, y_span)
    grid = mark_knots(grid, xs, samples, knots, y_min, y_span)

    header = "     y=#{:erlang.float_to_binary(y_max, decimals: 2)}"

    body =
      grid
      |> Enum.map(fn row -> "    |" <> Enum.join(row, "") <> "|" end)
      |> Enum.join("\n")

    footer = "     y=#{:erlang.float_to_binary(y_min, decimals: 2)}"

    xaxis =
      "     x: #{:erlang.float_to_binary(List.first(xs), decimals: 2)} -> #{:erlang.float_to_binary(List.last(xs), decimals: 2)}"

    [header, body, footer, xaxis] |> Enum.join("\n")
  end

  defp draw_curve(grid, ys, y_min, y_span) do
    ys
    |> Enum.with_index()
    |> Enum.reduce(grid, fn {y, col}, acc ->
      row = row_of(y, y_min, y_span)
      set_cell(acc, row, col, "*")
    end)
  end

  defp mark_knots(grid, xs, samples, knots, y_min, y_span) do
    Enum.reduce(knots, grid, fn {kx, ky}, acc ->
      # find nearest sample column to knot x
      col = nearest_index(xs, kx)
      {_sx, sy} = Enum.at(samples, col)
      # use the knot's exact y for row placement to keep the marker visually true
      row = row_of(ky || sy, y_min, y_span)
      set_cell(acc, row, col, "o")
    end)
  end

  defp row_of(y, y_min, y_span) do
    # 0 is top row, @plot_rows-1 is bottom. Larger y -> smaller row index.
    frac = (y - y_min) / y_span
    # clamp
    frac = max(0.0, min(1.0, frac))
    max(0, min(@plot_rows - 1, round((1.0 - frac) * (@plot_rows - 1))))
  end

  defp nearest_index(xs, target) do
    xs
    |> Enum.with_index()
    |> Enum.min_by(fn {x, _i} -> abs(x - target) end)
    |> elem(1)
  end

  defp set_cell(grid, row, col, char) do
    List.update_at(grid, row, fn r -> List.replace_at(r, col, char) end)
  end

  # -- Internal ---------------------------------------------------------------

  defp to_knot({x, y}), do: {:Knot, x * 1.0, y * 1.0}
end
