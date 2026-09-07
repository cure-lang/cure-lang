defmodule CureSplineTest do
  use ExUnit.Case, async: true

  @moduledoc """
  Exercises the natural cubic spline implemented in Cure, both directly on
  the `:"Cure.Spline"` BEAM module and through the `CureSpline` wrapper.
  """

  @raw_module :"Cure.Spline"

  defp knot(x, y), do: {:Knot, x * 1.0, y * 1.0}

  # ===========================================================================
  # Cure module: error paths
  # ===========================================================================

  describe "Cure.Spline.fit/1 validation" do
    test "rejects empty knot list" do
      assert {:error, {:String, ~c"spline: empty knot list"}} = @raw_module.fit([])
    end

    test "rejects single knot" do
      assert {:error, {:String, ~c"spline: need at least two knots"}} =
               @raw_module.fit([knot(0.0, 1.0)])
    end

    test "rejects duplicate x coordinates" do
      assert {:error, {:String, ~c"spline: x values must be strictly increasing"}} =
               @raw_module.fit([knot(0.0, 0.0), knot(0.0, 1.0)])
    end

    test "rejects decreasing x coordinates" do
      knots = [knot(0.0, 0.0), knot(1.0, 1.0), knot(0.5, 0.25)]

      assert {:error, {:String, ~c"spline: x values must be strictly increasing"}} =
               @raw_module.fit(knots)
    end

    test "accepts a minimal 2-knot spline (degenerate to linear segment)" do
      assert {:ok, spline} = @raw_module.fit([knot(0.0, 0.0), knot(1.0, 2.0)])
      assert @raw_module.x_min(spline) == 0.0
      assert @raw_module.x_max(spline) == 1.0
      assert @raw_module.n_segments(spline) == 1
    end

    test "accepts 100 knots sampled from a quadratic" do
      knots = for i <- 0..99, do: knot(i * 1.0, i * i * 1.0)
      assert {:ok, spline} = @raw_module.fit(knots)
      # n_segments = knots - 1
      assert 99 == @raw_module.n_segments(spline)
    end
  end

  # ===========================================================================
  # Interpolation properties
  # ===========================================================================

  describe "interpolation properties" do
    test "passes exactly through every knot" do
      knots = [
        knot(0.0, 0.0),
        knot(1.0, 3.0),
        knot(2.5, -1.5),
        knot(4.0, 2.75),
        knot(5.0, 0.0)
      ]

      {:ok, spline} = @raw_module.fit(knots)

      for {:Knot, x, y} <- knots do
        {:ok, got} = @raw_module.evaluate(spline, x)
        assert_in_delta got, y, 1.0e-9
      end
    end

    test "reproduces strictly linear data exactly" do
      knots = for i <- 0..5, do: knot(i * 1.0, 3.0 * i + 1.0)
      {:ok, spline} = @raw_module.fit(knots)

      for x <- [0.5, 1.7, 3.14, 4.99] do
        expected = 3.0 * x + 1.0
        {:ok, got} = @raw_module.evaluate(spline, x)
        assert_in_delta got, expected, 1.0e-9
      end
    end

    test "approximates sin(x) to within 5e-3 over [0, 2pi] with 11 knots" do
      pi2 = 2.0 * :math.pi()
      knots = for i <- 0..10, do: knot(i * pi2 / 10.0, :math.sin(i * pi2 / 10.0))
      {:ok, spline} = @raw_module.fit(knots)

      max_err =
        for i <- 0..200 do
          x = i * pi2 / 200.0
          {:ok, y} = @raw_module.evaluate(spline, x)
          abs(y - :math.sin(x))
        end
        |> Enum.max()

      assert max_err < 5.0e-3
    end
  end

  # ===========================================================================
  # Evaluation domain handling
  # ===========================================================================

  describe "evaluate/2 domain handling" do
    setup do
      knots = [knot(0.0, 0.0), knot(1.0, 2.0), knot(2.0, 0.0)]
      {:ok, spline} = @raw_module.fit(knots)
      {:ok, spline: spline}
    end

    test "x below domain returns error", %{spline: spline} do
      assert {:error, {:String, ~c"spline: x below domain"}} = @raw_module.evaluate(spline, -0.5)
    end

    test "x above domain returns error", %{spline: spline} do
      assert {:error, {:String, ~c"spline: x above domain"}} = @raw_module.evaluate(spline, 2.5)
    end

    test "evaluate_clamped/2 returns a finite number outside domain", %{spline: spline} do
      below = @raw_module.evaluate_clamped(spline, -1.0)
      above = @raw_module.evaluate_clamped(spline, 10.0)
      assert is_float(below)
      assert is_float(above)
      # should match the boundary knot values
      assert_in_delta below, 0.0, 1.0e-9
      assert_in_delta above, 0.0, 1.0e-9
    end
  end

  # ===========================================================================
  # Smoothness -- C1 continuity across segment boundaries
  # ===========================================================================

  describe "C1 continuity" do
    test "one-sided derivatives at interior knots agree" do
      pi2 = 2.0 * :math.pi()
      knots = for i <- 0..10, do: knot(i * pi2 / 10.0, :math.sin(i * pi2 / 10.0))
      {:ok, spline} = @raw_module.fit(knots)

      for i <- 1..9 do
        kx = i * pi2 / 10.0
        {:ok, d_left} = @raw_module.derivative(spline, kx - 1.0e-9)
        {:ok, d_right} = @raw_module.derivative(spline, kx + 1.0e-9)
        assert_in_delta d_left, d_right, 1.0e-6
      end
    end
  end

  # ===========================================================================
  # Sampling
  # ===========================================================================

  describe "sample/2" do
    setup do
      knots = [knot(0.0, 1.0), knot(1.0, 0.5), knot(2.0, -0.25), knot(3.0, 0.5)]
      {:ok, spline} = @raw_module.fit(knots)
      {:ok, spline: spline}
    end

    test "returns exactly n points", %{spline: spline} do
      samples = @raw_module.sample(spline, 25)
      assert 25 == length(samples)
    end

    test "x values span the full domain and are monotone increasing", %{spline: spline} do
      samples = @raw_module.sample(spline, 11)
      xs = Enum.map(samples, fn {x, _} -> x end)

      assert hd(xs) == 0.0
      assert_in_delta List.last(xs), 3.0, 1.0e-9

      # strictly increasing
      xs
      |> Enum.chunk_every(2, 1, :discard)
      |> Enum.each(fn [a, b] -> assert a < b end)
    end

    test "first sample's y matches first knot", %{spline: spline} do
      [{_, y0} | _] = @raw_module.sample(spline, 10)
      assert_in_delta y0, 1.0, 1.0e-9
    end
  end

  # ===========================================================================
  # CureSpline (Elixir wrapper)
  # ===========================================================================

  describe "CureSpline wrapper" do
    test "accepts raw {x, y} tuples and returns an error for bad input" do
      assert {:error, _} = CureSpline.fit([])
      assert {:error, _} = CureSpline.fit([{0.0, 0.0}])
      assert {:error, _} = CureSpline.fit([{0.0, 0.0}, {0.0, 1.0}])
    end

    test "fits a spline through {x, y} tuples" do
      {:ok, spline} = CureSpline.fit([{0.0, 1.0}, {1.0, 3.0}, {2.0, 2.0}, {3.0, 0.0}])
      assert CureSpline.x_min(spline) == 0.0
      assert CureSpline.x_max(spline) == 3.0
      assert CureSpline.n_segments(spline) == 3
    end

    test "evaluate delegates and returns {:ok, value}" do
      {:ok, spline} = CureSpline.fit([{0.0, 0.0}, {1.0, 2.0}, {2.0, 0.0}])
      assert {:ok, y} = CureSpline.evaluate(spline, 1.0)
      assert_in_delta y, 2.0, 1.0e-9
    end

    test "evaluate_clamped returns finite values at boundaries" do
      {:ok, spline} = CureSpline.fit([{0.0, 0.0}, {1.0, 1.0}])
      assert is_float(CureSpline.evaluate_clamped(spline, -999.0))
      assert is_float(CureSpline.evaluate_clamped(spline, 999.0))
    end

    test "sample returns correct count" do
      {:ok, spline} = CureSpline.fit([{0.0, 0.0}, {1.0, 1.0}, {2.0, 4.0}, {3.0, 9.0}])
      samples = CureSpline.sample(spline, 15)
      assert 15 == length(samples)
      Enum.each(samples, fn {x, y} -> assert is_float(x) and is_float(y) end)
    end

    test "accepts integer coordinates and promotes to float" do
      {:ok, spline} = CureSpline.fit([{0, 0}, {1, 1}, {2, 4}])
      assert {:ok, y} = CureSpline.evaluate(spline, 1)
      assert_in_delta y, 1.0, 1.0e-9
    end

    test "demo/0 returns a spline and produces output" do
      captured =
        ExUnit.CaptureIO.capture_io(fn ->
          spline = CureSpline.demo()
          assert match?({:Spline, _segments, _x_min, _x_max}, spline)
        end)

      assert captured =~ "cure_spline demo"
      assert captured =~ "domain:"
    end
  end

  # ===========================================================================
  # CureSpline.Float helper
  # ===========================================================================

  describe "CureSpline.Float extern helper" do
    test "fdiv/2 performs float division" do
      assert_in_delta CureSpline.Float.fdiv(1.0, 3.0), 0.3333333333333333, 1.0e-15
      assert_in_delta CureSpline.Float.fdiv(10, 4), 2.5, 1.0e-15
    end

    test "to_float/1 promotes integers" do
      assert CureSpline.Float.to_float(42) === 42.0
      assert CureSpline.Float.to_float(1.5) === 1.5
    end
  end
end
