defmodule Cure.Stdlib.DecimalTest do
  use ExUnit.Case, async: true

  @decimal :"Cure.Std.Decimal"

  # `Std.Decimal` is written entirely against `String`, which is nominal --
  # `rec String { characters: List(Char) }` -- and therefore erases to the tagged
  # pair `{:String, code_points}`. A BEAM caller of a compiled Cure function
  # speaks that erased language directly, so a bare charlist is not a `String`.
  defp cure_string(text), do: {:String, String.to_charlist(text)}
  defp elixir_string({:String, chars}), do: List.to_string(chars)

  defp decimal!(text) do
    assert {:ok, value} = apply(@decimal, :from_string, [cure_string(text)])
    value
  end

  defp render(value), do: @decimal |> apply(:to_string, [value]) |> elixir_string()

  describe "construction and parsing" do
    test "parses ordinary, scientific, leading-dot, and special forms" do
      assert render(decimal!("123.45")) == "123.45"
      assert render(decimal!(".5")) == "0.5"
      assert render(decimal!("1e3")) == "1E+3"
      assert render(decimal!("-7.5")) == "-7.5"
      assert render(decimal!("-iNf")) == "-Infinity"
      assert render(decimal!("nAn")) == "NaN"
      assert {:error, {:String, ~c"bad"}} = apply(@decimal, :from_string, [cure_string("bad")])
    end

    test "parse/1 returns the unconsumed suffix" do
      assert {:ok, {value, {:String, ~c"rest"}}} =
               apply(@decimal, :parse, [cure_string("3.14rest")])

      assert render(value) == "3.14"
    end

    test "keeps coefficients at arbitrary precision" do
      digits = "1234567890123456789012345678901234567890.0001"
      assert render(decimal!(digits)) == digits
    end
  end

  describe "arithmetic" do
    test "performs exact addition, subtraction, and multiplication" do
      assert render(apply(@decimal, :add, [decimal!("0.1"), decimal!("0.2")])) == "0.3"
      assert render(apply(@decimal, :subtract, [decimal!("1"), decimal!("0.1")])) == "0.9"

      assert render(apply(@decimal, :multiply, [decimal!("19.99"), decimal!("0.08")])) ==
               "1.5992"
    end

    test "division uses the default 28-digit context and preserves exact quotients" do
      assert render(apply(@decimal, :divide, [decimal!("3"), decimal!("4")])) == "0.75"

      assert render(apply(@decimal, :divide, [decimal!("1"), decimal!("3")])) ==
               "0.3333333333333333333333333333"
    end

    test "square roots handle exact, rounded, negative, and infinite values" do
      assert render(apply(@decimal, :square_root, [decimal!("100")])) == "10"

      assert render(apply(@decimal, :square_root, [decimal!("2")])) ==
               "1.414213562373095048801688724"

      assert apply(@decimal, :is_nan, [apply(@decimal, :square_root, [decimal!("-1")])])
      assert render(apply(@decimal, :square_root, [apply(@decimal, :infinity, [])])) == "Infinity"
    end
  end

  describe "rounding and normalization" do
    test "supports all midpoint families and directional rounding" do
      assert render(apply(@decimal, :round, [decimal!("1.25"), 1, :HalfEven])) == "1.2"
      assert render(apply(@decimal, :round, [decimal!("1.25"), 1, :HalfUp])) == "1.3"
      assert render(apply(@decimal, :round, [decimal!("1.25"), 1, :HalfDown])) == "1.2"
      assert render(apply(@decimal, :round, [decimal!("-1.21"), 1, :Floor])) == "-1.3"
      assert render(apply(@decimal, :round, [decimal!("-1.21"), 1, :Ceiling])) == "-1.2"
    end

    test "normalization removes insignificant coefficient zeros" do
      assert render(apply(@decimal, :normalize, [decimal!("1.00")])) == "1"
      assert render(apply(@decimal, :normalize, [decimal!("1.01")])) == "1.01"
    end
  end

  describe "comparison, conversion, and integer division" do
    test "numeric equality ignores representation exponent" do
      a = decimal!("1.0")
      b = decimal!("1.00")
      assert {:ok, :EqualTo} = apply(@decimal, :compare, [a, b])
      assert apply(@decimal, :eq, [a, b])
      refute apply(@decimal, :lt, [a, b])
    end

    test "converts integral decimals and rejects fractional ones" do
      assert {:ok, 42} = apply(@decimal, :to_int, [decimal!("42.00")])
      assert {:error, :OutOfRange} = apply(@decimal, :to_int, [decimal!("42.5")])
    end

    test "returns quotient and signed remainder together" do
      assert {quotient, remainder} = apply(@decimal, :divide_remainder, [decimal!("-5"), decimal!("2")])
      assert render(quotient) == "-2"
      assert render(remainder) == "-1"
    end
  end

  describe "format variants and special values" do
    test "renders scientific, raw, and XSD forms" do
      value = decimal!("123.45")
      assert @decimal |> apply(:to_string_scientific, [value]) |> elixir_string() == "1.2345E+2"
      assert @decimal |> apply(:to_string_raw, [value]) |> elixir_string() == "12345E-2"
      assert @decimal |> apply(:to_string_xsd, [decimal!("42")]) |> elixir_string() == "42.0"
    end

    test "propagates NaN and handles infinity arithmetic" do
      nan = apply(@decimal, :nan, [])
      inf = apply(@decimal, :infinity, [])
      zero = apply(@decimal, :zero, [])

      assert apply(@decimal, :is_nan, [apply(@decimal, :add, [nan, decimal!("1")])])
      assert apply(@decimal, :is_nan, [apply(@decimal, :subtract, [inf, inf])])
      assert apply(@decimal, :is_nan, [apply(@decimal, :multiply, [inf, zero])])
    end
  end
end
