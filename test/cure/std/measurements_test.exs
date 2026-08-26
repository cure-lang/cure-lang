defmodule Cure.Std.MeasurementsTest do
  # End-to-end coverage for `Std.Measurements` (design 2026-07-08-units-macro-design).
  #
  # The distinctive behaviour is that a `literal` suffix (`ms`, `khz`, `pct`, …)
  # declared inside `lib/std/measurements.cure` expands at a use-site in ANOTHER file,
  # with no local `macro` block — i.e. standard-library literal rules are globally
  # active through the prelude, the same way keyword `:syntax` macros are. These
  # tests compile a *consumer* module that only `use Std.Measurements` and never declares
  # the rules itself, so a green result proves the cross-file propagation.
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  defp load!(mod_atom, source) do
    assert {:ok, ^mod_atom} = Cure.Compiler.compile_and_load(source, emit_events: false)
    mod_atom
  end

  describe "literal suffixes expand in a consumer file (cross-file propagation)" do
    test "time suffixes build a microsecond-backed Duration" do
      m =
        load!(:"Cure.UT1", """
        mod UT1
          use Std.Measurements
          fn a() -> Duration = 500ms
          fn b() -> Duration = 250us
          fn c() -> Duration = 2s
        """)

      assert {:Duration, 500_000} = apply(m, :a, [])
      assert {:Duration, 250} = apply(m, :b, [])
      assert {:Duration, 2_000_000} = apply(m, :c, [])
    end

    test "frequency, percent, and baud suffixes build their own wrappers" do
      m =
        load!(:"Cure.UT2", """
        mod UT2
          use Std.Measurements
          fn f() -> Frequency = 3khz
          fn g() -> Frequency = 50hz
          fn p() -> Percent = 80pct
          fn w() -> Baud = 9600baud
        """)

      assert {:Frequency, 3_000} = apply(m, :f, [])
      assert {:Frequency, 50} = apply(m, :g, [])
      assert {:Percent, 80} = apply(m, :p, [])
      assert {:Baud, 9600} = apply(m, :w, [])
    end
  end

  describe "same-unit arithmetic and conversions" do
    test "add/sub/scale stay within Duration and convert back to integers" do
      m =
        load!(:"Cure.UT3", """
        mod UT3
          use Std.Measurements
          fn sum_ms() -> Int = as_ms(add(500ms, 250ms))
          fn diff_ms() -> Int = as_ms(sub(1s, 250ms))
          fn scaled_us() -> Int = as_us(scale(1ms, 3))
          fn as_seconds() -> Int = as_s(2s)
        """)

      assert 750 = apply(m, :sum_ms, [])
      assert 750 = apply(m, :diff_ms, [])
      assert 3_000 = apply(m, :scaled_us, [])
      assert 2 = apply(m, :as_seconds, [])
    end
  end

  describe "quantities are unmixable and a bare number is not a quantity" do
    test "adding a Duration and a Frequency is a type error" do
      assert {:error, _} =
               Program.elaborate("""
               mod BadMix
                 use Std.Measurements
                 fn oops() -> Duration = add(500ms, 3khz)
               """)
    end

    test "a bare integer where a Duration is expected is a type error" do
      assert {:error, _} =
               Program.elaborate("""
               mod BadBare
                 use Std.Measurements
                 fn need(d: Duration) -> Duration = d
                 fn call() -> Duration = need(500)
               """)
    end
  end
end
