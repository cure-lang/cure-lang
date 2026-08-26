defmodule Cure.Elab.RefinementAutodischargeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # §3a level 2: when a value is checked against a refinement type `{x: T | φ}` and
  # the obligation `φ[x := value]` is CLOSED, it reduces by computation
  # (`IsTrue(50 > 0)` → `IsTrue(True())`), so the elaborator fills the proof with the
  # reflection family's nullary constructor `Confirmed()` automatically — no `refine`,
  # no explicit proof. A violated obligation (`IsTrue(False())`) is rejected; an OPEN
  # obligation (mentioning a free binder) is left for explicit evidence, not invented.

  test "a satisfied closed literal auto-discharges at a bare refinement type" do
    assert {:ok, _} =
             Program.elaborate("""
             mod Lvl2Ok
               use Std.Bool
               use Std.Proof.IntMath
               fn ok() -> {n: Int | n > 0} = 50
             end
             """)
  end

  test "a satisfied range literal auto-discharges through a boolean conjunction" do
    assert {:ok, _} =
             Program.elaborate("""
             mod Lvl2Range
               use Std.Bool
               use Std.Proof.IntMath
               fn pct() -> {p: Int | 0 <= p and p <= 100} = 50
             end
             """)
  end

  test "a violated closed literal is rejected (no proof invented)" do
    assert {:error, _} =
             Program.elaborate("""
             mod Lvl2Bad
               use Std.Bool
               use Std.Proof.IntMath
               fn bad() -> {n: Int | n > 0} = 0
             end
             """)
  end

  test "an out-of-range literal is rejected" do
    assert {:error, _} =
             Program.elaborate("""
             mod Lvl2OutOfRange
               use Std.Bool
               use Std.Proof.IntMath
               fn bad() -> {p: Int | 0 <= p and p <= 100} = 150
             end
             """)
  end

  test "an open obligation is NOT auto-discharged (requires explicit evidence)" do
    assert {:error, _} =
             Program.elaborate("""
             mod Lvl2Open
               use Std.Bool
               use Std.Proof.IntMath
               fn f(x: Int) -> {n: Int | n > 0} = x
             end
             """)
  end
end
