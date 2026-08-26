defmodule Cure.Stdlib.ProofIntMathTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Std.Proof.IntMath reflects the primitive Int comparison (which already folds
  # to the inductive Bool `True()`/`False()`) into a proposition `IsTrue(claim)`.
  # A closed comparison reduces by computation, so `Confirmed()` inhabits it with
  # no solver and no kernel change.

  test "a closed satisfied Int comparison is inhabited by Confirmed() via computation" do
    src = """
    mod ClosedPositive
      use Std.Bool
      use Std.Proof.IntMath

      fn five_is_positive() -> IsTrue(5 > 0) = Confirmed()
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a closed UNSATISFIED Int comparison cannot be inhabited by Confirmed()" do
    src = """
    mod ClosedNegative
      use Std.Bool
      use Std.Proof.IntMath

      fn five_is_negative() -> IsTrue(5 < 0) = Confirmed()
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
