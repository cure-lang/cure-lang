defmodule Cure.Elab.RefinementUsecaseMatrixTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # The end-to-end payoff of wiring refinement obligations into the auto-lemma
  # proof search: an author writes a value at a refinement type and the proof is
  # discovered from in-scope evidence, `@lemma`s, the conjunction/projection
  # candidate sources, or the positivity procedure — never by hand. Every case
  # here is kernel-rechecked, so acceptance means a real proof was built.

  defp accepts(src), do: assert({:ok, _env} = Program.elaborate(src))

  test "conjunctive range: both bounds in context build the conjunction (lemma intro)" do
    accepts("""
    mod RangeIntro
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      fn clamp(x: Int, lo: IsTrue(0 <= x), hi: IsTrue(x <= 100)) -> {p: Int | 0 <= p and p <= 100} = x
    end
    """)
  end

  test "conjunctive range: a single conjunction hypothesis projects to one bound (elim)" do
    accepts("""
    mod RangeElim
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      fn lower(x: Int, both: IsTrue(0 <= x and x <= 100)) -> {p: Int | 0 <= p} = x
    end
    """)
  end

  test "positivity of a product discharges from the two factors' positivity (lemma/procedure)" do
    accepts("""
    mod ProductPositive
      use Std.Nat
      use Std.Proof.Math
      fn prod(a: Nat, b: Nat, pa: IsPositive(a), pb: IsPositive(b)) -> {n: Nat | IsPositive(n)} = multiply(a, b)
    end
    """)
  end

  test "positivity of a successor discharges from the successor_is_positive lemma with no hypothesis" do
    accepts("""
    mod SuccessorPositive
      use Std.Nat
      use Std.Proof.Math
      fn positive_successor(k: Nat) -> {n: Nat | IsPositive(n)} = S(k)
    end
    """)
  end

  test "a refined value flows into the same refinement via its carried proof (projection)" do
    accepts("""
    mod RefinedPassthrough
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn passthrough(v: {m: Int | m > 0}) -> {n: Int | n > 0} = v
    end
    """)
  end

  # The Std.Refine prelude ships these primitive-comparison refinement types; the
  # cases below pin every comparison operator's discharge from an in-scope
  # hypothesis, so no operator is only "green by luck" (matched structurally
  # without exercising its lowering). Each is the `NonZero`/`Negative`/… surface.

  test "strictly-negative (<) discharges from evidence" do
    accepts("""
    mod NegativeCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn f(x: Int, e: IsTrue(x < 0)) -> {n: Int | n < 0} = x
    end
    """)
  end

  test "non-negative (>=) discharges from evidence" do
    accepts("""
    mod NonNegativeCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn f(x: Int, e: IsTrue(x >= 0)) -> {n: Int | n >= 0} = x
    end
    """)
  end

  test "non-positive (<=) discharges from evidence" do
    accepts("""
    mod NonPositiveCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn f(x: Int, e: IsTrue(x <= 0)) -> {n: Int | n <= 0} = x
    end
    """)
  end

  test "non-zero (!=) discharges from evidence" do
    accepts("""
    mod NonZeroCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn f(x: Int, e: IsTrue(x != 0)) -> {n: Int | n != 0} = x
    end
    """)
  end

  test "strictly-positive float (single Float comparison) discharges from evidence" do
    accepts("""
    mod PositiveFloatCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn f(x: Float, e: IsTrue(x > 0.0)) -> {n: Float | n > 0.0} = x
    end
    """)
  end

  # Float CONJUNCTION: the `Probability` surface `{p: Float | 0.0 <= p and p <= 1.0}`.
  # Discharge builds the conjunction from two Float bounds — it must lower each
  # comparison to the Float builtin (`float_le`), not the Int one, in the index
  # position, and then assemble via the conjunction lemma.
  test "probability (Float conjunction) discharges from both bounds" do
    accepts("""
    mod ProbabilityCase
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      fn f(p: Float, lo: IsTrue(0.0 <= p), hi: IsTrue(p <= 1.0)) -> {q: Float | 0.0 <= q and q <= 1.0} = p
    end
    """)
  end

  # The shipped `Std.Refine` prelude types are named aliases for the same Sigma the
  # inline `{x: T | φ}` sugar lowers to. These cases exercise them through `use
  # Std.Refine` so the alias is δ-unfolded to its refinement Sigma before discharge —
  # covering the named-type surface an author actually writes, and the Int + Float
  # conjunction aliases (`Percentage`/`Probability`) together.
  test "shipped Std.Refine.Percentage (Int conjunction alias) discharges from matching bounds" do
    accepts("""
    mod ShippedPercentage
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      use Std.Refine
      fn f(p: Int, lo: IsTrue(p >= 0), hi: IsTrue(p <= 100)) -> Percentage = p
    end
    """)
  end

  test "shipped Std.Refine.Probability (Float conjunction alias) discharges from matching bounds" do
    accepts("""
    mod ShippedProbability
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      use Std.Refine
      fn f(p: Float, lo: IsTrue(p >= 0.0), hi: IsTrue(p <= 1.0)) -> Probability = p
    end
    """)
  end

  # Soundness guard: evidence for the wrong comparison direction (`0 <= p` where the
  # `Percentage` predicate is `p >= 0`) must NOT discharge — the proof search matches
  # structurally, so a mismatched-operator hypothesis is genuinely absent.
  test "shipped Std.Refine.Percentage rejects mismatched-operator evidence" do
    assert {:error, _} =
             Program.elaborate("""
             mod ShippedPercentageMismatch
               use Std.Nat
               use Std.Bool
               use Std.Proof.IntMath
               use Std.Proof.BooleanReflection
               use Std.Refine
               fn f(p: Int, lo: IsTrue(0 <= p), hi: IsTrue(p <= 100)) -> Percentage = p
             end
             """)
  end
end
