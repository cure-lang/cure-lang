defmodule Cure.Core.GradeTest do
  @moduledoc """
  `Cure.Core.Grade` — the quantity carrier for QTT (Atkey), modelled on Idris's
  `Algebra.Semiring` + `Algebra.Preorder` (`src/Algebra/*.idr`), which abstract
  the quantity so `ZeroOneOmega` is merely one instance.

  Cure instantiates a FOUR-element carrier — `0`, `1`, `affine` (≤1), `ω` —
  because the expensive part of quantities is the binder reshape, not the
  carrier, and it is paid once. Affine is one row in `admits?/2`.

  Laws asserted here are the ordered-semiring laws. They are the contract every
  other pass relies on, and they are exhaustively checkable: the carrier is
  finite, so these are proofs, not samples.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Grade

  @all [:erased, :linear, :affine, :unrestricted]

  defp all3, do: for(a <- @all, b <- @all, c <- @all, do: {a, b, c})

  describe "carrier" do
    test "the four grades round-trip through their names" do
      for g <- @all, do: assert(Grade.grade?(g))
      refute Grade.grade?(:bogus)
      refute Grade.grade?(1)
    end

    test "zero and one are the semiring neutrals" do
      assert Grade.zero() == :erased
      assert Grade.one() == :linear
    end
  end

  describe "additive monoid (usage sum)" do
    test "zero is the additive identity" do
      for a <- @all do
        assert Grade.add(Grade.zero(), a) == a
        assert Grade.add(a, Grade.zero()) == a
      end
    end

    test "addition is commutative" do
      for a <- @all, b <- @all, do: assert(Grade.add(a, b) == Grade.add(b, a))
    end

    test "addition is associative" do
      for {a, b, c} <- all3() do
        assert Grade.add(Grade.add(a, b), c) == Grade.add(a, Grade.add(b, c))
      end
    end

    test "using a thing twice is unrestricted" do
      assert Grade.add(:linear, :linear) == :unrestricted
      assert Grade.add(:affine, :affine) == :unrestricted
      assert Grade.add(:linear, :affine) == :unrestricted
    end
  end

  describe "multiplicative monoid (scaling)" do
    test "one is the multiplicative identity" do
      for a <- @all do
        assert Grade.mul(Grade.one(), a) == a
        assert Grade.mul(a, Grade.one()) == a
      end
    end

    test "zero annihilates" do
      for a <- @all do
        assert Grade.mul(Grade.zero(), a) == Grade.zero()
        assert Grade.mul(a, Grade.zero()) == Grade.zero()
      end
    end

    test "multiplication is associative" do
      for {a, b, c} <- all3() do
        assert Grade.mul(Grade.mul(a, b), c) == Grade.mul(a, Grade.mul(b, c))
      end
    end

    test "scaling an affine thing affinely stays affine" do
      assert Grade.mul(:affine, :affine) == :affine
      assert Grade.mul(:affine, :unrestricted) == :unrestricted
    end
  end

  describe "distributivity (the law that makes scaling a context coherent)" do
    test "left distributive" do
      for {a, b, c} <- all3() do
        assert Grade.mul(a, Grade.add(b, c)) == Grade.add(Grade.mul(a, b), Grade.mul(a, c))
      end
    end

    test "right distributive" do
      for {a, b, c} <- all3() do
        assert Grade.mul(Grade.add(a, b), c) == Grade.add(Grade.mul(a, c), Grade.mul(b, c))
      end
    end
  end

  describe "admits?/2 — the usage rule (Idris LinearCheck.idr:274-276, generalised)" do
    test "erased admits exactly zero uses" do
      assert Grade.admits?(:erased, 0)
      refute Grade.admits?(:erased, 1)
      refute Grade.admits?(:erased, 7)
    end

    test "linear admits exactly one use" do
      refute Grade.admits?(:linear, 0)
      assert Grade.admits?(:linear, 1)
      refute Grade.admits?(:linear, 2)
    end

    test "affine admits at most one use — this is the whole of affinity" do
      assert Grade.admits?(:affine, 0)
      assert Grade.admits?(:affine, 1)
      refute Grade.admits?(:affine, 2)
    end

    test "unrestricted admits any number of uses" do
      for n <- 0..5, do: assert(Grade.admits?(:unrestricted, n))
    end
  end

  describe "preorder (subusaging)" do
    test "reflexive" do
      for a <- @all, do: assert(Grade.leq(a, a))
    end

    test "transitive" do
      for {a, b, c} <- all3() do
        if Grade.leq(a, b) and Grade.leq(b, c), do: assert(Grade.leq(a, c))
      end
    end

    test "unrestricted is the top" do
      for a <- @all, do: assert(Grade.leq(a, :unrestricted))
    end

    test "linear and erased both fit where affine is demanded" do
      assert Grade.leq(:erased, :affine)
      assert Grade.leq(:linear, :affine)
    end

    test "affine does NOT fit where linear is demanded (it may be dropped)" do
      refute Grade.leq(:affine, :linear)
    end

    test "erased does NOT fit where linear is demanded (it must be used)" do
      refute Grade.leq(:erased, :linear)
    end
  end

  describe "predicates the rest of the compiler uses" do
    test "erased?/1 identifies the erasable grade" do
      assert Grade.erased?(:erased)
      for g <- @all -- [:erased], do: refute(Grade.erased?(g))
    end

    test "present?/1 is the dual — anything a runtime value must exist for" do
      refute Grade.present?(:erased)
      for g <- @all -- [:erased], do: assert(Grade.present?(g))
    end

    test "restricted?/1 flags the grades a usage check must count" do
      refute Grade.restricted?(:unrestricted)
      assert Grade.restricted?(:linear)
      assert Grade.restricted?(:affine)
      assert Grade.restricted?(:erased)
    end
  end

  describe "the usage rule: leq/2 IS admits?/2 when usage is carried as a grade" do
    # `Cure.Elab.Relevance` (slice 4b) carries a binder's usage as a grade rather
    # than a count, so it can compose usages with the semiring (`add/2` in
    # sequence, `mul/2` on entering a subterm) and then apply the rule as
    # `leq(used, declared)`. That is only legitimate if subusaging and Idris's
    # `checkUsageOK` (`LinearCheck.idr:274-276`, generalised as `admits?/2`) agree
    # everywhere. The carrier is finite, so this is a proof, not a sample.
    #
    # A usage of `:affine` means "zero or one" — it arises from scaling a single
    # use by an affine position — so it must be admitted exactly when BOTH counts
    # are.
    @uses %{erased: [0], linear: [1], affine: [0, 1], unrestricted: [2]}

    test "leq(used, declared) agrees with admits? on every one of the 16 pairs" do
      for used <- @all, declared <- @all do
        by_count = Enum.all?(@uses[used], &Grade.admits?(declared, &1))

        assert Grade.leq(used, declared) == by_count,
               "leq(#{used}, #{declared}) = #{Grade.leq(used, declared)} but " <>
                 "admits?(#{declared}, #{inspect(@uses[used])}) = #{by_count}"
      end
    end

    test "the rule has teeth in both directions" do
      # A linear binder must be used exactly once: neither dropping nor duplicating.
      refute Grade.leq(:erased, :linear)
      refute Grade.leq(:unrestricted, :linear)
      assert Grade.leq(:linear, :linear)

      # An affine binder may be dropped, but not duplicated.
      assert Grade.leq(:erased, :affine)
      assert Grade.leq(:linear, :affine)
      refute Grade.leq(:unrestricted, :affine)
    end
  end
end
