defmodule Cure.Core.UniverseLevelTest do
  @moduledoc """
  U1 gate tests for `Cure.Core.UniverseLevel`.

  **Authority:** `docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`
  §18 Phase U1 ("Add algebraic property tests and malformed-form tests. Add
  arbitrary-precision closed-level tests.") and §19.1's verification matrix.

  The U1 gate is "focused UniverseLevel tests and property tests green; **no
  kernel semantics changed**". Nothing in this file touches `Term`, `Kernel` or
  `Conv`'s universe handling; it exercises the new module in isolation.

  `docs/LEAN4_PHASE5_U0_INVENTORY.md` §8 records the one substitution U1 makes:
  atom ordering uses `:erlang.term_to_binary/1` until U2 lands the versioned
  serializer.
  """

  use ExUnit.Case, async: true

  alias Cure.Core.UniverseLevel
  alias Cure.Core.UniverseLevel, as: L

  # ---------------------------------------------------------------------------
  # §19.1 — universe-level algebra
  # ---------------------------------------------------------------------------

  describe "§19.1 commutativity, associativity, idempotence of universe_max" do
    test "commutativity on closed levels" do
      for a <- 0..5, b <- 0..5 do
        assert L.equal?(L.max(L.closed(a), L.closed(b)), L.max(L.closed(b), L.closed(a)), nil)
      end
    end

    test "associativity on closed levels" do
      for a <- 0..3, b <- 0..3, c <- 0..3 do
        left = L.max(L.max(L.closed(a), L.closed(b)), L.closed(c))
        right = L.max(L.closed(a), L.max(L.closed(b), L.closed(c)))
        assert L.equal?(left, right, nil), "max(max(#{a},#{b}),#{c}) != max(#{a},max(#{b},#{c}))"
      end
    end

    test "idempotence" do
      for a <- 0..5 do
        assert L.equal?(L.max(L.closed(a), L.closed(a)), L.closed(a), nil)
      end
    end

    test "zero neutrality: max(a, zero) == a and max(zero, a) == a" do
      for a <- 0..5 do
        assert L.equal?(L.max(L.closed(a), L.zero()), L.closed(a), nil)
        assert L.equal?(L.max(L.zero(), L.closed(a)), L.closed(a), nil)
      end
    end
  end

  describe "§19.1 successor distribution over maximum" do
    test "succ(max(a, b)) == max(succ(a), succ(b))" do
      for a <- 0..3, b <- 0..3 do
        assert L.equal?(
                 L.succ(L.max(L.closed(a), L.closed(b))),
                 L.max(L.succ(L.closed(a)), L.succ(L.closed(b))),
                 nil
               )
      end
    end
  end

  describe "§19.1 subsumption and ordering" do
    test "a <= succ(a), and succ(a) <= a is false" do
      for a <- 0..5 do
        assert L.leq?(L.closed(a), L.succ(L.closed(a)), nil)
        refute L.leq?(L.succ(L.closed(a)), L.closed(a), nil)
      end
    end

    test "a + 1 <= a is rejected (§19.3)" do
      refute L.leq?(L.closed(1), L.closed(0), nil)
      refute L.leq?(L.closed(38), L.closed(37), nil)
    end

    test "reflexive and transitive" do
      for a <- 0..4 do
        assert L.leq?(L.closed(a), L.closed(a), nil)
      end

      assert L.leq?(L.closed(0), L.closed(1), nil)
      assert L.leq?(L.closed(1), L.closed(2), nil)
      assert L.leq?(L.closed(0), L.closed(2), nil)
    end
  end

  describe "§19.1 arbitrary-precision constants" do
    test "Type37 : Type38 without constructing 38 successor nodes" do
      big = L.closed(37)
      assert %UniverseLevel{constant: 37, atoms: []} = big
      assert %UniverseLevel{constant: 38, atoms: []} = L.succ(big)
      assert L.leq?(big, L.succ(big), nil)
    end

    test "levels far beyond any machine integer are representable" do
      huge = 10 ** 40
      assert %UniverseLevel{constant: ^huge} = L.closed(huge)
      assert L.leq?(L.closed(huge - 1), L.closed(huge), nil)
      refute L.leq?(L.closed(huge), L.closed(huge - 1), nil)
    end

    test "a negative closed level is an argument error, not a silent level" do
      assert_raise ArgumentError, fn -> L.closed(-1) end
    end
  end

  # ---------------------------------------------------------------------------
  # §19.1 canonical duplicate removal / deterministic ordering (§6.2)
  # ---------------------------------------------------------------------------

  describe "§6.2 canonical maximum-plus normal form" do
    test "max(0) is the unique zero normal form" do
      assert %UniverseLevel{constant: 0, atoms: []} = L.zero()
      assert L.equal?(L.zero(), L.closed(0), nil)
      assert L.equal?(L.max(L.closed(0), L.closed(0)), L.zero(), nil)
    end

    test "an equal atom appears once, retaining the greatest offset" do
      a = L.atom({:var, 0})

      # max(a, a+1) must collapse to a+1, not keep both.
      level = L.max(a, L.succ(a))
      assert %UniverseLevel{atoms: [{_, 1}]} = level
      assert [_] = level.atoms
    end

    test "atoms are sorted deterministically regardless of insertion order" do
      x = L.atom({:var, 0})
      y = L.atom({:var, 1})

      forward = L.max(x, y)
      backward = L.max(y, x)

      assert forward.atoms == backward.atoms
      assert L.equal?(forward, backward, nil)
    end

    test "a constant subsumed by an atom offset is dropped" do
      a = L.atom({:var, 0})
      # max(2, a+5): the atom already guarantees at least 5, so the constant 2
      # is redundant and canonical form stores 0.
      level = L.max(L.closed(2), L.succ(L.succ(L.succ(L.succ(L.succ(a))))))
      assert %UniverseLevel{constant: 0, atoms: [{_, 5}]} = level
    end

    test "a constant above every atom offset is retained" do
      a = L.atom({:var, 0})
      level = L.max(L.closed(9), L.succ(a))
      assert %UniverseLevel{constant: 9, atoms: [{_, 1}]} = level
    end
  end

  # ---------------------------------------------------------------------------
  # §19.1 substitution and shifting under nested grade-0 binders (§7.2)
  # ---------------------------------------------------------------------------

  describe "§7.2 shift and subst descend into level atoms" do
    test "shift moves a free variable inside an atom" do
      level = L.atom({:var, 0})
      shifted = L.shift(level, 1, 0)
      assert shifted.atoms == [{{:var, 1}, 0}]
    end

    test "shift respects the cutoff" do
      level = L.atom({:var, 0})
      # cutoff 1 means index 0 is bound, so it must not move.
      assert L.shift(level, 1, 1).atoms == [{{:var, 0}, 0}]
    end

    test "shift descends under a binder inside an atom" do
      # atom = λ. #0  — the variable is BOUND, so shifting must not touch it.
      level =
        L.atom(
          {:lam, Cure.Core.Grade.unrestricted(), {:type, {:finite, %UniverseLevel{constant: 0, atoms: []}}}, {:var, 0}}
        )

      shifted = L.shift(level, 1, 0)
      assert [{lam, _, _, {:var, 0}}] = shifted.atoms |> Enum.map(&elem(&1, 0))
      assert lam == :lam
    end

    test "subst replaces the target index inside an atom" do
      level = L.atom({:var, 0})
      substituted = L.subst(level, 0, {:global, :replacement})
      assert substituted.atoms == [{{:global, :replacement}, 0}]
    end

    test "subst shifts the replacement under a binder" do
      # The outer index 0 occurs as index 1 under the lambda.
      level =
        L.atom(
          {:lam, Cure.Core.Grade.unrestricted(), {:type, {:finite, %UniverseLevel{constant: 0, atoms: []}}}, {:var, 1}}
        )

      substituted = L.subst(level, 0, {:var, 2})
      # A distinct free index 2 becomes 3; leaving the old 1 proves nothing.
      assert [{:lam, _, _, {:var, 3}}] = substituted.atoms |> Enum.map(&elem(&1, 0))
    end

    test "free_vars reports free variables in atoms, respecting binders" do
      free = L.atom({:var, 0})

      bound =
        L.atom(
          {:lam, Cure.Core.Grade.unrestricted(), {:type, {:finite, %UniverseLevel{constant: 0, atoms: []}}}, {:var, 0}}
        )

      assert L.free_vars(free) == [0]
      assert L.free_vars(bound) == []
      assert L.free_vars(L.closed(3)) == []
      assert L.free_vars(L.max(free, L.atom({:var, 2}))) == [0, 2]
    end
  end

  # ---------------------------------------------------------------------------
  # §15 / §16 — malformed-form rejection
  # ---------------------------------------------------------------------------

  describe "§15 malformed and noncanonical encodings are rejected" do
    test "a well-formed canonical level validates" do
      assert :ok = L.validate(L.zero(), nil)
      assert :ok = L.validate(L.closed(37), nil)
      assert :ok = L.validate(L.atom({:var, 0}), nil)
      assert :ok = L.validate(L.max(L.closed(2), L.atom({:var, 1})), nil)
    end

    test "a negative constant is rejected" do
      assert {:error, {:noncanonical_level_encoding, _}} =
               L.validate(%UniverseLevel{constant: -1, atoms: []}, nil)
    end

    test "a negative offset is rejected" do
      assert {:error, {:noncanonical_level_encoding, _}} =
               L.validate(%UniverseLevel{constant: 0, atoms: [{{:var, 0}, -1}]}, nil)
    end

    test "duplicate atoms are rejected" do
      duplicated = %UniverseLevel{constant: 0, atoms: [{{:var, 0}, 0}, {{:var, 0}, 0}]}
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(duplicated, nil)
    end

    test "unsorted atoms are rejected" do
      x = {:var, 0}
      y = {:var, 1}
      [first, second] = Enum.sort_by([x, y], &L.atom_order_key/1)
      unsorted = %UniverseLevel{constant: 0, atoms: [{second, 0}, {first, 0}]}
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(unsorted, nil)
    end

    test "a constant subsumed by an atom offset is rejected" do
      # max(2, a+5) must canonicalize to constant 0; storing constant 2 is not
      # canonical.
      noncanonical = %UniverseLevel{constant: 2, atoms: [{{:var, 0}, 5}]}
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(noncanonical, nil)
    end

    test "a non-level value is rejected" do
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(0, nil)
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(%{constant: 0}, nil)
      assert {:error, {:noncanonical_level_encoding, _}} = L.validate(nil, nil)
    end

    test "an atom that is not a Core term is rejected" do
      assert {:error, {:noncanonical_level_encoding, _}} =
               L.validate(%UniverseLevel{constant: 0, atoms: [{"not a term", 0}]}, nil)
    end
  end

  # ---------------------------------------------------------------------------
  # §13 — erasure
  # ---------------------------------------------------------------------------

  describe "§13 level binders are grade zero" do
    test "binder_grade is :erased" do
      assert L.binder_grade() == :erased
      assert Cure.Core.Grade.erased?(L.binder_grade())
    end
  end

  # ---------------------------------------------------------------------------
  # §16 — display
  # ---------------------------------------------------------------------------

  describe "§16 source-notation rendering" do
    test "zero renders as universe_zero" do
      assert L.to_string(L.zero()) == "universe_zero"
    end

    test "a closed level renders as its numeral" do
      assert L.to_string(L.closed(37)) == "37"
    end

    test "an atom renders as its printed term" do
      # `Printer.print/2` renders a bare de Bruijn index with no name table as
      # `?#{k}`. The offset-zero atom is the whole level, so no `universe_max`
      # wrapper appears.
      assert L.to_string(L.atom({:var, 0})) == "?#{0}"
    end

    test "an offset atom renders as a successor chain, not a max with a numeral" do
      # `atom + 2` is `universe_succ(universe_succ(atom))`. Rendering it as
      # `universe_max(atom, 2)` would denote `max(atom, 2)` — a level floored by
      # the numeral 2 — which is a different level.
      #
      # The offset already guarantees the lower bound 2, so canonical form
      # drops that redundant constant.
      assert L.to_string(L.succ(L.succ(L.atom({:var, 0})))) ==
               "universe_succ(universe_succ(?#{0}))"
    end
  end
end
