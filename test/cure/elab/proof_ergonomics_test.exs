defmodule Cure.Elab.ProofErgonomicsTest do
  @moduledoc """
  Lean-parity proof ergonomics: `apply`/`exact` (C6), `rewrite … all` (C8), and
  the ambient `@lemma` simplification set (C4).

  Each command is elaboration syntax: it adds no Core constructors and no
  kernel rules. Every `ACCEPTED` assertion therefore also re-checks the
  resulting definition through the kernel, so a test cannot pass on an
  elaborator bug alone.
  """

  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  defp elaborate!(source) do
    assert {:ok, env} = Program.elaborate(source)
    env
  end

  defp assert_certified!(env, name) do
    assert Env.certified?(env, name), "expected #{name} to be totality-certified"
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, name))
  end

  defp assert_rejected!(source, predicate) do
    assert {:error, reason} = Program.elaborate(source)
    assert predicate.(reason), "unexpected rejection shape: #{inspect(reason, limit: 8)}"
  end

  # ── C6: apply / exact ────────────────────────────────────────────────────

  describe "exact (C6)" do
    test "closes a goal with a proof term of the exact goal type" do
      env =
        elaborate!("""
        mod ExactCloses
          type Nat = Z | S(Nat)
          fn refl_nat(x: Nat) -> Equivalent(Nat, x, x) = reflexive(x)
          fn theorem(x: Nat) -> Equivalent(Nat, x, x) =
            proof chain
              x == x
              because exact refl_nat(x)
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "rejects a proof of the wrong proposition" do
      assert_rejected!(
        """
        mod ExactWrong
          type Nat = Z | S(Nat)
          fn refl_nat(x: Nat) -> Equivalent(Nat, x, x) = reflexive(x)
          fn theorem(x: Nat) -> Equivalent(Nat, x, S(x)) =
            proof chain
              x == S(x)
              because exact refl_nat(x)
        end
        """,
        &match?({:source_context, _, _}, &1)
      )
    end
  end

  describe "apply (C6)" do
    test "closes a goal whose conclusion matches the applied theorem" do
      env =
        elaborate!("""
        mod ApplyCloses
          type Nat = Z | S(Nat)
          fn refl_nat(x: Nat) -> Equivalent(Nat, x, x) = reflexive(x)
          fn theorem(x: Nat) -> Equivalent(Nat, x, x) =
            proof chain
              x == x
              because apply refl_nat(x)
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "rejects an application that does not close the goal" do
      assert_rejected!(
        """
        mod ApplyWrong
          type Nat = Z | S(Nat)
          fn refl_nat(x: Nat) -> Equivalent(Nat, x, x) = reflexive(x)
          fn theorem(x: Nat) -> Equivalent(Nat, x, S(x)) =
            proof chain
              x == S(x)
              because apply refl_nat(x)
        end
        """,
        &match?({:source_context, {:proof_chain_mismatch, %{cause: {:apply_does_not_close, _}}}, _}, &1)
      )
    end

    test "apply stays an ordinary identifier outside a justification block" do
      # Contextual vocabulary: a function named `apply` must still work.
      env =
        elaborate!("""
        mod ApplyIsOrdinary
          type Nat = Z | S(Nat)
          fn apply(x: Nat) -> Nat = x
          fn use_it(x: Nat) -> Nat = apply(x)
        end
        """)

      assert_certified!(env, :use_it)
    end
  end

  # ── C8: rewrite … all ────────────────────────────────────────────────────

  describe "rewrite … all (C8)" do
    test "rewrites every occurrence in one step" do
      env =
        elaborate!("""
        mod RewriteAll
          type Nat = Z | S(Nat)
          type Pair = Pair(Nat, Nat)
          fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) =
            proof chain
              Pair(x, x) == Pair(y, y)
              because
                rewrite using h all
                simplify
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "single-occurrence default is unchanged: a multi-match goal still fails" do
      assert_rejected!(
        """
        mod RewriteStillStrict
          type Nat = Z | S(Nat)
          type Pair = Pair(Nat, Nat)
          fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) =
            proof chain
              Pair(x, x) == Pair(y, y)
              because
                rewrite using h
                simplify
        end
        """,
        &match?({:source_context, {:rewrite_failed, %{kind: :ambiguous_occurrence}}, _}, &1)
      )
    end

    test "all with no matching occurrence still reports no_occurrence" do
      assert_rejected!(
        """
        mod RewriteAllNone
          type Nat = Z | S(Nat)
          fn theorem(x: Nat, h: Equivalent(Nat, S(x), S(x))) -> Equivalent(Nat, x, x) =
            proof chain
              x == x
              because
                rewrite using h all
                simplify
        end
        """,
        &match?({:source_context, {:rewrite_failed, %{kind: :no_occurrence}}, _}, &1)
      )
    end
  end

  # ── C4: ambient @lemma simplification set ────────────────────────────────

  describe "ambient @lemma simplification (C4)" do
    test "a proved @lemma equation participates in bare simplify" do
      env =
        elaborate!("""
        mod AmbientLemma
          type Nat = Z | S(Nat)
          fn plus(l: Nat, r: Nat) -> Nat = match l
            Z -> r
            S(p) -> S(plus(p, r))
          @lemma
          fn plus_zero(x: Nat) -> Equivalent(Nat, plus(x, Z), x) = induction x
            case Z => reflexive(Z)
            case S(p, ih) => proof chain
              plus(S(p), Z) == S(p)
              because
                rewrite using ih
                simplify
          fn theorem(x: Nat) -> Equivalent(Nat, plus(x, Z), x) =
            proof chain
              plus(x, Z) == x
              because simplify
        end
        """)

      assert_certified!(env, :plus_zero)
      assert_certified!(env, :theorem)
    end

    test "an uncertified lemma is not admitted into the ambient set" do
      # `loop` is not certified total, so its equation must not rewrite.
      assert_rejected!(
        """
        mod UncertifiedLemma
          type Nat = Z | S(Nat)
          @lemma
          fn loop(x: Nat) -> Equivalent(Nat, x, Z) = loop(x)
          fn theorem(x: Nat) -> Equivalent(Nat, x, Z) =
            proof chain
              x == Z
              because simplify
        end
        """,
        fn reason -> match?({:error, _}, reason) or match?({_, _, _}, reason) end
      )
    end
  end

  # ── Non-regression: the existing vocabulary still works ──────────────────

  describe "existing proof vocabulary is unchanged" do
    test "bare simplify still closes a definitionally equal goal" do
      env =
        elaborate!("""
        mod SimplifyStillWorks
          type Nat = Z | S(Nat)
          fn id(n: Nat) -> Nat = n
          fn theorem(x: Nat) -> Equivalent(Nat, id(x), x) =
            proof chain
              id(x) == x
              because simplify
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "bare simplify still closes a recursive certified-unfolding goal" do
      # This is the C5 case: certified δ unfolding already reaches it.
      env =
        elaborate!("""
        mod SimplifyRecursive
          type Nat = Z | S(Nat)
          fn plus(l: Nat, r: Nat) -> Nat = match l
            Z -> r
            S(p) -> S(plus(p, r))
          fn theorem(v: Nat) -> Equivalent(Nat, plus(Z, plus(Z, v)), v) =
            proof chain
              plus(Z, plus(Z, v)) == v
              because simplify
        end
        """)

      assert_certified!(env, :theorem)
    end

    test "the audited default rule set is unchanged" do
      assert Cure.Elab.Simplifier.audited_standard_rules() == [:beta, :iota, :zeta, :certified_delta]
    end
  end
end
