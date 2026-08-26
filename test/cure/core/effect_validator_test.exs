defmodule Cure.Core.EffectValidatorTest do
  @moduledoc """
  Release-boundary Validator clauses for the inert `Effect` former
  (design 2026-07-09-effect-type-former §8). These are a STRUCTURAL backstop
  enforced at the emit boundary, NOT a kernel judgement — the kernel already
  types effect nodes; this lint catches an effect COMPUTATION node that has
  leaked into a TYPE/INDEX or structurally-ERASED position, where it can never
  legitimately appear.

  The critical property is the ACCEPT direction: every real effectful def body
  is a `bind`-chain full of effect nodes in TERM position, and those MUST pass
  (no false positives), or the lint would reject all effectful code.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Validator

  @omega Cure.Core.Grade.unrestricted()

  # A real effectful continuation body: bind(pure(1), λx:Int. pure(x)). Every
  # effect node here sits in TERM position.
  defp bind_chain,
    do: {:effect_bind, {:effect_pure, {:int_lit, 1}}, {:lam, @omega, {:int_type}, {:effect_pure, {:var, 0}}}}

  describe "ACCEPT — no false positives on real effectful terms (term position)" do
    test "an effectful bind-chain body in term position passes under release_config" do
      assert {:ok, _} = Validator.validate(bind_chain(), Validator.release_config())
    end

    test "Effect(Int) as a Pi domain is fine (the type former is legitimate in type position)" do
      term = {:pi, @omega, {:effect_type, {:int_type}}, {:int_type}}
      assert {:ok, _} = Validator.validate(term, Validator.release_config())
    end
  end

  describe "REJECT — effect computation in a type/index position" do
    test "a pure computation as a Pi domain is rejected" do
      term = {:pi, @omega, {:effect_pure, {:int_lit, 1}}, {:int_type}}

      assert {:error, [%{clause: :no_effect_in_type_position} | _]} =
               Validator.validate(term, Validator.release_config())
    end

    test "an effect_bind in a case motive is rejected" do
      # {:case, scrut, motive, branches} — motive is a type position.
      term = {:case, {:int_lit, 0}, bind_chain(), []}

      assert {:error, rejections} = Validator.validate(term, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_effect_in_type_position))
    end
  end

  describe "REJECT — effect computation under a structurally-erased binder" do
    test "an effect computation as an erased let value is rejected" do
      term = {:let, :erased, {:int_type}, {:effect_pure, {:int_lit, 1}}, {:var, 0}}

      assert {:error, rejections} = Validator.validate(term, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_effect_in_erased_position))
    end

    test "the same effect computation as an omega (non-erased) let value passes" do
      term = {:let, @omega, {:int_type}, {:effect_pure, {:int_lit, 1}}, {:var, 0}}
      assert {:ok, _} = Validator.validate(term, Validator.release_config())
    end
  end

  describe "effect_ops_known — registered but vacuous" do
    test "the clause is on the books" do
      assert :effect_ops_known in Validator.clauses()
    end
  end
end
