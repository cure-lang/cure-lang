defmodule Cure.Elab.InductionBranchPathsTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel, Validator}
  alias Cure.Elab.Program

  defp checked!(source) do
    assert {:ok, env} = Program.elaborate(source)
    assert Env.total?(env, :theorem)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :theorem))
    env
  end

  test "a sole nullary constructor still refines its subject in the branch goal" do
    env =
      checked!("""
      mod SingletonInductionBranch
        type Flag = Only
        fn theorem(flag: Flag) -> Equivalent(Flag, flag, Only()) = induction flag
          case Only => exact reflexive(Only())
      end
      """)

    assert Enum.any?(Validator.nodes(Env.get_def(env, :theorem).body), &match?({:case, _, _, _}, &1))
  end

  test "non-equality omega branch commands use the real caller hypotheses" do
    checked!("""
    mod OmegaInductionBranch
      use Std.Proof.LinearArithmetic
      use Std.Proof.IntOrder
      macro Tactics
        tactic close_order becomes by omega
      type Flag = Only
      fn theorem(a: Int, b: Int, h: IsLessThanOrEqual(a, b), flag: Flag) -> IsLessThanOrEqual(a, b) = induction flag
        case Only => close_order
    end
    """)
  end

  test "existing nested induction checks each singleton branch at its own refined goal" do
    checked!("""
    mod NestedSingletonInductionBranch
      type Flag = Only
      fn theorem(left: Flag, right: Flag) -> Equivalent(Flag, right, Only()) = induction left
        case Only => induction right
          case Only => exact reflexive(Only())
    end
    """)
  end

  test "nested induction branches retain local command and exact-expression semantics" do
    checked!("""
    mod NestedCommandInductionBranch
      type Nat = Z | S(Nat)
      fn theorem(left: Nat, right: Nat) -> Equivalent(Nat, Z, Z) = induction left
        case Z => induction right
          case Z =>
            have fact: Equivalent(Nat, Z, Z) = reflexive(Z)
            exact fact
          case S(previous, ih) => exact ih
        case S(previous, ih) => exact ih
    end
    """)
  end
end
