defmodule Cure.Elab.SimplifierTest do
  # This module contains an explicit wall-clock resource-ceiling assertion.
  # Running it in the saturated async compiler pool measures scheduler
  # contention instead of simplifier cost.
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  test "the audited default reduction set is finite and explicit" do
    assert Cure.Elab.Simplifier.audited_standard_rules() == [:beta, :iota, :zeta, :certified_delta]
  end

  test "bare simplify closes a definitionally equal justification goal" do
    source = """
    mod SimplifyDefinitional
      type Nat = Z | S(Nat)
      fn id(n: Nat) -> Nat = n
      fn theorem(x: Nat) -> Equivalent(Nat, id(x), x) =
        proof chain
          id(x) == x
          because simplify
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :theorem)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :theorem))
  end

  test "a residual simplification goal reports E112 data instead of accepting it" do
    source = """
    mod SimplifyResidual
      type Nat = Z | S(Nat)
      fn bad(x: Nat) -> Equivalent(Nat, x, S(x)) =
        proof chain
          x == S(x)
          because simplify
    end
    """

    assert {:error,
            {:source_context,
             {:simplification_failed,
              %Cure.Diagnostic.SimplificationProblem{kind: :residual_goal, before_goal: _, after_goal: _}}, _context}} =
             Program.elaborate(source)
  end

  test "explicit decreasing local equality rules produce a checked transport certificate" do
    source = """
    mod SimplifyExplicit
      type Nat = Z | S(Nat)
      fn adapt(x: Nat, y: Nat, equality: Equivalent(Nat, S(x), y)) -> Equivalent(Nat, S(S(x)), S(y)) =
        proof chain
          S(S(x)) == S(y)
          because simplify using [equality]
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :adapt))
  end

  test "equal-size ambiguous rules are rejected by the orientation policy" do
    source = """
    mod SimplifyOrientation
      type Nat = Z | S(Nat)
      fn reject(x: Nat, y: Nat, equality: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) =
        proof chain
          x == y
          because simplify using [equality]
    end
    """

    assert {:error,
            {:source_context,
             {:simplification_failed,
              %Cure.Diagnostic.SimplificationProblem{kind: :inadmissible_rule, cause: :non_decreasing_orientation}},
             _context}} = Program.elaborate(source)
  end

  test "universally quantified generated defining equations are instantiated as rules" do
    source = """
    mod SimplifyEquation
      type Nat = Z | S(Nat)
      fn identity(n: Nat) -> Nat = match n
        Z -> Z
        S(previous) -> S(previous)
      fn prove(x: Nat) -> Equivalent(Nat, identity(S(x)), S(x)) =
        proof chain
          identity(S(x)) == S(x)
          because simplify using [identity.S]
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :prove))
  end

  test "duplicate decreasing rules are deterministic and harmless" do
    source = """
    mod SimplifyDuplicate
      type Nat = Z | S(Nat)
      fn adapt(x: Nat, y: Nat, equality: Equivalent(Nat, S(x), y)) -> Equivalent(Nat, S(S(x)), S(y)) =
        proof chain
          S(S(x)) == S(y)
          because simplify using [equality, equality]
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :adapt))
  end

  test "mutually cycling and symmetric explicit rules are rejected before traversal" do
    source = """
    mod SimplifyCycle
      type Nat = Z | S(Nat)
      fn reject(x: Nat, y: Nat, xy: Equivalent(Nat, x, y), yx: Equivalent(Nat, y, x)) -> Equivalent(Nat, x, y) =
        proof chain
          x == y
          because simplify using [xy, yx]
    end
    """

    assert {:error,
            {:source_context,
             {:simplification_failed, %Cure.Diagnostic.SimplificationProblem{kind: :inadmissible_rule}}, _context}} =
             Program.elaborate(source)
  end

  test "the explicit step ceiling reports a resource guard on a large decreasing term" do
    nested = Enum.reduce(1..300, "x", fn _, acc -> "S(#{acc})" end)

    source = """
    mod SimplifyCeiling
      type Nat = Z | S(Nat)
      fn guarded(x: Nat, equality: Equivalent(Nat, S(x), x)) -> Equivalent(Nat, #{nested}, x) =
        proof chain
          #{nested} == x
          because simplify using [equality]
    end
    """

    started = System.monotonic_time(:millisecond)

    assert {:error,
            {:source_context,
             {:simplification_failed,
              %Cure.Diagnostic.SimplificationProblem{kind: :resource_guard, cause: {:step_ceiling, 256}}}, _context}} =
             Program.elaborate(source)

    assert System.monotonic_time(:millisecond) - started < 5_000
  end

  test "forged generated rules are rejected at admission even if their metadata claims provenance" do
    source = """
    mod SimplifyForged
      type Nat = Z | S(Nat)
      fn identity(n: Nat) -> Nat = match n
        Z -> Z
        S(previous) -> S(previous)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    [equation | _] = Env.equations(env, :identity)
    forged = put_in(env.defs[equation.theorem].body, Cure.Elab.Rewrite.mk_refl({:int_lit, 99}))

    assert {:error, :forged_generated_equation} =
             Cure.Elab.ProofGoal.admit_generated_rule(forged, equation.theorem)
  end
end
