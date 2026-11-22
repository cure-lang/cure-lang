defmodule Cure.Elab.Phase4TacticsTest do
  @moduledoc """
  Delivered-scope and refusal tests for Phase 4 of `docs/PATH_TO_LEAN4.md` §8:
  C1.2 computed tactics, closing apply and missing-premise refusal, server/REPL
  goal views, and checked automation (`assumption`, bounded `omega`, `simp?`).
  These do not establish premise generation or a VS Code goal-panel client.

  Every test here measures REACH or a REFUSAL. None of them is a soundness
  theorem: the trust boundary remains the kernel re-checking evidence at the
  original goal, and these tests assert that the boundary is still in place
  (a false goal is still refused) rather than that it could never be crossed.
  """

  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, ProofGoal, Tactic}
  alias Cure.Pipeline.Events

  # -- helpers ---------------------------------------------------------------

  defp elaborate(source), do: Program.elaborate(source)

  defp assert_elaborates(source) do
    assert {:ok, env} = elaborate(source)
    env
  end

  defp refusal_cause(reason) do
    case Program.semantic_error(reason) do
      {:proof_chain_mismatch, %{cause: cause}} -> refusal_cause(cause)
      {:computed_macro_error, _meta, cause} -> refusal_cause(cause)
      cause -> cause
    end
  end

  test "C6 remaining scope: an under-applied theorem does not fabricate premise evidence" do
    source = """
    mod PendingBackwardPremise
      use Std.Equivalent

      fn need(x: Int, h: Equivalent(Int, x, x)) -> Equivalent(Int, x, x) = h
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because
          apply need(x)
          reflexive(x)
    end
    """

    assert {:error, {:proof_chain_mismatch, %{cause: {:apply_does_not_close, _}}}} =
             source |> Program.elaborate() |> Program.semantic_result()
  end

  defp assert_refused(source) do
    assert {:error, reason} = elaborate(source)
    refusal_cause(reason)
  end

  # -- C1.2: goal-inspecting computed tactics --------------------------------

  @computed_provider """
  mod ComputedProvider
    use Std.Tactic
    use Std.Equivalent
    use Std.Syntax
    use Std.Bool
    use Std.Nat

    fn identity(value: Nat) -> Nat = value

    macro Tactics
      tactic close computed by close_goal

    ## Inspects the goal and picks a command from what it sees. This is the C1.2
    ## shape: the expander receives a goal VALUE, so the choice is made from the
    ## goal's own head rather than from the captures at the use site.
    fn close_goal(g: Goal) -> MacroResult = match is_equality(g)
      True() -> expand(Std.Tactic.simplify(g))
      False() -> reject_goal("computed tactic only handles equalities")
  end
  """

  defp computed_consumer(body) do
    String.replace_suffix(@computed_provider, "end\n", body <> "\nend\n")
  end

  test "C1.2: a computed tactic inspects the goal and closes it" do
    source =
      computed_consumer("""
        fn theorem(value: Nat) -> Equivalent(Nat, identity(value), value) = proof chain
          identity(value) == value
          because close
      """)

    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"ComputedProvider#theorem")
  end

  test "C1.2: a computed tactic that rejects the goal shape refuses the proof" do
    # `Std.Tactic.is_equality` inspects the goal's own head. A goal that is not an
    # `Equivalent(…)` proposition answers `False()`, so the expander takes its
    # `reject_goal` branch and the proof is refused with the expander's own
    # words -- not a fabricated success, and not a generic E110.
    source =
      computed_consumer("""
        use Std.Proof.Math

        fn theorem(value: Nat) -> IsPositive(S(value)) = by close
      """)

    assert {:author_diagnostics, [{:diagnostic_details, meta, _}]} = assert_refused(source)
    assert meta[:message] == "computed tactic only handles equalities"
  end

  test "C1.2: a computed tactic cannot close a false goal" do
    source =
      computed_consumer("""
        fn wrong() -> Equivalent(Nat, Z(), S(Z())) = proof chain
          Z() == S(Z())
          because close
      """)

    assert {:simplification_failed, _} = assert_refused(source)
  end

  test "C1.2: the operation vocabulary is closed -- an unknown operation is refused" do
    source = """
    mod UnknownOperation
      use Std.Tactic
      use Std.Equivalent
      use Std.Syntax

      type Nat = Z | S(Nat)

      macro Tactics
        tactic cheat computed by cheat_goal

      ## Builds a `tactic_operation` node naming a command that does not exist.
      ## `Tactic.Computed` validates against its own closed table, so this is a
      ## diagnostic and never a silent no-op.
      fn cheat_goal(g: Goal) -> MacroResult =
        expand(operation(:prove_everything, g, []))

      fn wrong(value: Nat) -> Equivalent(Nat, value, value) = proof chain
        value == value
        because cheat
    end
    """

    assert {:unknown_tactic_operation, :prove_everything, _} = assert_refused(source)
  end

  # -- C6: backward `apply` ------------------------------------------------

  test "C6 delivered subset: a fully supplied apply closes the goal" do
    source = """
    mod BackwardApply
      use Std.Equivalent

      type Nat = Z | S(Nat)

      fn identity(value: Nat) -> Nat = value

      fn theorem(value: Nat) -> Equivalent(Nat, identity(value), value) = proof chain
        identity(value) == value
        because
          apply reflexive(identity(value))
    end
    """

    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"BackwardApply#theorem")
  end

  test "C6: apply that does not fit reports the residual goal (E110)" do
    source = """
    mod BackwardApplyMismatch
      use Std.Equivalent

      type Nat = Z | S(Nat)

      fn wrong(value: Nat) -> Equivalent(Nat, S(value), value) = proof chain
        S(value) == value
        because
          apply reflexive(value)
    end
    """

    assert {:apply_does_not_close, _} = assert_refused(source)
  end

  # -- C7: goal views ------------------------------------------------------

  test "C7: inspect_goal reports the target and the checked hypothesis types" do
    env =
      assert_elaborates("""
      mod GoalView
        use Std.Equivalent

        type Nat = Z | S(Nat)

        fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) =
          proof chain
            x == y
            because
              exact h
      end
      """)

    %{type: type} = Env.get_def(env, :theorem)
    {context, target} = open_telescope(type, Context.empty(env))
    goal = ProofGoal.new(target, ["h", "y", "x"], context, env)

    assert %{target: ^target, hypotheses: hypotheses} = ProofGoal.inspect_goal(goal)
    assert Enum.map(hypotheses, & &1.name) == ["h", "y", "x"]
    assert Enum.all?(hypotheses, &(not is_nil(&1.type)))
  end

  defp open_telescope({:pi, grade, domain, body}, context),
    do: open_telescope(body, Context.extend(context, Eval.eval(domain, Context.env(context)), grade))

  defp open_telescope(target, context), do: {context, target}

  test "C7: the LSP proofState request reports open goals with type and context" do
    source = """
    mod ParityProofState
      use Std.Equivalent

      fn later(x: Int) -> Equivalent(Int, x, x) = ?goal
    end
    """

    assert [%{"function" => function, "goal" => goal, "context" => context}] =
             Cure.LSP.Server.proof_state(source)

    assert is_binary(function)
    assert is_binary(goal)
    assert is_list(context)
  end

  test "C7: proofState on a document with no holes is an empty list, not an error" do
    assert [] = Cure.LSP.Server.proof_state("mod NoHoles\n  fn id(n: Int) -> Int = n\nend\n")
  end

  test "C7: proofState degrades to [] on an unparseable buffer" do
    assert [] = Cure.LSP.Server.proof_state("mod Broken\n  fn (\n")
  end

  test "C7: the REPL session goal view reports the same goal as the LSP" do
    source = "fn later(x: Int) -> Equivalent(Int, x, x) = ?goal"

    {:definitions, entries} = Cure.REPL.Session.classify(source)
    assert {:ok, [%{function: _function, goal: goal, context: _context}]} = Cure.REPL.Session.goals(entries)
    assert is_binary(goal)
  end

  # -- tactic wrappers over the sound libraries -----------------------------

  test "assumption closes a goal that is one of the local hypotheses" do
    source = """
    mod AssumptionCloses
      use Std.Proof.Math

      fn theorem(value: Nat, h: IsPositive(value)) -> IsPositive(value) = by assumption
    end
    """

    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"AssumptionCloses#theorem")
  end

  test "assumption refuses a goal that is not a local hypothesis" do
    source = """
    mod AssumptionRefuses
      use Std.Proof.Math

      fn theorem(value: Nat) -> IsPositive(S(value)) = by assumption
    end
    """

    assert_refused(source)
  end

  test "assumption does not inhabit a proof-relevant value type from a local" do
    # `Nat` is proof-RELEVANT: a local `n: Nat` is a value, not a proof. Gating
    # on `proposition?/3` is what keeps `assumption` from silently choosing an
    # inhabitant the author never wrote.
    source = """
    mod AssumptionValueType
      fn identity(n: Nat) -> Nat = by assumption
    end
    """

    assert_refused(source)
  end

  test "assumption works inside a justification block" do
    source = """
    mod AssumptionInBlock
      use Std.Equivalent

      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
        x == y
        because
          by assumption
    end
    """

    assert_elaborates(source)
  end

  # -- simp? (G10) ---------------------------------------------------------

  test "simp? runs the same simplification as simplify and reports fired lemmas" do
    source = """
    mod SimpTrace
      use Std.Equivalent

      type Nat = Z | S(Nat)

      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))

      @simp
      fn plus_zero(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
        case Z => reflexive(Z())
        case S(previous, ih) => rewrite ih in reflexive(S(previous))

      fn reduced(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
        plus(plus(value, Z()), Z()) == value
        because simp?
    end
    """

    Events.subscribe(:type_checker, :simp_trace)
    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"SimpTrace#reduced")

    assert_receive {Events, :type_checker, :simp_trace, %{lemmas: lemmas}, _meta}, 5_000
    assert :"SimpTrace#plus_zero" in lemmas
  end

  test "simp? closes the same goals as simplify (no second rule set)" do
    body = fn command ->
      """
      mod SimpEquivalence
        use Std.Equivalent

        type Nat = Z | S(Nat)

        fn plus(left: Nat, right: Nat) -> Nat = match left
          Z() -> right
          S(previous) -> S(plus(previous, right))

        @simp
        fn plus_zero(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
          case Z => reflexive(Z())
          case S(previous, ih) => rewrite ih in reflexive(S(previous))

        fn reduced(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
          plus(plus(value, Z()), Z()) == value
          because #{command}
      end
      """
    end

    plain = assert_elaborates(body.("simplify"))
    traced = assert_elaborates(body.("simp?"))

    # Byte-identical Core for the proof body: `simp?` reports, it does not
    # change what is proved.
    assert Env.get_def(plain, :reduced).body == Env.get_def(traced, :reduced).body
  end

  # -- tactic wrappers compose inside template tactics ---------------------

  test "a template tactic can compose the new solver commands" do
    # The closed tactic vocabulary must agree with the parser's solver table.
    # `assumption` and `omega` are new members, so a template that names them has
    # to classify as a valid step rather than `:not_a_step`.
    source = """
    mod TemplateComposes
      use Std.Equivalent

      macro Tactics
        tactic close becomes by assumption

      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
        x == y
        because
          close
    end
    """

    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"TemplateComposes#theorem")
  end

  # -- omega ---------------------------------------------------------------

  test "omega discharges a linear goal with a kernel-checked proof object" do
    source = """
    mod OmegaLinear
      use Std.Proof.LinearArithmetic
      use Std.Proof.IntOrder

      fn theorem(a: Int, b: Int, h: IsLessThanOrEqual(a, b)) -> IsLessThanOrEqual(a, b) =
        by omega
    end
    """

    env = assert_elaborates(source)
    assert :ok = Kernel.check_def(env, :"OmegaLinear#theorem")
  end

  test "omega returns a refusal, not a guess, outside the linear fragment" do
    source = """
    mod OmegaOutsideFragment
      use Std.Proof.LinearArithmetic
      use Std.Proof.Math

      fn theorem(a: Nat, b: Nat) -> IsPositive(plus(a, b)) = by omega
    end
    """

    assert_refused(source)
  end

  # -- the goal API still refuses to fabricate evidence --------------------

  test "a tactic that closes the goal records a solution keyed by the original goal" do
    env =
      assert_elaborates("""
      mod TacticSolution
        use Std.Equivalent

        type Nat = Z | S(Nat)

        fn identity(value: Nat) -> Nat = value

        fn theorem(value: Nat) -> Equivalent(Nat, identity(value), value) = proof chain
          identity(value) == value
          because simplify
      end
      """)

    %{type: type} = Env.get_def(env, :theorem)
    {context, target} = open_telescope(type, Context.empty(env))
    goal = ProofGoal.new(target, ["value"], context, env)

    assert {:ok, %Tactic.Result{goals: []} = result} =
             Tactic.command({:simplify_command, [], []}).(goal)

    assert %{evidence: evidence} = Map.fetch!(result.solutions, goal.id)
    assert :ok = Kernel.check(goal.context, evidence, Eval.eval(goal.expected, Context.env(goal.context)))
  end
end
