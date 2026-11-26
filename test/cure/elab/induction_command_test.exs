defmodule Cure.Elab.InductionCommandTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Context, Env, Eval, Kernel, Validator}
  alias Cure.Elab.{Program, ProofGoal, ProofState, Tactic}
  alias Cure.Elab.Induction.Frame
  alias Cure.Elab.Tactic.{Result, Step}

  @plus """
  type Nat = Z | S(Nat)
  fn plus(left: Nat, right: Nat) -> Nat = match left
    Z() -> right
    S(previous) -> S(plus(previous, right))
  """

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp checked!(source, name \\ :theorem) do
    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, name)
    assert Env.total?(env, name)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, name))
    env
  end

  test "a real induction template uses the recursive IH for plus-zero-right" do
    source = """
    mod TemplateInductionCommand
      macro Tactics
        tactic prove_zero <n: Code> becomes induction n
          case Z => simplify
          case S(previous, induction_hypothesis) =>
            simplify using [induction_hypothesis]
      #{String.replace(@plus, "\n", "\n  ")}
      fn theorem(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = proof chain
        plus(value, Z) == value
        because prove_zero value
    end
    """

    env = checked!(source)
    body = Env.get_def(env, :theorem).body
    assert Enum.any?(Validator.nodes(body), &match?({:global, :"TemplateInductionCommand#theorem"}, &1))
    refute Enum.any?(Validator.nodes(body), &match?({:hole, _}, &1))
  end

  test "ordinary top-level induction and each branch really execute goal commands" do
    source = """
    mod BranchCommandInduction
      #{String.replace(@plus, "\n", "\n  ")}
      fn theorem(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
        case Z => exact reflexive(Z)
        case S(previous, induction_hypothesis) =>
          have step: Equivalent(Nat, plus(previous, Z), previous) = induction_hypothesis
          rewrite using step
          simplify
    end
    """

    {{:ok, env}, states} = ProofState.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :theorem))
    before = Enum.filter(states, &(&1.phase == :before))
    assert [_root, _zero_branch, _ih, _have, _rewrite, _simplify | _] = before
    assert MapSet.size(MapSet.new(before, & &1.id)) == 3

    assert Enum.any?(before, fn state ->
             Enum.any?(state.goals, fn goal ->
               Enum.any?(goal.hypotheses, &(&1.name == "induction_hypothesis"))
             end)
           end)
  end

  test "prelifted nonparameter induction remains an exact checked helper call inside a tactic" do
    env =
      checked!("""
      mod LiftedTemplateInductionCommand
        macro Tactics
          tactic prove_successor <n: Code> becomes induction S(n)
            case Z => exact reflexive(Z)
            case S(previous, ih) => exact reflexive(S(previous))
        type Nat = Z | S(Nat)
        fn theorem(value: Nat) -> Equivalent(Nat, S(value), S(value)) = proof chain
          S(value) == S(value)
          because prove_successor value
      end
      """)

    helper = :"LiftedTemplateInductionCommand#__induction_theorem_1"
    assert Env.certified?(env, helper)
    assert :ok = Kernel.check_def(env, helper)
  end

  test "template case binders are hygienic and explicit captures remain outside them" do
    checked!("""
    mod HygienicInductionCommand
      macro Tactics
        tactic prove <n: Code> becomes induction n
          case Z => exact reflexive(<capture outside>)
          case S(outside, ih) => exact reflexive(<capture outside>)
      type Nat = Z | S(Nat)
      fn theorem(outside: Nat, value: Nat) -> Equivalent(Nat, outside, outside) = proof chain
        outside == outside
        because prove value
    end
    """)
  end

  test "ordinary branch lets and proof chains retain expression semantics" do
    checked!("""
    mod InductionExpressionBranches
      type Nat = Z | S(Nat)
      fn theorem(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z =>
          let saved = Z
          reflexive(saved)
        case S(previous, ih) => proof chain
          S(previous) == S(previous)
          because simplify
    end
    """)
  end

  test "a tree template receives two checked hypotheses in constructor field order" do
    checked!("""
    mod TreeTemplateInductionCommand
      macro Tactics
        tactic rebuild <tree: Code> becomes induction tree
          case Leaf => simplify
          case Node(left, right, left_ih, right_ih) => simplify using [left_ih, right_ih]
      type Tree = Leaf | Node(Tree, Tree)
      fn copy(tree: Tree) -> Tree = match tree
        Leaf() -> Leaf()
        Node(left, right) -> Node(copy(left), copy(right))
      fn theorem(tree: Tree) -> Equivalent(Tree, copy(tree), tree) = proof chain
        copy(tree) == tree
        because rebuild tree
    end
    """)
  end

  test "indexed templates preserve the ordinary impossible-case check" do
    checked!("""
    mod IndexedTemplateInductionCommand
      macro Tactics
        tactic prove <w: Code> becomes induction w
          case szero => exact reflexive(Z)
          case ssuc(index, previous, ih) => impossible
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      fn theorem(witness: SNat(Z)) -> Equivalent(Nat, Z, Z) = proof chain
        Z == Z
        because prove witness
    end
    """)
  end

  defp standalone_goal do
    env =
      checked!("""
      mod StandaloneInductionCommand
        type Nat = Z | S(Nat)
        fn theorem(value: Nat) -> Equivalent(Nat, value, value) = reflexive(value)
      end
      """)

    definition = Env.get_def(env, :theorem)
    {:pi, grade, domain, expected} = definition.type
    env = Env.with_current_def(env, :theorem)
    context = Context.extend(Context.empty(env), Eval.eval(domain, []), grade)

    signature = %{
      name: :theorem,
      params: [{:param, [type: {:variable, [], "Nat"}], "value"}],
      telescope: [{:value, domain}],
      scope: ["value"],
      quantities: [grade],
      plicities: [:explicit],
      return_core: expected,
      pi: definition.type,
      inferred_return: false
    }

    frame = Frame.new(signature, context, env)
    goal = ProofGoal.new(expected, ["value"], context, env, [], declaration_frame: frame)

    command =
      parse!(
        "induction value\n  case Z => exact reflexive(Z)\n  case S(previous, ih) => exact reflexive(S(previous))\n"
      )

    {goal, command}
  end

  test "standalone goal plus an explicit canonical frame produces kernel-checked evidence" do
    {goal, command} = standalone_goal()
    assert Frame.current() == nil
    assert {:ok, %Result{goals: [], solutions: solutions}} = Tactic.command(command).(goal)
    assert %{evidence: evidence} = Map.fetch!(solutions, goal.id)
    assert :ok = Kernel.check(goal.context, evidence, Eval.eval(goal.expected, Context.env(goal.context)))
    assert Frame.current() == nil
  end

  test "missing, foreign, and wrong-motive frames refuse without leaking scoped state" do
    {goal, command} = standalone_goal()

    for {invalid, kind} <- [
          {%{goal | declaration_frame: nil}, :missing_declaration_frame},
          {%{goal | env: Env.with_current_def(goal.env, :other)}, :foreign_declaration_frame},
          {%{goal | expected: {:data, :"StandaloneInductionCommand#Nat", [], []}}, :unsupported_induction_motive}
        ] do
      assert {:error, {:induction_failed, %{kind: ^kind}}} = Tactic.command(command).(invalid)
      assert Frame.current() == nil
    end
  end

  test "nested frame scopes restore on both return and exception" do
    {goal, _command} = standalone_goal()
    frame = goal.declaration_frame

    Frame.within(frame, fn ->
      assert Frame.current() == frame
      assert_raise RuntimeError, fn -> Frame.within(nil, fn -> raise "failed nested elaboration" end) end
      assert Frame.current() == frame
    end)

    assert Frame.current() == nil
  end

  test "induction template structural validation refuses malformed cases and Core bodies" do
    subject = {:variable, [], "value"}
    assert {:error, _} = Step.classify({:induction, [], [subject]})

    for invalid <- [
          {:induction_case, [], [subject]},
          {:induction_case, [], [subject, {:global, :forged}]},
          {:induction_case, [], [subject, nil]},
          {:induction_case, [], [{:ctor, :S, []}, {:simplify_command, [], []}]}
        ] do
      assert {:error, _} = Step.classify({:induction, [], [subject, invalid]})
    end
  end

  test "an induction branch cannot silently accept commands after closure" do
    assert {:error, reason} =
             Program.elaborate("""
             mod DeadInductionCommand
               type Nat = Z | S(Nat)
               fn theorem(value: Nat) -> Equivalent(Nat, value, value) = induction value
                 case Z =>
                   simplify
                   exact missing
                 case S(previous, ih) => exact reflexive(S(previous))
             end
             """)

    assert {:proof_chain_syntax, %{kind: :unreachable_proof_statement}} =
             reason |> then(fn {:source_context, semantic, _} -> semantic end)
  end

  test "ordinary totality certification rejects nondecreasing induction command recursion" do
    assert {:error, {:total_required_by_decorator, :"NondecreasingInductionCommand#theorem"}} =
             """
             mod NondecreasingInductionCommand
               type Nat = Z | S(Nat)
               @total true
               fn theorem(value: Nat) -> Nat = induction value
                 case Z => exact theorem(Z)
                 case S(previous, ih) => exact ih
             end
             """
             |> Program.elaborate()
             |> Program.semantic_result()
  end

  test "induction does not prove a false base case or release a surviving proof hole" do
    source = """
    mod InductionReleaseFirewall
      type Nat = Z | S(Nat)
      fn theorem(value: Nat) -> Equivalent(Nat, Z, S(Z)) = induction value
        case Z => BASE_COMMAND
        case S(previous, ih) => exact ih
    end
    """

    assert {:error, {:simplification_failed, _}} =
             source
             |> String.replace("BASE_COMMAND", "simplify")
             |> Program.elaborate()
             |> Program.semantic_result()

    assert {:ok, env} =
             source |> String.replace("BASE_COMMAND", "?unproved_base") |> Program.elaborate()

    assert Enum.any?(Validator.nodes(Env.get_def(env, :theorem).body), &match?({:hole, _}, &1))

    assert {:error, {:unfilled_hole, _}} =
             Cure.Elab.Emit.compile_forms(env, :InductionReleaseFirewall, [
               :"InductionReleaseFirewall#theorem"
             ])
  end

  test "the checked command preserves ordinary recursive match Core bytes" do
    declaration = """
    mod InductionCoreParity
      #{String.replace(@plus, "\n", "\n  ")}
      fn theorem(value: Nat) -> Equivalent(Nat, plus(value, Z), value) =
    """

    induction =
      checked!(
        declaration <>
          """
            induction value
              case Z => reflexive(Z)
              case S(previous, ih) => rewrite ih in reflexive(S(previous))
          end
          """
      )

    ordinary =
      checked!(
        declaration <>
          """
            match value
              Z() -> reflexive(Z)
              S(previous) ->
                let ih = theorem(previous)
                rewrite ih in reflexive(S(previous))
          end
          """
      )

    assert :erlang.term_to_binary(Env.get_def(induction, :theorem).body) ==
             :erlang.term_to_binary(Env.get_def(ordinary, :theorem).body)
  end
end
