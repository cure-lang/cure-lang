defmodule Cure.Elab.TacticMacroAuditTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Kernel}
  alias Cure.Elab.{Program, ProofGoal, Tactic}
  alias Cure.Elab.Tactic.{Result, Step}

  defp checked!(source, name \\ :theorem) do
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, name))
    env
  end

  test "forward parameterized aliases and distinct overloads can compose" do
    checked!("""
    mod ForwardTacticAliases
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because wrapped reflexive(x)
      macro Tactics
        tactic wrapped <e: Code> becomes finish with e
        tactic finish with <e: Code> becomes finish e
        tactic finish <e: Code> becomes exact e
    end
    """)
  end

  test "cyclic template expansion is refused instead of recursing forever" do
    assert {:error, _} =
             Program.elaborate("""
             mod CyclicTacticAliases
               macro Tactics
                 tactic first becomes second
                 tactic second becomes first
               fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
                 x == x
                 because first
             end
             """)
  end

  test "a rewrite-only tactic composes with the next caller command and preserves Core bytes" do
    env =
      checked!("""
      mod PartialTactic
        macro Tactics
          tactic move <e: Code> becomes rewrite using e all
        type Pair = Pair(Int, Int)
        fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) = proof chain
          Pair(x, x) == Pair(y, y)
          because
            move h
            simplify
        fn direct(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) = proof chain
          Pair(x, x) == Pair(y, y)
          because
            rewrite using h all
            simplify
      end
      """)

    assert :erlang.term_to_binary(Env.get_def(env, :theorem).body) ==
             :erlang.term_to_binary(Env.get_def(env, :direct).body)
  end

  test "a final open tactic reports the transformed residual goal" do
    assert {:error, {:source_context, {:proof_chain_mismatch, problem}, _}} =
             Program.elaborate("""
             mod OpenTactic
               macro Tactics
                 tactic move <e: Code> becomes rewrite using e
               fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
                 x == y
                 because move h
             end
             """)

    assert problem.kind == :unfinished_justification
    assert {:data, _, [{:level_value, _}, _], [endpoint, endpoint]} = problem.residual_goal
  end

  test "statements after a script closes are rejected instead of silently skipped" do
    assert {:error, {:source_context, {:proof_chain_syntax, problem}, _}} =
             Program.elaborate("""
             mod DeadTacticCommand
               macro Tactics
                 tactic close becomes
                   simplify
                   exact missing_proof
               fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
                 x == x
                 because close
             end
             """)

    assert problem.kind == :unreachable_proof_statement
  end

  test "nested tactic aliases execute in either declaration order" do
    for rules <- [
          "tactic close becomes simplify\n    tactic wrapped becomes close",
          "tactic wrapped becomes close\n    tactic close becomes simplify"
        ] do
      checked!("""
      mod NestedTactic
        macro Tactics
          #{rules}
        fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
          x == x
          because wrapped
      end
      """)
    end
  end

  test "tactics really execute directly in induction arms" do
    checked!("""
    mod TacticInductionArms
      macro Tactics
        tactic close becomes simplify
        tactic finish <e: Code> becomes exact e
      type Nat = Z | S(Nat)
      fn theorem(n: Nat) -> Equivalent(Nat, n, n) = induction n
        case Z => close
        case S(k, ih) => finish reflexive(S(k))
    end
    """)
  end

  test "a closing tactic cannot replace its original obligation without a transport" do
    env = checked!("mod OriginalTacticGoal\n  fn theorem(x: Int) -> Equivalent(Int, x, x) = reflexive(x)\nend")
    context = Context.empty(env)
    false_goal = Cure.Elab.Rewrite.mk_eq({:data, :"Std.Int#Int", [], []}, {:int_lit, 0}, {:int_lit, 1})
    goal = ProofGoal.new(false_goal, [], context, env)
    forged = %{goal | expected: Cure.Elab.Rewrite.mk_eq({:data, :"Std.Int#Int", [], []}, {:int_lit, 0}, {:int_lit, 0})}
    command = {:tactic_script, [keyword: "close"], [{:simplify_command, [], []}]}
    assert {:error, _} = Tactic.command(command).(forged)
  end

  test "nested tactic closure does not duplicate the caller's trace" do
    env = checked!("mod TacticTrace\n  fn theorem(x: Int) -> Equivalent(Int, x, x) = reflexive(x)\nend")
    expected = Cure.Elab.Rewrite.mk_eq({:data, :"Std.Int#Int", [], []}, {:int_lit, 0}, {:int_lit, 0})
    goal = %{ProofGoal.new(expected, [], Context.empty(env), env) | trace: [{:prior, nil}]}
    command = {:tactic_script, [keyword: "close"], [{:simplify_command, [], []}]}
    assert {:ok, %Result{goals: [], solutions: solutions}} = Tactic.command(command).(goal)
    assert %{trace: [{:prior, nil}, {:simplify_definitional, _}]} = Map.fetch!(solutions, goal.id)
  end

  test "empty blocks, malformed commands, and actual Core nodes are refused structurally" do
    assert {:error, :empty_tactic_body} = Step.classify({:block, [], []})

    core_lambda =
      {:lam, :unrestricted, {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}, {:var, 0}}

    assert Cure.Core.Term.term?(core_lambda)

    for node <- [
          {:proof_application, nil, [{:variable, [], "h"}]},
          {:proof_application, [kind: :bogus], [{:variable, [], "h"}]},
          {:simplify_command, [using: :proof], []},
          {:simplify_command, [], [{:list, [], :bad}]},
          {:solver_command, [solver: :bogus], []},
          {:tactic_script, [:bad], [{:simplify_command, [], []}]},
          {:block, [:bad], [{:simplify_command, [], []}]},
          {:rewrite_command, [direction: :forward, target: :bogus], [{:variable, [], "h"}]},
          {:app, {:global, :f}, {:var, 0}},
          core_lambda,
          {:data, :Forged, [], []}
        ] do
      assert {:error, _} = Step.classify(node)
    end
  end

  test "an induction template executes and uses its recursive hypothesis" do
    env =
      checked!("""
      mod CheckedInductionTemplate
        use Std.Equivalent
        type Nat = Z | S(Nat)
        fn plus(left: Nat, right: Nat) -> Nat = match left
          Z() -> right
          S(k) -> S(plus(k, right))

        macro Tactics
          tactic induct <value: Code> becomes induction value
            case Z => simplify
            case S(previous, ih) => simplify using [ih]

        fn theorem(n: Nat) -> Equivalent(Nat, plus(n, Z()), n) = proof chain
          plus(n, Z()) == n
          because induct n
      end
      """)

    assert :ok = Cure.Core.Kernel.check_def(env, :"CheckedInductionTemplate#theorem")
    assert Cure.Core.Env.total?(env, :"CheckedInductionTemplate#theorem")
  end
end
