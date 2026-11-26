defmodule Cure.Elab.ApplicationSessionTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, ProofGoal, Tactic}
  alias Cure.Elab.Tactic.Result

  defp checks(body) do
    body = String.replace(body, "\n", "\n  ")

    source = """
    mod ApplicationSession
      use Std.Equivalent
      use Std.Nat
      #{body}
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"ApplicationSession#theorem")
    assert {:ok, checked_env} = Cure.Compiler.check_source(source)
    assert :ok = Kernel.check_def(checked_env, :"ApplicationSession#theorem")
    env
  end

  test "a partially supplied global theorem generates and checks its premise" do
    checks("""
    fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        apply need(x)
        reflexive(x)
    """)
  end

  test "independent premises are focused, ordered, and not broadcast" do
    checks("""
    fn need(x: Nat, y: Nat, h: Equivalent(Nat, x, x), k: Equivalent(Nat, y, y)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat, y: Nat) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        apply need(x, y)
        reflexive(x)
        reflexive(y)
    """)
  end

  test "dependent value witness stages a later proof domain" do
    checks("""
    fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, Z(), Z()) = reflexive(Z())
    fn theorem(y: Nat) -> Equivalent(Nat, Z(), Z()) = proof chain
      Z() == Z()
      because
        apply need
        y
        reflexive(y)
    """)
  end

  test "nested apply retains the outer sibling and original obligation" do
    checks("""
    fn one(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
    fn two(x: Nat, y: Nat, h: Equivalent(Nat, x, x), k: Equivalent(Nat, y, y)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat, y: Nat) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        apply two(x, y)
        apply one(x)
        reflexive(x)
        reflexive(y)
    """)
  end

  test "local theorem heads and constructor telescopes are real checked evidence" do
    checks("""
    fn theorem(
      x: Nat,
      f: (Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x)
    ) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        apply f
        apply reflexive
    """)
  end

  test "parent facts are materialized exactly once" do
    checks("""
    fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        have y = x
        apply need(y)
        reflexive(y)
    """)
  end

  test "parent solutions are absent while independent child identities remain open" do
    env = Env.empty()
    ctx = Context.empty(env)
    type = {:pi, :unrestricted, {:type, 0}, {:pi, :unrestricted, {:type, 0}, {:type, 0}}}
    ctx = Context.extend(ctx, Eval.eval(type, []))
    goal = ProofGoal.new({:type, 0}, ["f"], ctx, env)

    assert {:ok, %Result{goals: [a, b], pending: pending, solutions: %{}} = result} =
             Tactic.command({:proof_application, [kind: :apply], [{:variable, [], "f"}]}).(goal)

    refute a.id == b.id
    refute a.id == goal.id
    assert Map.has_key?(pending, goal.id)
    refute Tactic.closed?({:ok, result})
    assert a.root_expected == {:type, 0}
    assert b.root_expected == {:type, 0}
  end

  test "host focus preserves earlier siblings while nested application settles" do
    env = Env.empty()
    type = {:pi, :unrestricted, {:type, 0}, {:pi, :unrestricted, {:type, 0}, {:type, 0}}}
    ctx = Context.empty(env) |> Context.extend({:vtype, 0})
    ctx = Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    ctx = Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    goal = ProofGoal.new({:type, 0}, ["g", "f", "X"], ctx, env)
    apply_head = fn name -> Tactic.command({:proof_application, [kind: :apply], [{:variable, [], name}]}) end
    exact_x = Tactic.command({:proof_application, [kind: :exact], [{:variable, [], "X"}]})
    assert {:ok, %Result{goals: [first, _second]} = result} = apply_head.("f").(goal)
    assert {:ok, %Result{goals: [^first, _, _]} = result} = Tactic.focus(apply_head.("g"), 1).(result)
    assert {:ok, %Result{goals: [^first, _]} = result} = Tactic.focus(exact_x, 1).(result)
    assert {:ok, %Result{goals: [], pending: pending, solutions: solutions}} = Tactic.run_all(exact_x, result)
    assert pending == %{}
    assert %{evidence: evidence} = Map.fetch!(solutions, goal.id)
    assert :ok = Kernel.check(ctx, evidence, {:vtype, 0})
  end

  test "constructor fields use the constructor telescope and result" do
    checks("""
    type Both = MkBoth(Nat, Nat)
    fn need(pair: Both) -> Equivalent(Nat, Z(), Z()) = reflexive(Z())
    fn theorem(x: Nat, y: Nat) -> Equivalent(Nat, Z(), Z()) = proof chain
      Z() == Z()
      because
        apply need
        apply MkBoth
        exact x
        exact y
    """)
  end

  test "unresolved trans middle is a visible typed value obligation" do
    checks("""
    fn theorem(
      x: Nat, y: Nat, z: Nat,
      left: Equivalent(Nat, x, y), right: Equivalent(Nat, y, z)
    ) -> Equivalent(Nat, x, z) = proof chain
      x == z
      because
        apply trans
        exact y
        exact left
        exact right
    """)
  end

  test "a template can leave a staged session for following source statements" do
    checks("""
    macro Tactics
      tactic begin_proof becomes apply need
    fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, Z(), Z()) = reflexive(Z())
    fn theorem(x: Nat) -> Equivalent(Nat, Z(), Z()) = proof chain
      Z() == Z()
      because
        begin_proof
        exact x
        exact reflexive(x)
    """)
  end

  test "wrong, unfinished, erased-hole and post-closure proofs are refused" do
    for commands <- [
          "apply need(x)",
          "apply need(x)\n      reflexive(Z())",
          "apply need(x)\n      ?fake",
          "apply need(x)\n      reflexive(x)\n      reflexive(x)"
        ] do
      assert {:error, reason} =
               Program.elaborate("""
               mod RefuseApplication
                 use Std.Nat
                 use Std.Equivalent
                 fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
                 fn theorem(x: Nat) -> Equivalent(Nat, x, x) = proof chain
                   x == x
                   because
                     #{commands}
               end
               """)

      refute is_list(Program.semantic_error(reason))
    end
  end

  test "parent rewrites restore the original target only after application closes" do
    checks("""
    fn need(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat, y: Nat, equation: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) = proof chain
      x == y
      because
        rewrite using equation
        apply need(y)
        exact reflexive(y)
    """)
  end

  test "child rewrites and facts close at the child's original root" do
    checks("""
    fn need(x: Nat, y: Nat, h: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) = h
    fn theorem(x: Nat, y: Nat, equation: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, y) = proof chain
      x == y
      because
        apply need(x, y)
        have witness = y
        rewrite using equation
        exact reflexive(witness)
    """)
  end

  test "forged evidence is refused even when it occupies an erased application position" do
    alias Cure.Elab.Tactic.Apply

    for evidence <- [
          {:hole, "fake"},
          {:meta, 0},
          {:app, {:global, :discard}, {:hole, "erased"}},
          {:lam, :erased, {:type, 0}, {:meta, 0}},
          {:var, -1},
          {:app, :not_a_term, {:type, 0}}
        ] do
      assert {:error, :internal_application_hole} = Apply.concrete(evidence)
    end

    env = Env.empty()
    type = {:pi, :unrestricted, {:type, 0}, {:type, 0}}
    ctx = Context.extend(Context.empty(env), Eval.eval(type, []))
    goal = ProofGoal.new({:type, 0}, ["f"], ctx, env)

    assert {:ok, %Result{goals: [child], pending: pending}} =
             Tactic.command({:proof_application, [kind: :apply], [{:variable, [], "f"}]}).(goal)

    assert {:error, :internal_application_hole} =
             Apply.advance(Map.fetch!(pending, goal.id), %{child.id => %{evidence: {:hole, "fake"}, trace: []}})
  end

  test "the existing totality certificate refuses circular false evidence" do
    assert {:error, _} =
             Program.elaborate("""
             mod CircularApplication
               use Std.Nat
               use Std.Equivalent
               @total true
               fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
               fn theorem() -> Equivalent(Nat, Z(), S(Z())) = proof chain
                 Z() == S(Z())
                 because
                   apply loop()
             end
             """)
  end

  test "source unreachable statements label the actual closing premise" do
    source = """
    mod ApplicationClosureLocation
      use Std.Nat
      use Std.Equivalent
      fn need(x: Nat, y: Nat, h: Equivalent(Nat, x, x), k: Equivalent(Nat, y, y)) -> Equivalent(Nat, x, x) = h
      fn theorem(x: Nat, y: Nat) -> Equivalent(Nat, x, x) = proof chain
        x == x
        because
          apply need(x, y)
          exact reflexive(x)
          exact reflexive(y)
          exact reflexive(Z())
    end
    """

    assert {:error, reason} = Cure.Compiler.check_source(source)

    assert {:proof_chain_syntax, %{kind: :unreachable_proof_statement, construct: closed_at, step: extra}} =
             Program.semantic_error(reason)

    assert closed_at.start_line == 10
    assert extra.start_line == 11
    assert {:ok, env} = Cure.Compiler.check_source(String.replace(source, "      exact reflexive(Z())\n", ""))
    assert :ok = Kernel.check_def(env, :"ApplicationClosureLocation#theorem")
  end

  defp traced_application do
    env = Env.empty()
    type = {:pi, :unrestricted, {:type, 0}, {:pi, :unrestricted, {:type, 0}, {:type, 0}}}
    ctx = Context.empty(env) |> Context.extend({:vtype, 0})
    ctx = Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    ctx = Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    goal = ProofGoal.new({:type, 0}, ["g", "f", "X"], ctx, env)

    command = fn kind, name, line ->
      span = %Cure.Diagnostic.Span{
        source_id: "application-trace.cure",
        path: "application-trace.cure",
        start_byte: line,
        end_byte: line + 1,
        start_line: line,
        end_line: line,
        start_column: 1,
        end_column: 2
      }

      meta = [kind: kind, source_info: %Cure.MetaAST.SourceInfo{whole: span}]
      Tactic.command({:proof_application, meta, [{:variable, [], name}]})
    end

    {goal, command}
  end

  test "nested application root traces retain every premise exactly once" do
    {goal, command} = traced_application()
    assert {:ok, result} = command.(:apply, "f", 1).(goal)
    assert {:ok, result} = Tactic.run_focused(command.(:apply, "g", 2), result)
    assert {:ok, result} = Tactic.run_focused(command.(:exact, "X", 3), result)
    assert {:ok, result} = Tactic.run_focused(command.(:exact, "X", 4), result)

    assert {:ok, %Result{goals: [], pending: pending, solutions: solutions}} =
             Tactic.run_focused(command.(:exact, "X", 5), result)

    assert pending == %{}
    assert %{evidence: evidence, trace: trace} = Map.fetch!(solutions, goal.id)

    assert [{:apply, 1}, {:apply, 2}, {:exact, 3}, {:exact, 4}, {:exact, 5}] =
             Enum.map(trace, fn {kind, span} -> {kind, span.start_line} end)

    assert :ok = Kernel.check(goal.context, evidence, {:vtype, 0})
  end

  test "out-of-order host focus records actual premise completion order" do
    {goal, command} = traced_application()
    assert {:ok, result} = command.(:apply, "f", 1).(goal)
    assert {:ok, result} = Tactic.focus(command.(:exact, "X", 2), 1).(result)

    assert {:ok, %Result{goals: [], solutions: solutions}} =
             Tactic.run_focused(command.(:exact, "X", 3), result)

    assert %{trace: trace} = Map.fetch!(solutions, goal.id)

    assert [{:apply, 1}, {:exact, 2}, {:exact, 3}] =
             Enum.map(trace, fn {kind, span} -> {kind, span.start_line} end)
  end
end
