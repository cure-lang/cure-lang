defmodule Cure.Elab.SourceSessionObservationTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Kernel}
  alias Cure.Elab.{Program, ProofGoal, ProofState, SourceContext}

  @application """
  mod ObservedSession
    use Std.Nat
    use Std.Equivalent
    fn one(x: Nat, h: Equivalent(Nat, x, x)) -> Equivalent(Nat, x, x) = h
    fn two(x: Nat, y: Nat, h: Equivalent(Nat, x, x), k: Equivalent(Nat, y, y)) -> Equivalent(Nat, x, x) = h
    fn theorem(x: Nat, y: Nat) -> Equivalent(Nat, x, x) = proof chain
      x == x
      because
        apply two(x, y)
        apply one(x)
        exact reflexive(x)
        exact reflexive(y)
  end
  """

  @induction """
  mod ObservedInductionSession
    type Nat = Z | S(Nat)
    fn theorem(value: Nat) -> Equivalent(Nat, value, value) = induction value
      case Z => exact reflexive(Z)
      case S(previous, ih) =>
        have witness = previous
        exact reflexive(S(previous))
  end
  """

  test "nested application publishes one authoritative pair per command and the whole frontier" do
    assert {{:ok, env}, context} = SourceContext.analyze(@application)
    states = context.observations
    assert Enum.map(states, & &1.phase) == [:before, :after, :before, :after, :before, :after, :before, :after]
    assert Enum.all?(states, &(&1.kind == :session))
    assert :ok = Kernel.check_def(env, :"ObservedSession#theorem")
    assert [] = SourceContext.remaining(context)

    assert [%{goal: "Equivalent(Nat, x, x)"}, %{goal: "Equivalent(Nat, y, y)"}] =
             SourceContext.at(context, position(@application, "apply one(x)", :end))

    assert [%{goal: "Equivalent(Nat, y, y)"}] =
             SourceContext.at(context, position(@application, "exact reflexive(x)", :end))

    assert [] = SourceContext.at(context, position(@application, "exact reflexive(y)", :end))
  end

  test "an unfinished nested application retains all concrete siblings once" do
    unfinished = String.replace(@application, "      exact reflexive(x)\n      exact reflexive(y)\n", "")
    assert {{:error, reason}, context} = SourceContext.analyze(unfinished)
    assert {:proof_chain_mismatch, %{kind: :unfinished_justification}} = Program.semantic_error(reason)
    assert %{phase: :unfinished, kind: :session, goals: [_, _]} = List.last(context.observations)
    assert [%{goal: "Equivalent(Nat, x, x)"}, %{goal: "Equivalent(Nat, y, y)"}] = SourceContext.remaining(context)
  end

  test "branch cursors choose authored inner commands and keep IH context at command ends" do
    assert {{:ok, env}, context} = SourceContext.analyze(@induction)
    assert :ok = Kernel.check_def(env, :"ObservedInductionSession#theorem")
    before = SourceContext.at(context, position(@induction, "exact reflexive(S(previous))"))
    assert [%{context: names}] = before
    assert Enum.any?(names, &String.starts_with?(&1, "ih : Equivalent"))
    assert "witness : Nat" in names
    assert [] = SourceContext.at(context, position(@induction, "exact reflexive(S(previous))", :end))

    failed = String.replace(@induction, "exact reflexive(S(previous))", "exact missing")
    assert {{:error, _}, failed_context} = SourceContext.analyze(failed)

    assert [%{goal: target, context: failed_names}] =
             SourceContext.at(failed_context, position(failed, "exact missing", :end))

    assert target =~ "previous"
    assert Enum.any?(failed_names, &String.starts_with?(&1, "ih : Equivalent"))
    assert "witness : Nat" in failed_names
  end

  test "session scopes restore after nested returns and exceptions, leaving standalone observations active" do
    env = Env.empty()
    goal = ProofGoal.new({:type, 0}, [], Context.empty(env), env)
    statement = {:variable, [], "standalone"}

    assert {:ok, [state]} =
             ProofState.capture(fn ->
               ProofState.with_session(fn ->
                 ProofState.observe(:before, statement, goal, [goal])
                 ProofState.with_session(fn -> ProofState.observe(:after, statement, goal, []) end)

                 assert_raise RuntimeError, fn ->
                   ProofState.with_session(fn -> raise "restore session" end)
                 end

                 ProofState.observe(:after, statement, goal, [])
               end)

               ProofState.observe(:before, statement, goal, [goal])
             end)

    assert state.kind == :command
    assert state.phase == :before
  end

  test "blocked pending application refusal exposes its concrete root rather than apparent closure" do
    env = Env.empty()
    goal = ProofGoal.new({:type, 0}, [], Context.empty(env), env)

    assert {{:error, {:proof_chain_mismatch, problem}}, [state]} =
             ProofState.capture(fn -> ProofGoal.pending_application(goal, 2) end)

    assert problem.kind == :unfinished_justification
    assert problem.cause == :pending_application
    assert problem.step_index == 2
    assert [%{goal: "Type"}] = state.goals
    assert state.phase == :unfinished
    assert state.kind == :session
  end

  @tag :tmp_dir
  test "source-imported template steps stay at the caller despite overlapping provider byte offsets", %{tmp_dir: root} do
    consumer = """
    mod LocalObservedTemplate
      use RemoteObservedTemplate
      # Padding keeps the authored consumer command after the provider command offset.
      # Additional caller-only text makes coincident provider offsets deliberately possible.
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because
          have local_marker = 4
          remote_close reflexive(x)
    end
    """

    provider = """
    mod RemoteObservedTemplate
      macro Rules
        tactic remote_close <e: Code> becomes
          have provider_marker = 7
          exact e
    end
    """

    {consumer_byte, _} = :binary.match(consumer, "have local_marker")
    {provider_byte, _} = :binary.match(provider, "have provider_marker")
    padding = consumer_byte - provider_byte - 2
    assert padding > 0
    provider = "#" <> String.duplicate("p", padding) <> "\n" <> provider
    assert {^consumer_byte, _} = :binary.match(provider, "have provider_marker")
    provider_file = Path.join(root, "provider.cure")
    consumer_file = Path.join(root, "consumer.cure")
    File.write!(provider_file, provider)
    File.write!(consumer_file, consumer)

    assert {{:ok, checked}, snapshots} =
             ProofState.capture(fn ->
               Cure.Compiler.ModulePipeline.check([consumer_file, provider_file],
                 package: "source_identity",
                 source_roots: [root]
               )
             end)

    env = Map.fetch!(checked.body_envs, {"source_identity", "LocalObservedTemplate"})

    context = %SourceContext{
      file: consumer_file,
      text: consumer,
      hash: :crypto.hash(:sha256, consumer),
      status: :checked,
      observations: snapshots
    }

    assert :ok = Kernel.check_def(env, :"LocalObservedTemplate#theorem")

    before = SourceContext.at(context, position(consumer, "have local_marker"))
    assert [%{context: before_names}] = before
    refute Enum.any?(before_names, &String.contains?(&1, "provider_marker"))
    assert [%{context: invocation_names}] = SourceContext.at(context, position(consumer, "remote_close"))
    assert "local_marker : Int" in invocation_names
    refute Enum.any?(invocation_names, &String.contains?(&1, "provider_marker"))
    assert [] = SourceContext.at(context, position(consumer, "remote_close reflexive(x)", :end))

    assert Enum.all?(context.observations, fn state ->
             Enum.all?([state.span, state.scope], &(is_nil(&1) or &1.source_id == consumer_file))
           end)
  end

  defp position(source, needle, endpoint \\ :start) do
    {byte, size} = :binary.match(source, needle)
    prefix = binary_part(source, 0, byte + if(endpoint == :end, do: size, else: 0))
    lines = String.split(prefix, "\n")
    %{"line" => length(lines) - 1, "character" => String.length(List.last(lines))}
  end
end
