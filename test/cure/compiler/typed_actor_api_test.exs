defmodule Cure.Compiler.TypedActorApiTest do
  use ExUnit.Case, async: false

  test "generated actor API starts, folds typed messages, answers requests, and stops" do
    source = """
    mod TypedActorDefinition
      use Std.Actor

      actor Cure.Generated.TypedCounter
        state Int
        on_cast
          Inc -> state + 1
        on_call Read() returns Int
          reply state

    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.TypedCounter"
    assert {:Started, pid} = apply(actor, :start, [0])

    assert :unit = apply(actor, :send, [pid, :Inc])
    assert :unit = apply(actor, :send, [pid, :Inc])
    assert 2 = apply(actor, :read, [pid])
    assert :unit = apply(actor, :stop, [pid])
    refute Process.alive?(pid)
  end

  test "generated send rejects values outside the actor message protocol" do
    source = """
    mod WrongTypedActorDefinition
      use Std.Actor

      actor Cure.Generated.TypedCounterNegative
        state Int
        on_cast
          Inc -> state + 1
        body
          fn wrong(handle: Handle) -> Effect(Unit) = send(handle, 42)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "on_message derives payload-bearing constructors and folds record updates" do
    source = """
    mod PayloadActorDefinition
      use Std.Actor

      rec CounterState
        count: Int
        touched: Bool

      actor Cure.Generated.PayloadCounter
        state CounterState
        initial CounterState{count: 0, touched: false}
        on_message
          Add(amount: Int) -> CounterState{
            state |
            count: state.count + amount,
            touched: true
          }
          Reset() -> CounterState{state | count: 0, touched: false}
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.PayloadCounter"
    assert {:Started, pid} = apply(actor, :start, [])

    assert :unit = apply(actor, :send, [pid, {:Add, 7}])
    assert :sys.get_state(pid) == {:CounterState, 7, true}
    assert :unit = apply(actor, :send, [pid, :Reset])
    assert :sys.get_state(pid) == {:CounterState, 0, false}
    assert :unit = apply(actor, :stop, [pid])
  end

  test "an explicit reply family gives one actor request-specific reply types" do
    source = """
    mod DependentActorDefinition
      use Std.Actor

      actor Cure.Generated.DependentCounter
        state Int
        initial 3
        on_message
          Increment() -> state + 1
        on_call Count() returns CountResult
          reply CountReply(state)
        on_call Ping() returns AckResult
          reply Ack()
        body
          type CountResult = CountReply(Int)
          type AckResult = Ack
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.DependentCounter"
    assert {:Started, pid} = apply(actor, :start, [])

    assert {:CountReply, 3} = apply(actor, :count, [pid])
    assert :Ack = apply(actor, :ping, [pid])
    assert :unit = apply(actor, :send, [pid, :Increment])
    assert {:CountReply, 4} = apply(actor, :count, [pid])
    assert :unit = apply(actor, :stop, [pid])
  end

  test "dependent actor queries reject a reply from another request branch" do
    source = """
    mod InvalidDependentActorDefinition
      use Std.Actor

      actor Cure.Generated.InvalidDependentCounter
        state Int
        on_message
          Increment() -> state + 1
        on_call Count() returns CountResult
          reply Ack()
        on_call Ping() returns AckResult
          reply Ack()
        body
          type CountResult = CountReply(Int)
          type AckResult = Ack
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "payload-bearing named queries can update state explicitly" do
    source = """
    mod UpdatingQueryActorDefinition
      use Std.Actor

      actor Cure.Generated.UpdatingQueryCounter
        state Int
        initial 1
        on_message
          Reset() -> 0
        on_call AddAndRead(amount: Int) returns Int
          reply state + amount
          update state + amount
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.UpdatingQueryCounter"
    assert {:Started, pid} = apply(actor, :start, [])
    assert 4 = apply(actor, :addAndRead, [pid, 3])
    assert 6 = apply(actor, :addAndRead, [pid, 2])
    assert :unit = apply(actor, :stop, [pid])
  end

  test "a query-only actor gets the same call surface as one that also casts" do
    # No `on_message` and no `on_cast`, so this goes down the raw branch of
    # `derive_actor_family`. That branch used to ignore `definition.queries`
    # outright: the module compiled clean, exported neither `handle_call/3` nor
    # any adapter, and the `on_call` clauses vanished without a diagnostic.
    source = """
    use Std.Actor

    actor QueryOnlyCounter
      state Int
      initial 7
      on_call Value() returns Int
        reply state
      on_call Bump(step: Int) returns Int
        reply state + step
        update state + step
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Main.QueryOnlyCounter"
    assert {:handle_call, 3} in actor.module_info(:exports)

    assert {:Started, pid} = apply(actor, :start, [])
    assert 7 = apply(actor, :value, [pid])
    assert 12 = apply(actor, :bump, [pid, 5])
    assert 12 = apply(actor, :value, [pid])
    assert :unit = apply(actor, :stop, [pid])
    refute Process.alive?(pid)
  end

  test "typed lifecycle hooks transform startup state and receive ExitReason on stop" do
    source = """
    mod LifecycleActorDefinition
      use Std.Actor

      actor Cure.Generated.LifecycleCounter
        state Int
        initial 4
        on_start state + 1
        on_message
          Increment() -> state + 1
        on_call Value() returns Int
          reply state
        on_stop
          match reason
            Normal() -> :ok
            Kill() -> :ok
            Shutdown() -> :ok
            Because(_) -> :ok
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.LifecycleCounter"
    assert {:Started, pid} = apply(actor, :start, [])
    assert 5 = apply(actor, :value, [pid])
    assert :unit = apply(actor, :stop, [pid])
    refute Process.alive?(pid)
  end
end
