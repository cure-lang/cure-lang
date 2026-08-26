defmodule Cure.Compiler.TransparentObjectMacroTest do
  use ExUnit.Case, async: false

  test "typed actor state annotations reject mismatched callback bodies" do
    source = """
    macro TypedActor
      syntax typed_actor <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour gen_server
        typealias State = state_type
        callback init(initial: State) returns Tuple(Atom, State) = %[:ok, true]
    typed_actor Cure.InvalidTypedActor state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "typed fsm data annotations reject mismatched callback bodies" do
    source = """
    macro TypedFsm
      syntax typed_fsm <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour gen_statem
        typealias State = state_type
        callback init(initial: State) returns Tuple(Atom, Atom, State) = %[:ok, :initial, true]
    typed_fsm Cure.InvalidTypedFsm state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "typed app lifecycle annotations reject mismatched callback bodies" do
    source = """
    macro TypedApp
      syntax typed_app <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour application
        typealias State = state_type
        callback start(kind: t, args: State) returns Tuple(Atom, State) = %[:ok, true]
    typed_app Cure.InvalidTypedApp state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "a concrete Pid goal solves the erased type index of qualified self" do
    source = """
    mod Cure.ConcretePid
      use Std.Otp
      fn me() -> Effect(Pid(Atom)) = Std.Otp.self()
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert is_pid(apply(module, :me, []))
  end

  test "a concrete Pid goal solves the erased type index through beam_ops" do
    source = """
    mod Cure.ConcreteBeamOps
      use Std.Otp
      fn me() -> Effect(Pid(Atom)) = beam_ops self
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert is_pid(apply(module, :me, []))
  end

  test "supervisor child policies are closed typed values" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, Std.Supervisor.transient(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, []}, :transient, 1000, :worker, [:worker_module]}
  end

  test "supervisor child startup arguments preserve their checked element type" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Tuple(Std.Otp.Raw.RawTerm, Tuple(Atom, Atom, List(Int)), Atom, Nat, Atom, List(Atom)) =
        Std.Supervisor.child_with_args(:worker_module, :worker, [1], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, [1]}, :permanent, 1000, :worker, [:worker_module]}
  end

  test "supervisor child startup rejects a heterogeneous argument list" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> ChildSpec =
        Std.Supervisor.child_with_args(:worker_module, :worker, [1, :boot], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "heterogeneous supervisor arguments require explicit raw-term erasure" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Tuple(Std.Otp.Raw.RawTerm, Tuple(Atom, Atom, List(Std.Otp.Raw.RawTerm)), Atom, Nat, Atom, List(Atom)) =
        Std.Supervisor.child_with_raw_args(:worker_module, :worker, [Std.Supervisor.raw_arg(1), Std.Supervisor.raw_arg(:boot)], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, [1, :boot]}, :permanent, 1000, :worker, [:worker_module]}
  end

  test "raw child_spec syntax rejects unwrapped heterogeneous arguments" do
    source = "sup Cure.InvalidRawArgRoot children [child_spec Cure.ArgWorker :worker raw with [1, :boot]]\n"

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor child policies reject arbitrary restart atoms" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Std.Supervisor.ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, :permanent, Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategies lower from the closed Cure vocabulary" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_all(), 2, Std.Supervisor.more(9))
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :build, []) == {:one_for_all, 2, 10}
  end

  test "supervisor strategy conversion rejects arbitrary atoms" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(:one_for_all, 2, Std.Supervisor.more(9))
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategy policies reject negative intensity and period literals" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_one(), -1, 5)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategy policies reject a zero restart period" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_one(), 0, 0)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor shutdown policies reject unrestricted integer variables" do
    source = """
    mod Main
      use Std.Supervisor
      fn build(timeout: Int) -> ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(timeout), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor child constructors reject non-atom modules" do
    source = "sup Cure.InvalidChildRoot children [Std.Supervisor.child(1, :worker)]\n"

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "no per-container compiler modules remain in the lowering path" do
    refute Code.ensure_loaded?(Cure.Actor.Compiler)
    refute Code.ensure_loaded?(Cure.FSM.Compiler)
    refute Code.ensure_loaded?(Cure.Sup.Compiler)
    refute Code.ensure_loaded?(Cure.App.Compiler)
  end
end
