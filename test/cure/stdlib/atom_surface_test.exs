defmodule Cure.Stdlib.AtomSurfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "safe stdlib signatures do not regress to the removed atom shortcuts" do
    signatures = %{
      "lib/std/string.cure" => ["fn to_atom(s: String) -> Atom"],
      "lib/std/system.cure" => ["fn system_time(unit: Atom)", "fn system_info(key: Atom)"],
      "lib/std/process.cure" => [
        "fn link(pid: Pid) -> Atom",
        "fn unlink(pid: Pid) -> Atom",
        "fn exit(pid: Pid, reason: Atom)"
      ],
      "lib/std/io.cure" => ["fn println(text: String) -> Atom", "fn print(text: String) -> Atom"],
      "lib/std/gen.cure" => ["fn seed(_alg: Atom"],
      "lib/std/test.cure" => ["fn assert(condition: Bool) -> Atom", "fn forall(gen: Atom ->"],
      "lib/std/fsm.cure" => ["type Transition = Row(Atom, Atom, Atom)"],
      "lib/std/crdt.cure" => ["node: Atom"]
    }

    Enum.each(signatures, fn {file, forbidden} ->
      source = File.read!(file)

      Enum.each(forbidden, fn signature ->
        refute String.contains?(source, signature), "#{file} restored #{signature}"
      end)
    end)
  end

  test "closed system-time vocabulary rejects a raw atom" do
    assert {:error, _} =
             Program.elaborate("""
             mod BadTimeUnit
               use Std.System
               fn now() -> Int = system_time(:millisecond)
             """)
  end

  test "closed system-time vocabulary accepts TimeUnit" do
    assert {:ok, _} =
             Program.elaborate("""
             mod GoodTimeUnit
               use Std.System
               fn now() -> Int = system_time(Millisecond())
             """)
  end

  test "typed OTP exit requires ExitReason rather than a raw atom" do
    assert {:ok, _} =
             Program.elaborate("""
             mod GoodExitReason
               use Std.Otp
               use Std.ExitReason
               fn stop(pid: Pid(Atom)) -> Effect(Unit) = exit(pid, Shutdown())
             """)

    assert {:error, _} =
             Program.elaborate("""
             mod BadExitReason
               use Std.Otp
               use Std.ExitReason
               fn stop(pid: Pid(Atom)) -> Effect(Unit) = exit(pid, :shutdown)
             """)
  end

  test "retired unindexed process types fail in the signature that names them" do
    assert {:error, {:retired_process_type, %{name: :Pid, span: span}}} =
             Program.elaborate("""
             mod LegacyPid
               fn stale(pid: Pid) -> Pid = pid
             """)

    assert %Cure.Diagnostic.Span{start_line: 2, start_column: 17} = span
  end

  test "typed OTP monitoring rejects the raw BEAM kind atom" do
    assert {:ok, _} =
             Program.elaborate("""
             mod GoodMonitorKind
               use Std.Otp
               fn observe(pid: Pid(Atom)) -> Effect(MonitorRef) = monitor(Process(), pid)
             """)

    assert {:error, _} =
             Program.elaborate("""
             mod BadMonitorKind
               use Std.Otp
               fn observe(pid: Pid(Atom)) -> Effect(MonitorRef) = monitor(:process, pid)
             """)
  end

  test "FSM transition algebra accepts distinct application state and event types" do
    assert {:ok, _} =
             Program.elaborate("""
             mod TypedTransitions
               use Std.Fsm

               type Door = Open | Closed
               type Event = Push | Pull

               fn row() -> Transition(Door, Event) = transition(Closed(), Push(), Open())

               fn step(state: Door, event: Event) -> Tuple(Atom, Door, Int) =
                 dispatch([row()], state, event, 0)
             """)

    assert {:error, _} =
             Program.elaborate("""
             mod BadTypedTransition
               use Std.Fsm

               type Door = Open | Closed
               type Event = Push | Pull

               fn bad() -> Transition(Door, Event) = transition(Closed(), Push(), Push())
             """)
  end

  test "safe atom lookup preserves existing atoms without interning input" do
    # Called at the BEAM level, so the argument is the erasure of the nominal
    # `String` record — `{:String, charlist}`, not a bare charlist.
    assert :ok = :"Cure.Std.String".to_existing_atom({:String, ~c"ok"})

    unknown = "cure_atom_surface_#{System.unique_integer([:positive])}"

    assert_raise ArgumentError, fn ->
      apply(:"Cure.Std.String", :to_existing_atom, [{:String, String.to_charlist(unknown)}])
    end

    assert_raise ArgumentError, fn -> String.to_existing_atom(unknown) end
  end

  test "effect-typed process compatibility operations discard BEAM success atoms as Unit" do
    assert :unit = :"Cure.Std.Process".link(self())
    assert :unit = :"Cure.Std.Process".unlink(self())
  end

  test "timestamp wrappers still call BEAM with the correct atom encoding" do
    now = :"Cure.Std.System".timestamp_ms()
    assert is_integer(now)
    assert now > 0
  end

  test "system halt does not expose an undifferentiated result atom" do
    assert {:ok, _} =
             Program.elaborate("""
             mod TypedResults
               use Std.System

               fn halt_status(code: Int) -> Unit = Std.System.exit(code)
             """)
  end
end
