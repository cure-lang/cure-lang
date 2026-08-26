defmodule Cure.Compiler.LiftedModuleMemberResolutionTest do
  @moduledoc """
  A `fsm`/`actor`/`sup` declared inside a `mod` is compiled to a *separate*
  BEAM module -- `mod Demo` containing `fsm Machine` emits `Cure.Demo` and
  `Cure.Demo.Machine`. The members that lifting synthesises (the `Event` type,
  `init/1`, ...) live in that second module, so the only way for `Demo` to name
  them is qualified: `Machine.Event`.

  That failed with `{:bad_projection, "Event"}`, because qualified module
  resolution loads interfaces from *source files* via the module index, and a
  lifted module has no source file of its own.
  """
  use ExUnit.Case, async: false

  defp compile(source) do
    Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  describe "a lifted module's members are nameable from the module that declares it" do
    test "an fsm's Event type resolves under its bare name" do
      assert {:ok, _} =
               compile("""
               mod LmDemoA
                 use Std.Fsm

                 fsm Machine
                   state Int
                   events
                     Tick -> :keep_state_and_data

                 fn describe(e: Machine.Event) -> Int = 1
               """)
    end

    test "an fsm's Event type resolves under its fully qualified name" do
      assert {:ok, _} =
               compile("""
               mod LmDemoB
                 use Std.Fsm

                 fsm Machine
                   state Int
                   events
                     Tick -> :keep_state_and_data

                 fn describe(e: LmDemoB.Machine.Event) -> Int = 1
               """)
    end

    test "an fsm's generated function is callable from the declaring module" do
      assert {:ok, _} =
               compile("""
               mod LmDemoC
                 use Std.Fsm

                 fsm Machine
                   state Int
                   events
                     Tick -> :keep_state_and_data

                 fn mode() -> Atom = Machine.callback_mode()
               """)

      assert apply(:"Cure.LmDemoC", :mode, []) == :handle_event_function
    end

    test "a consumer of the lifted module is not copied back into the lift" do
      assert {:ok, _} =
               compile("""
               mod LmDemoConsumer
                 use Std.Fsm
                 use Std.Otp

                 fsm Machine with Int
                   Red   --Tick--> Green
                   Green --Tick--> Red

                 fn run() -> Effect(StartResult(Machine.Handle)) = Machine.start(0)
               """)
    end

    test "a Main-owned fsm's generated aliases resolve from a sibling module" do
      assert {:ok, _} =
               compile("""
               use Std.Fsm

               fsm LmAliasMachine with Int
                 Red    --Tick--> Green
                 Green  --Tick--> Red

               mod LmAliasUser
                 fn handle(h: Main.LmAliasMachine.Handle) -> Int = 1
                 fn datum(d: Main.LmAliasMachine.Data) -> Int = d
               """)
    end

    test "a Main-owned lifted module is nameable from a later sibling module" do
      assert {:ok, _} =
               compile("""
               use Std.Fsm

               fsm LmTopMachine
                 state Int
                 events
                   Tick -> :keep_state_and_data

               mod LmTopUser
                 fn describe(e: Main.LmTopMachine.Event) -> Int = 1
               """)
    end
  end

  describe "resolution stays honest" do
    test "a member the lifted module does not have is still rejected" do
      assert {:error, _} =
               compile("""
               mod LmBogusA
                 use Std.Fsm

                 fsm Machine
                   state Int
                   events
                     Tick -> :keep_state_and_data

                 fn describe(e: Machine.CompletelyBogus) -> Int = 1
               """)
    end

    test "a lifted module that is not declared here is still unknown" do
      assert {:error, _} =
               compile("""
               mod LmBogusB
                 use Std.Fsm

                 fsm Machine
                   state Int
                   events
                     Tick -> :keep_state_and_data

                 fn describe(e: NeverDeclared.Event) -> Int = 1
               """)
    end
  end
end
