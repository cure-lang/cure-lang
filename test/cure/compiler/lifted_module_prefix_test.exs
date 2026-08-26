defmodule Cure.Compiler.LiftedModulePrefixTest do
  use ExUnit.Case, async: false
  @moduletag timeout: 180_000

  # `mod Demo` has always compiled to `Cure.Demo` without the author spelling the
  # prefix out. The lifted-module macros -- `fsm`, `actor`, `sup`, `app` -- used to
  # reject the same bare name with `{:invalid_module_name, "Demo"}`, so every
  # example had to carry an emitter artifact in its source.
  #
  # A `ModuleName` capture now qualifies itself, by two rules:
  #   * a bare name is relative to its enclosing module (including implicit
  #     `Main`), so siblings don't collide
  #   * a dotted name is absolute, so one module can reach another's children

  describe "top level (implicit Main module)" do
    test "fsm emits a bare module name beneath the implicit Main module" do
      source = """
      use Std.Fsm

      fsm BarePrefixFsm
        state Int
        events
          Tick -> :keep_state_and_data
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert apply(:"Cure.Main.BarePrefixFsm", :init, [0]) == {:ok, :initial, 0}
    end

    test "sup accepts a bare module name and prefixes bare child references" do
      source = """
      use Std.Supervisor

      sup BarePrefixRoot
        children
          worker BarePrefixWorker as bare_worker
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_strategy, [child]}} = apply(:"Cure.Main.BarePrefixRoot", :init, [[]])

      assert {:bare_worker, {:"Cure.Main.BarePrefixWorker", :start_link, []}, _, _, :worker, _} =
               child
    end

    # `app` and `sup` are deliberately in separate compilation units: only the
    # first lifted module of a unit is loaded by `compile_and_load`, which is a
    # pre-existing limitation and not what this test is about.
    test "app accepts a bare module name and a bare root" do
      source = """
      use Std.App

      app BarePrefixApp
        root BarePrefixAppRoot
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
      exports = :"Cure.Main.BarePrefixApp".module_info(:exports)
      assert {:start, 2} in exports
      assert {:stop, 1} in exports
    end
  end

  describe "inside a mod" do
    test "a bare name is scoped to the enclosing mod" do
      source = """
      mod Scoped
        use Std.Fsm

        fsm Inner
          state Int
          events
            Tick -> :keep_state_and_data
      """

      assert {:ok, :"Cure.Scoped"} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert apply(:"Cure.Scoped.Inner", :init, [0]) == {:ok, :initial, 0}
      assert Code.ensure_loaded(:"Cure.Inner") == {:error, :nofile}
    end

    test "two mods may each declare a lifted module of the same name" do
      source = """
      mod Gamma
        use Std.Supervisor

        sup Tree
          children
            worker GammaWorker as w

      mod Delta
        use Std.Supervisor

        sup Tree
          children
            worker DeltaWorker as w
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_s, [{:w, {:"Cure.Gamma.GammaWorker", :start_link, []}, _, _, _, _}]}} =
               apply(:"Cure.Gamma.Tree", :init, [[]])

      assert {:ok, {_s, [{:w, {:"Cure.Delta.DeltaWorker", :start_link, []}, _, _, _, _}]}} =
               apply(:"Cure.Delta.Tree", :init, [[]])
    end

    test "a bare child reference resolves inside the declaring mod" do
      source = """
      mod Local
        use Std.Supervisor

        sup LocalRoot
          children
            worker LocalWorker as local_worker
      """

      assert {:ok, :"Cure.Local"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_strategy, [child]}} = apply(:"Cure.Local.LocalRoot", :init, [[]])

      assert {:local_worker, {:"Cure.Local.LocalWorker", :start_link, []}, _, _, :worker, _} =
               child
    end

    test "a dotted name is absolute, so one mod can reference another's child" do
      source = """
      mod Trees
        use Std.Supervisor

        sup Root
          children
            worker Workers.Counter as counter
      """

      assert {:ok, :"Cure.Trees"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_strategy, [child]}} = apply(:"Cure.Trees.Root", :init, [[]])
      assert {:counter, {:"Cure.Workers.Counter", :start_link, []}, _, _, :worker, _} = child
    end

    test "nested mods scope by the full path" do
      source = """
      mod Outer
        mod Inner
          use Std.Supervisor

          sup Deep
            children
              worker DeepWorker as w
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_s, [{:w, {:"Cure.Outer.Inner.DeepWorker", :start_link, []}, _, _, _, _}]}} =
               apply(:"Cure.Outer.Inner.Deep", :init, [[]])
    end
  end

  describe "synthesised companion types" do
    # The transition-table emitter already declared `State`/`Event` inside the
    # generated module. The structured-family emitter hoisted an `FsmEvent` type
    # into the enclosing scope instead, which is both a name nobody wrote and a
    # guaranteed collision between two sibling modules. Both now agree: a
    # synthesised type is owned by the machine it belongs to.
    test "the synthesised event type is owned by the generated module" do
      source = """
      mod Synth
        use Std.Fsm

        fsm Machine
          state Int
          events
            Tick -> :keep_state_and_data
      """

      assert {:ok, :"Cure.Synth"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      exports = :"Cure.Synth.Machine".module_info(:exports)
      assert {:"__impl_Equatable_Synth.Machine#Event_==", 2} in exports
    end

    test "the synthesised event constructors are not bound in the enclosing mod" do
      source = """
      mod Unqualified
        use Std.Fsm

        fsm Machine
          state Int
          events
            Tick -> :keep_state_and_data

        fn make() -> Atom = Tick
      """

      assert {:error, {:codegen_error, {:source_context, {:unknown_global, :Tick, _}, _}}} =
               Cure.Compiler.compile_and_load(source, emit_events: false)
    end

    test "two structured fsms in sibling mods do not collide on the event type" do
      source = """
      mod Left
        use Std.Fsm

        fsm Machine
          state Int
          events
            Tick -> :keep_state_and_data

      mod Right
        use Std.Fsm

        fsm Machine
          state Int
          events
            Ping -> :keep_state_and_data
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert apply(:"Cure.Left.Machine", :handle_event, [:cast, :Tick, :initial, 0]) ==
               :keep_state_and_data

      assert apply(:"Cure.Right.Machine", :handle_event, [:cast, :Ping, :initial, 0]) ==
               :keep_state_and_data
    end

    test "an explicit event_type is still honoured, and stays in the enclosing mod" do
      source = """
      mod Explicit
        use Std.Fsm

        type Kind = Tick | Stop

        fsm Machine
          state Int
          event_type Kind
          events
            Tick -> :keep_state_and_data
            Stop -> :keep_state_and_data

        fn make() -> Kind = Tick
      """

      assert {:ok, :"Cure.Explicit"} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert apply(:"Cure.Explicit", :make, []) == :Tick

      assert apply(:"Cure.Explicit.Machine", :handle_event, [:cast, :Stop, :initial, 0]) ==
               :keep_state_and_data
    end
  end

  describe "the transition-table surface" do
    test "a transition table is scoped to the enclosing mod" do
      source = """
      mod Gate
        use Std.Fsm

        fsm Turnstile with Int
          initial locked
          transitions
            locked --coin--> unlocked
            unlocked --push--> locked
      """

      assert {:ok, :"Cure.Gate"} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert {:ok, :locked, 0} = apply(:"Cure.Gate.Turnstile", :init, [0])
      assert Code.ensure_loaded(:"Cure.Turnstile") == {:error, :nofile}
    end

    test "its State and Event types are owned by the generated module" do
      source = """
      mod Doors
        use Std.Fsm

        fsm Door with Int
          initial shut
          transitions
            shut --open--> ajar
            ajar --shut_it--> shut
      """

      assert {:ok, :"Cure.Doors"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      exports = :"Cure.Doors.Door".module_info(:exports)
      assert {:"__impl_Equatable_Doors.Door#State_==", 2} in exports
      assert {:"__impl_Equatable_Doors.Door#Event_==", 2} in exports
    end

    test "an event payload declared in the table reaches the transition body" do
      source = """
      mod Meters
        use Std.Fsm

        fsm Meter with Int
          initial idle
          transitions
            idle --insert(amount: Int)--> running
              update data + amount
            running --reset--> idle
      """

      assert {:ok, :"Cure.Meters"} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert apply(:"Cure.Meters.Meter", :decide, [{:insert, 25}, :idle, 0]) == {:Next, :running, 25}
    end

    test "two transition tables in sibling mods do not collide" do
      source = """
      mod North
        use Std.Fsm

        fsm Signal with Int
          initial red
          transitions
            red --go--> green
            green --stop--> red

      mod South
        use Std.Fsm

        fsm Signal with Int
          initial red
          transitions
            red --go--> green
            green --stop--> red
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert {:ok, :red, 0} = apply(:"Cure.North.Signal", :init, [0])
      assert {:ok, :red, 0} = apply(:"Cure.South.Signal", :init, [0])
    end
  end

  describe "names that are left alone" do
    test "an explicit Cure prefix is preserved rather than doubled or rescoped" do
      source = """
      mod Explicit
        use Std.Supervisor

        sup Cure.ExplicitPrefixRoot
          children
            worker Cure.ExplicitPrefixWorker as explicit_worker
      """

      assert {:ok, :"Cure.Explicit"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_strategy, [child]}} = apply(:"Cure.ExplicitPrefixRoot", :init, [[]])

      assert {:explicit_worker, {:"Cure.ExplicitPrefixWorker", :start_link, []}, _, _, :worker, _} =
               child
    end

    test "a foreign child module keeps its own name" do
      source = """
      mod Foreign
        use Std.Supervisor

        sup ForeignChildRoot
          children
            worker Elixir.Agent as foreign
      """

      assert {:ok, :"Cure.Foreign"} = Cure.Compiler.compile_and_load(source, emit_events: false)

      assert {:ok, {_strategy, [child]}} = apply(:"Cure.Foreign.ForeignChildRoot", :init, [[]])
      assert {:foreign, {Agent, :start_link, []}, _, _, :worker, _} = child
    end
  end
end
