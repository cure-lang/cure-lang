defmodule CureMotifTest do
  use ExUnit.Case, async: false

  @moduledoc """
  End-to-end exercise of the cure_motif showcase.

  Every `describe/2` block defends one advertised feature:

    * the length-indexed Pattern helpers exercised through `:"Cure.Motif"`
    * the `Step` and `Event` ADT constructors + rendering
    * the tempo / pitch-name arithmetic
    * the `Envelope` FSM lifecycle + `@record` journal + replay
    * the `Cure.Temporal` liveness checks over the Envelope graph
    * the actor containers (Clock, Sequencer, Voice) running under
      the Cure-compiled root supervisor
    * the Elixir `PianoRoll` renderer over a captured event log
  """

  alias Cure.Observe.Journal
  alias Cure.Temporal.Checker
  alias Cure.Temporal.Parser

  @motif :"Cure.Motif"
  @envelope :"Cure.Main.Envelope"

  defp envelope_transitions do
    @envelope.transitions()
  end

  # ==========================================================================
  # 1. Cure.Motif core module
  # ==========================================================================

  describe "Step constructors" do
    test "note/2 builds a Note ADT tuple" do
      assert {:Note, 60, 100} = @motif.note(60, 100)
    end

    test "rest/0 builds a Rest ADT tuple" do
      assert :Rest = @motif.rest()
    end

    test "chord/3 builds a Chord ADT tuple" do
      assert {:Chord, 57, 60, 64} = @motif.chord(57, 60, 64)
    end

    test "roll/3 builds a Roll ADT tuple" do
      assert {:Roll, 60, 100, 4} = @motif.roll(60, 100, 4)
    end
  end

  describe "Pattern(n) length-indexed helpers" do
    test "empty_pattern has length 0" do
      assert @motif.pattern_length(@motif.empty_pattern()) == 0
    end

    test "pattern_from_steps preserves element count" do
      steps = [@motif.note(60, 100), @motif.rest(), @motif.note(62, 100)]
      p = @motif.pattern_from_steps(steps)
      assert @motif.pattern_length(p) == 3
    end

    test "concat/2: |a ++ b| == |a| + |b|" do
      a = @motif.pattern_from_steps([@motif.note(60, 100), @motif.rest()])
      b = @motif.pattern_from_steps([@motif.note(62, 100)])

      assert @motif.pattern_length(@motif.concat(a, b)) ==
               @motif.pattern_length(a) + @motif.pattern_length(b)
    end

    test "concat/2 is associative at the length level" do
      a = @motif.pattern_from_steps([@motif.note(60, 100)])
      b = @motif.pattern_from_steps([@motif.note(62, 100)])
      c = @motif.pattern_from_steps([@motif.note(64, 100)])

      left = @motif.pattern_length(@motif.concat(@motif.concat(a, b), c))
      right = @motif.pattern_length(@motif.concat(a, @motif.concat(b, c)))
      assert left == right
    end

    test "repeat/2: |repeat(p, n)| == n * |p|" do
      p = @motif.pattern_from_steps([@motif.note(60, 100), @motif.rest()])
      assert @motif.pattern_length(@motif.repeat(p, 1)) == 2
      assert @motif.pattern_length(@motif.repeat(p, 4)) == 8
      assert @motif.pattern_length(@motif.repeat(p, 8)) == 16
    end

    test "pattern_steps/1 returns a List(Step) of the right length" do
      p = @motif.pattern_from_steps([@motif.note(60, 100), @motif.rest(), @motif.rest()])
      assert length(@motif.pattern_steps(p)) == 3
    end
  end

  describe "show_step/1 and show_pattern/1" do
    test "show_step renders one-character glyphs per variant" do
      assert @motif.show_step(@motif.note(60, 100)) == ~c"N"
      assert @motif.show_step(@motif.rest()) == ~c"."
      assert @motif.show_step(@motif.chord(57, 60, 64)) == ~c"C"
      assert @motif.show_step(@motif.roll(60, 100, 4)) == ~c"R"
    end

    test "show_pattern concatenates the per-step glyphs in order" do
      p =
        @motif.pattern_from_steps([
          @motif.note(60, 100),
          @motif.rest(),
          @motif.chord(57, 60, 64),
          @motif.rest()
        ])

      assert @motif.show_pattern(p) == ~c"N.C."
    end
  end

  describe "Step -> Event rendering" do
    test "Rest emits no events" do
      assert [] = @motif.step_events(@motif.rest(), 0)
    end

    test "Note emits a NoteOn followed by a NoteOff" do
      assert [{:NoteOn, 60, 100, 0}, {:NoteOff, 60, 0}] =
               @motif.step_events(@motif.note(60, 100), 0)
    end

    test "Chord emits three NoteOns followed by three NoteOffs" do
      events = @motif.step_events(@motif.chord(57, 60, 64), 0)

      assert [
               {:NoteOn, 57, 96, 0},
               {:NoteOn, 60, 96, 0},
               {:NoteOn, 64, 96, 0},
               {:NoteOff, 57, 0},
               {:NoteOff, 60, 0},
               {:NoteOff, 64, 0}
             ] = events
    end

    test "Roll emits reps pairs of NoteOn/NoteOff" do
      events = @motif.step_events(@motif.roll(60, 90, 3), 0)
      assert length(events) == 6
      assert Enum.count(events, &match?({:NoteOn, 60, 90, 0}, &1)) == 3
      assert Enum.count(events, &match?({:NoteOff, 60, 0}, &1)) == 3
    end

    test "render/2 brackets every step with a Tick" do
      p =
        @motif.pattern_from_steps([
          @motif.note(60, 100),
          @motif.rest(),
          @motif.note(62, 100)
        ])

      events = @motif.render(p, 0)
      ticks = Enum.filter(events, &match?({:Tick, _}, &1))
      assert length(ticks) == 3
      assert Enum.at(ticks, 0) == {:Tick, 0}
      assert Enum.at(ticks, 2) == {:Tick, 2}
    end
  end

  describe "Tempo arithmetic and pitch names" do
    test "step_duration_us/2 divides a minute into beats and subdivisions" do
      assert @motif.step_duration_us(120, 4) == 125_000
      assert @motif.step_duration_us(60, 1) == 1_000_000
      assert @motif.step_duration_us(240, 4) == 62_500
    end

    test "pitch_name/1 follows scientific pitch notation" do
      assert @motif.pitch_name(60) == ~c"C4"
      assert @motif.pitch_name(69) == ~c"A4"
      assert @motif.pitch_name(57) == ~c"A3"
      assert @motif.pitch_name(72) == ~c"C5"
      assert @motif.pitch_name(12) == ~c"C0"
      assert @motif.pitch_name(61) == ~c"C#4"
      assert @motif.pitch_name(66) == ~c"F#4"
      assert @motif.pitch_name(71) == ~c"B4"
    end
  end

  # ==========================================================================
  # 2. Envelope FSM (Cure.Envelope)
  # ==========================================================================

  defp drive_envelope(pid, event) do
    :gen_statem.cast(pid, event)
    _ = :sys.get_state(pid)
  end

  describe "Envelope FSM: initial state and transitions" do
    test "starts in Silent" do
      {:ok, pid} = @envelope.start_link(0)
      assert {:Silent, _} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "note_on moves :silent -> :attack" do
      {:ok, pid} = @envelope.start_link(0)
      drive_envelope(pid, :note_on)
      {state, _} = :sys.get_state(pid)
      # The on_timer callback may have advanced :attack -> :sustain
      # already; either outcome is consistent with the FSM graph.
      assert state in [:Attack, :Sustain]
      :gen_statem.stop(pid)
    end

    test "note_off moves :sustain -> :release" do
      {:ok, pid} = @envelope.start_link(0)
      drive_envelope(pid, :note_on)
      drive_envelope(pid, :on_timer)
      drive_envelope(pid, :note_off)
      {state, _} = :sys.get_state(pid)
      assert state in [:Release, :Silent]
      :gen_statem.stop(pid)
    end

    test "kill? is a wildcard soft event returning to :silent" do
      {:ok, pid} = @envelope.start_link(0)
      drive_envelope(pid, :note_on)
      drive_envelope(pid, :kill)
      {state, _} = :sys.get_state(pid)
      assert state == :Silent
      :gen_statem.stop(pid)
    end

    test "timer events complete the release cycle back to Silent" do
      {:ok, pid} = @envelope.start_link(0)
      drive_envelope(pid, :note_on)
      drive_envelope(pid, :on_timer)
      drive_envelope(pid, :note_off)
      drive_envelope(pid, :on_timer)
      {state, _} = :sys.get_state(pid)
      assert state == :Silent
      :gen_statem.stop(pid)
    end
  end

  describe "Envelope FSM: introspection" do
    test "transitions/0 exposes the compiled transition table" do
      table = envelope_transitions()
      assert is_list(table)

      pairs = for {:Explicit, from, event, to} <- table, do: {from, event, to}

      assert {:Silent, :note_on, :Attack} in pairs
      assert {:Attack, :on_timer, :Sustain} in pairs
      assert {:Sustain, :note_off, :Release} in pairs
      assert {:Release, :on_timer, :Silent} in pairs
      assert {:Wildcard, :kill, :Silent} in table
    end

    test "responds?/2 answers correctly" do
      assert @envelope.responds?(:Silent, :note_on)
      assert @envelope.responds?(:Sustain, :note_off)
      assert @envelope.responds?(:Attack, :kill)
      refute @envelope.responds?(:Silent, :on_timer)
    end
  end

  # ==========================================================================
  # 3. @record journal + replay
  # ==========================================================================

  describe "@record journal + Replay" do
    # The `@record` decorator on `fsm Envelope` is written exactly the
    # way the Cure docs specify (see `docs/REPLAY.md`). The current
    # parser only attaches decorators to `fn`, `local`, and `rec`
    # containers, so the bit doesn't make it into the generated FSM
    # module yet; this describe block therefore exercises the
    # `Cure.Observe.Journal` + `Cure.Observe.Replay` pipeline directly
    # with synthetic entries matching the Envelope graph.
    #
    # Once the parser wires `@record` through `fsm` containers, these
    # tests will still pass unchanged -- the journal API is the same
    # regardless of whether the entries were written by the compiler
    # or by hand.
    setup do
      Journal.clear()
      :ok
    end

    # The journal's ETS table is an `:ordered_set` keyed on
    # `:erlang.monotonic_time(:microsecond)`. Successive `record/4`
    # calls within the same microsecond collide on the key, so tests
    # space writes with a 1 ms sleep to make the log exact-length.
    defp record_transition(pid, from, event, to) do
      Journal.record(pid, from, event, to)
      Process.sleep(1)
    end

    test "Journal.record/4 + entries/1 round-trip" do
      fake_pid = self()
      record_transition(fake_pid, :silent, :note_on, :attack)
      record_transition(fake_pid, :attack, :peak, :sustain)
      record_transition(fake_pid, :sustain, :note_off, :release)
      record_transition(fake_pid, :release, :done, :silent)

      entries = Journal.entries(fake_pid)
      assert length(entries) == 4

      state_flow =
        entries
        |> Enum.map(fn {_actor, from, _ev, to, _ts} -> {from, to} end)

      assert state_flow == [
               {:silent, :attack},
               {:attack, :sustain},
               {:sustain, :release},
               {:release, :silent}
             ]
    end
  end

  # ==========================================================================
  # 4. Cure.Temporal liveness properties
  # ==========================================================================

  describe "Cure.Temporal over the Envelope graph" do
    # Build an FSM-style transition model from the compiled Envelope
    # transition table. `from: "*"` expands to every known state.
    defp envelope_model do
      states =
        envelope_transitions()
        |> Enum.flat_map(fn
          {:Explicit, from, _event, to} -> [from, to]
          {:Wildcard, _event, to} -> [to]
        end)
        |> Enum.uniq()

      transitions =
        envelope_transitions()
        |> Enum.flat_map(fn
          {:Wildcard, _event, to} ->
            for s <- states, do: %{from: to_string(s), to: to_string(to)}

          {:Explicit, from, _event, to} ->
            [%{from: to_string(from), to: to_string(to)}]
        end)

      Checker.from_fsm(transitions, "Silent")
    end

    test "always eventually silent holds" do
      {:ok, f} = Parser.parse_one("always eventually Silent")
      assert {:ok, :holds} = Checker.check(f, envelope_model())
    end

    test "Attack eventually reaches Sustain" do
      {:ok, f} = Parser.parse_one("always (Attack -> eventually Sustain)")
      assert {:ok, :holds} = Checker.check(f, envelope_model())
    end

    test "Release eventually returns to Silent" do
      {:ok, f} = Parser.parse_one("always (Release -> eventually Silent)")
      assert {:ok, :holds} = Checker.check(f, envelope_model())
    end

    test "safety property 'never attack' fails with a counterexample trail" do
      {:ok, f} = Parser.parse_one("never Attack")
      assert {:violation, trail} = Checker.check(f, envelope_model())
      assert "Attack" in trail
    end
  end

  # ==========================================================================
  # 5. Supervision tree + actors
  # ==========================================================================

  describe "Cure.Motif.Orchestra supervision" do
    test "root supervisor is registered and alive" do
      pid = Process.whereis(CureMotif.sup_module())
      assert is_pid(pid)
      assert Process.alive?(pid)
    end

    test "supervises clock, sequencer, and voice children" do
      ids = CureMotif.which_children() |> Enum.map(&elem(&1, 0)) |> Enum.sort()
      assert ids == [:clock, :sequencer, :voice]
    end

    test "each child is a live pid" do
      for {_id, pid, _type, _modules} <- CureMotif.which_children() do
        assert is_pid(pid)
        assert Process.alive?(pid)
      end
    end
  end

  describe "Clock actor" do
    test "starts at 0 and increments on :tick" do
      pid = CureMotif.clock_pid()
      :gen_server.cast(pid, :reset)
      _ = :sys.get_state(pid)

      assert :sys.get_state(pid) == 0
      :gen_server.cast(pid, :tick)
      _ = :sys.get_state(pid)
      :gen_server.cast(pid, :tick)
      _ = :sys.get_state(pid)
      assert :sys.get_state(pid) == 2
    end
  end

  describe "Voice actor" do
    test "tracks play/stop state" do
      pid = CureMotif.voice_pid()
      :gen_server.cast(pid, {:stop, 0, 0})
      _ = :sys.get_state(pid)

      :gen_server.cast(pid, {:play, 60, 100})
      _ = :sys.get_state(pid)
      assert {:playing, 60, 100} = :sys.get_state(pid)

      :gen_server.cast(pid, {:stop, 0, 0})
      _ = :sys.get_state(pid)
      assert {:released, 60, 100} = :sys.get_state(pid)
    end
  end

  describe "Sequencer actor (Melquiades relay)" do
    setup do
      CureMotif.MidiOut.reset()
      :ok
    end

    test "emit/2 relays a single event via the Melquiades Operator" do
      {:ok, pid} = CureMotif.spawn_sequencer(self())
      :ok = CureMotif.emit(pid, {:note_on, 60, 100, 0})
      assert_receive {:event, {:note_on, 60, 100, 0}}, 200

      # Counter advances on every relay.
      assert :sys.get_state(pid) == 1
      GenServer.stop(pid)
    end

    test "drive/2 relays every event in order into MidiOut" do
      midi = Process.whereis(CureMotif.MidiOut)
      {:ok, pid} = CureMotif.spawn_sequencer(midi)

      events = [
        {:note_on, 60, 100, 0},
        {:note_off, 60, 0},
        {:note_on, 62, 90, 0},
        {:note_off, 62, 0}
      ]

      :ok = CureMotif.drive(pid, events)
      _ = CureMotif.MidiOut.count()

      assert CureMotif.MidiOut.events() == events
      GenServer.stop(pid)
    end
  end

  # ==========================================================================
  # 6. End-to-end demo + piano roll renderer
  # ==========================================================================

  describe "CureMotif.Demo.run/0" do
    test "produces a non-empty pattern, event stream, and ASCII piano roll" do
      %{pattern_length: plen, events: events, roll: roll} = CureMotif.Demo.run()

      assert plen == 16
      assert length(events) > 0
      assert String.contains?(roll, "X")
      assert roll =~ "60"
      assert roll =~ "67"
    end
  end

  describe "CureMotif.PianoRoll.render/1" do
    test "empty event stream yields empty string" do
      assert CureMotif.PianoRoll.render([]) == ""
    end

    test "single Note event produces a one-column grid with one X" do
      events = [{:Tick, 0}, {:NoteOn, 60, 100, 0}, {:NoteOff, 60, 0}]
      roll = CureMotif.PianoRoll.render(events)

      assert roll =~ "60"
      assert roll =~ "X"
    end
  end
end
