defmodule CureMotif.Demo do
  @moduledoc """
  Packaged walkthrough demonstrating the cure_motif showcase end-to-end.

  `CureMotif.Demo.run/0`:

    1. Builds a 16-step example pattern on top of the `:"Cure.Motif"`
       BEAM module (compiled from `cure_src/motif.cure`).
    2. Renders that pattern into a flat Cure event stream.
    3. Loads the stream into the running `:"Cure.Main.Sequencer"`.
    4. Drives 16 `:tick` messages through the sequencer and captures
       every event it emits via `CureMotif.MidiOut`.
    5. Returns a map with the pattern, the event log, and the ASCII
       piano-roll, ready to print or assert on in tests.
  """

  @motif :"Cure.Motif"
  @compile {:no_warn_undefined, @motif}

  @doc """
  Run the complete demo and return a map with `:pattern_length`,
  `:events`, and `:roll`.

  Spawns a fresh sequencer actor whose `notify/1` target is the
  running `CureMotif.MidiOut` sink, loads the pre-rendered event
  stream, drives exactly `length(events)` ticks through it, and
  returns the captured roll. The spawned sequencer is stopped at the
  end of the call, so this function is safe to call repeatedly.
  """
  @spec run() :: %{
          pattern_length: non_neg_integer(),
          events: [term()],
          roll: String.t()
        }
  def run do
    pattern = build_pattern()
    events = @motif.render(pattern, 0)
    :ok = CureMotif.MidiOut.reset()
    :ok = drive_sequencer(events)
    # Flush MidiOut's mailbox by making a sync call before we read.
    _ = CureMotif.MidiOut.count()
    roll = CureMotif.PianoRoll.render(CureMotif.MidiOut.events())

    %{
      pattern_length: @motif.pattern_length(pattern),
      events: events,
      roll: roll
    }
  end

  @doc """
  Build the showcase's 16-step pattern as a Cure Pattern value.

  The phrase alternates a middle-C single note on the downbeats, an
  A-minor triad on the third beat of every bar, and a roll on the
  fifth of every other bar. The layout is intentionally musical
  enough that the rendered ASCII piano roll reads like a real groove
  rather than a uniform grid.
  """
  @spec build_pattern() :: term()
  def build_pattern do
    steps = [
      @motif.note(60, 100),
      @motif.rest(),
      @motif.note(62, 90),
      @motif.rest(),
      @motif.chord(57, 60, 64),
      @motif.rest(),
      @motif.note(62, 90),
      @motif.rest(),
      @motif.note(60, 100),
      @motif.rest(),
      @motif.roll(67, 80, 4),
      @motif.rest(),
      @motif.chord(57, 60, 64),
      @motif.rest(),
      @motif.note(62, 90),
      @motif.rest()
    ]

    @motif.pattern_from_steps(steps)
  end

  @doc """
  Spawn a new sequencer rooted at `CureMotif.MidiOut`, relay every
  event in `events` through it, and stop the spawned sequencer
  before returning.
  """
  @spec drive_sequencer([term()]) :: :ok
  def drive_sequencer(events) do
    midi_out = Process.whereis(CureMotif.MidiOut)
    {:ok, pid} = CureMotif.spawn_sequencer(midi_out)

    try do
      :ok = CureMotif.drive(pid, events)
      :ok
    after
      # Let any lingering notifications flush before we stop.
      _ = :sys.get_state(pid)
      GenServer.stop(pid)
    end
  end
end
