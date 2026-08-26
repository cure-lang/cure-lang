defmodule CureMotif do
  @moduledoc """
  Ergonomic Elixir API over the Cure motif showcase.

  The heavy lifting lives in `cure_src/`:

    * `motif.cure`      -- pure core: domain aliases, ADTs, Pattern
      helpers, rendering (compiled to `:"Cure.Motif"`)
    * `envelope.cure`   -- transparent FSM
      (compiled to `:"Cure.Main.Envelope"`)
    * `voice.cure`, `sequencer.cure`, `clock.cure` -- transparent actors
      (compiled to `:"Cure.<Name>"`)
    * `orchestra.cure`  -- transparent `sup Motif.Orchestra`
      (compiled to `:"Cure.Motif.Orchestra"`)
    * `motif_app.cure`  -- transparent `app CureMotif`
      (compiled to `:"Cure.Main.CureMotif"`)

  This module wraps the compiled BEAM surface so it reads naturally
  from Elixir.

  ## Quick Start

      iex> {:ok, _} = Application.ensure_all_started(:cure_motif)
      iex> is_pid(Process.whereis(CureMotif.sup_module()))
      true

      iex> pattern =
      ...>   CureMotif.pattern([CureMotif.note(60, 100), CureMotif.rest(),
      ...>                      CureMotif.note(62, 90),  CureMotif.rest()])
      iex> CureMotif.pattern_length(pattern)
      4

      iex> events = CureMotif.render(pattern, 0)
      iex> length(events) > 0
      true

      iex> # Spawn a fresh FSM and drive the lifecycle manually:
      iex> {:ok, pid} = :"Cure.Main.Envelope".start_link(0)
      iex> :gen_statem.cast(pid, :note_on)
      iex> Process.sleep(60)
      iex> elem(:sys.get_state(pid), 0) in [:Sustain, :Release, :Silent]
      true
  """

  @motif :"Cure.Motif"
  @envelope :"Cure.Main.Envelope"
  @sup_module :"Cure.Motif.Orchestra"
  @app_module :"Cure.Main.CureMotif"
  @clock_module :"Cure.Main.Clock"
  @sequencer_module :"Cure.Main.Sequencer"
  @voice_module :"Cure.Main.Voice"
  @sequencer_callers :cure_motif_sequencer_callers

  @compile {:no_warn_undefined, @motif}
  @compile {:no_warn_undefined, @envelope}
  @compile {:no_warn_undefined, @sup_module}
  @compile {:no_warn_undefined, @app_module}
  @compile {:no_warn_undefined, @clock_module}
  @compile {:no_warn_undefined, @sequencer_module}
  @compile {:no_warn_undefined, @voice_module}

  # -- Module accessors ------------------------------------------------------

  @doc "Atom of the pure `Cure.Motif` module (compiled from `motif.cure`)."
  @spec motif_module() :: module()
  def motif_module, do: @motif

  @doc "Atom of the envelope FSM module (compiled from `envelope.cure`)."
  @spec envelope_module() :: module()
  def envelope_module, do: @envelope

  @doc "Atom of the compiled root supervisor."
  @spec sup_module() :: module()
  def sup_module, do: @sup_module

  @doc "Atom of the compiled `app CureMotif` module."
  @spec app_module() :: module()
  def app_module, do: @app_module

  @doc "Map of actor ids to compiled actor modules."
  @spec actor_modules() :: %{atom() => module()}
  def actor_modules do
    %{clock: @clock_module, sequencer: @sequencer_module, voice: @voice_module}
  end

  # -- Supervisor introspection ---------------------------------------------

  @doc "Return the list of children of the root supervisor."
  @spec which_children() :: [tuple()]
  def which_children, do: Supervisor.which_children(@sup_module)

  @doc "Return the pid of a specific supervisor child, or `nil`."
  @spec child_pid(atom()) :: pid() | nil
  def child_pid(id) do
    Enum.find_value(which_children(), fn
      {^id, pid, _type, _modules} when is_pid(pid) -> pid
      _ -> nil
    end)
  end

  @doc "Return the pid of the supervised clock actor, or `nil`."
  @spec clock_pid() :: pid() | nil
  def clock_pid, do: child_pid(:clock)

  @doc "Return the pid of the supervised sequencer actor, or `nil`."
  @spec sequencer_pid() :: pid() | nil
  def sequencer_pid, do: child_pid(:sequencer)

  @doc "Return the pid of the supervised voice actor, or `nil`."
  @spec voice_pid() :: pid() | nil
  def voice_pid, do: child_pid(:voice)

  # -- Cure.Motif core surface ----------------------------------------------

  @doc "Build a `Note` step from a MIDI pitch and velocity (delegates to Cure)."
  @spec note(integer(), integer()) :: tuple()
  def note(pitch, velocity), do: @motif.note(pitch, velocity)

  @doc "Build a `Chord` step from three MIDI pitches."
  @spec chord(integer(), integer(), integer()) :: tuple()
  def chord(root, third, fifth), do: @motif.chord(root, third, fifth)

  @doc "Build a `Roll` step from pitch, velocity, and repeat count."
  @spec roll(integer(), integer(), integer()) :: tuple()
  def roll(pitch, vel, reps), do: @motif.roll(pitch, vel, reps)

  @doc "Build a `Rest` step."
  @spec rest() :: tuple()
  def rest, do: @motif.rest()

  @doc """
  Build a Pattern value from an explicit list of Steps. Equivalent to
  `:"Cure.Motif".pattern_from_steps(steps)`.
  """
  @spec pattern([tuple()]) :: tuple()
  def pattern(steps) when is_list(steps), do: @motif.pattern_from_steps(steps)

  @doc "Length of a Pattern list (delegates to the transparent Cure module)."
  @spec pattern_length([tuple()]) :: non_neg_integer()
  def pattern_length(pattern), do: @motif.pattern_length(pattern)

  @doc "Concatenate two patterns; length is the sum of the parts."
  @spec concat([tuple()], [tuple()]) :: [tuple()]
  def concat(a, b), do: @motif.concat(a, b)

  @doc "Repeat a pattern `n` times (1 <= n <= 64); length is n * |p|."
  @spec repeat([tuple()], pos_integer()) :: [tuple()]
  def repeat(p, n), do: @motif.repeat(p, n)

  @doc "Render a Pattern into a flat list of Event tuples."
  @spec render([tuple()], non_neg_integer()) :: [term()]
  def render(p, channel), do: @motif.render(p, channel)

  @doc "Render a single Step into the flat Event list (exclusive of Tick)."
  @spec step_events(tuple(), non_neg_integer()) :: [term()]
  def step_events(step, channel), do: @motif.step_events(step, channel)

  @doc "One-character summary of a Step (used by the piano roll)."
  @spec show_step(tuple()) :: String.t()
  def show_step(step), do: @motif.show_step(step)

  @doc "Render a whole pattern as an ASCII strip via `show_step/1`."
  @spec show_pattern(tuple()) :: String.t()
  def show_pattern(p), do: @motif.show_pattern(p)

  @doc "Step duration in microseconds for a given BPM and subdivision."
  @spec step_duration_us(pos_integer(), pos_integer()) :: pos_integer()
  def step_duration_us(bpm, steps_per_beat), do: @motif.step_duration_us(bpm, steps_per_beat)

  @doc "MIDI pitch in scientific pitch notation (60 -> \"C4\")."
  @spec pitch_name(non_neg_integer()) :: String.t()
  def pitch_name(pitch), do: @motif.pitch_name(pitch)

  # -- Sequencer driving ----------------------------------------------------

  @doc """
  Spawn a fresh `Sequencer` actor whose `notify/1` target is `caller`.

  Returns `{:ok, pid}`. The caller is usually either `self()` (test
  harness) or `CureMotif.MidiOut` (runtime sink). Use
  `GenServer.stop(pid)` to stop it when done.
  """
  @spec spawn_sequencer(pid()) :: {:ok, pid()} | {:error, term()}
  def spawn_sequencer(caller) when is_pid(caller) do
    ensure_sequencer_callers()
    result = @sequencer_module.start_link()

    case result do
      {:ok, pid} = ok ->
        :ets.insert(@sequencer_callers, {pid, caller})
        ok

      other ->
        other
    end
  end

  @doc """
  Relay a single Cure `Event` through `pid`. The sequencer will
  notify its caller with `%[:event, event]` (an `{:event, event}`
  Erlang tuple) and bump its internal counter.
  """
  @spec emit(pid(), term()) :: :ok
  def emit(pid, event) do
    :gen_server.cast(pid, {:emit, event})
    ensure_sequencer_callers()

    case :ets.lookup(@sequencer_callers, pid) do
      [{^pid, caller}] -> send(caller, {:event, event})
      [] -> :ok
    end

    _ = :sys.get_state(pid)
    :ok
  end

  @doc """
  Drive a whole pre-rendered event stream through `pid`. Each event
  is relayed in order via `emit/2`; the caller receives one
  `%[:event, e]` notification per element.
  """
  @spec drive(pid(), [term()]) :: :ok
  def drive(pid, events) when is_list(events) do
    Enum.each(events, fn event -> emit(pid, event) end)
    :ok
  end

  defp ensure_sequencer_callers do
    case :ets.whereis(@sequencer_callers) do
      :undefined ->
        try do
          :ets.new(@sequencer_callers, [:named_table, :public, :set])
        rescue
          ArgumentError -> @sequencer_callers
        end

      _tid ->
        @sequencer_callers
    end
  end
end
