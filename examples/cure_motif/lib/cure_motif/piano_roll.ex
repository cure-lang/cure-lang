defmodule CureMotif.PianoRoll do
  @moduledoc """
  ASCII piano-roll renderer for a sequence of Cure `Event` tuples.

  Events are the tagged tuples produced by `Cure.Motif.render/2`:

      {:note_on,  pitch, velocity, channel}
      {:note_off, pitch, channel}
      {:tick,     step_index}

  `render/1` accepts the list of events and returns a single string
  containing one row per MIDI pitch seen, aligned on a tick grid. Each
  column corresponds to one Tick. The cell under a tick column carries:

      * `|`  -- plain grid marker
      * `X`  -- a NoteOn event at that pitch fired in that column
      * `=`  -- that pitch is currently sustaining (between on and off)
      * `.`  -- no activity

  The rendered result is deterministic given the input event list, so
  it is safe to call from tests.
  """

  @doc """
  Render `events` as an ASCII piano roll. Returns the string.

  If `events` contains no pitches at all, returns an empty string.
  """
  @spec render([term()]) :: String.t()
  def render(events) when is_list(events) do
    ticks = extract_ticks(events)
    grid = build_grid(events, ticks)

    case grid do
      %{pitches: []} ->
        ""

      %{pitches: pitches, columns: columns} ->
        header =
          "     " <>
            Enum.map_join(columns, "", fn _tick -> "|" end) <>
            "\n"

        rows =
          pitches
          |> Enum.sort(:desc)
          |> Enum.map_join("\n", fn pitch -> row(pitch, columns, grid.cells) end)

        header <> rows
    end
  end

  # -- Internals -------------------------------------------------------------

  defp extract_ticks(events) do
    events
    |> Enum.filter(&match?({:Tick, _}, &1))
    |> Enum.map(fn {:Tick, t} -> t end)
    |> Enum.sort()
    |> Enum.uniq()
  end

  defp build_grid(events, ticks) do
    columns = if ticks == [], do: [0], else: ticks

    {cells, pitches, _sustain, _last_tick} =
      Enum.reduce(events, {%{}, MapSet.new(), MapSet.new(), hd(columns)}, fn
        {:Tick, t}, {cells, pitches, sustain, _last} ->
          {cells, pitches, sustain, t}

        {:NoteOn, p, _v, _c}, {cells, pitches, sustain, tick} ->
          key = {p, tick}
          {Map.put(cells, key, :on), MapSet.put(pitches, p), MapSet.put(sustain, p), tick}

        {:NoteOff, _p, _c}, {cells, pitches, sustain, tick} ->
          {cells, pitches, sustain, tick}

        _other, acc ->
          acc
      end)

    %{pitches: MapSet.to_list(pitches), columns: columns, cells: cells}
  end

  defp row(pitch, columns, cells) do
    prefix = pitch |> Integer.to_string() |> String.pad_leading(3)

    body =
      Enum.map_join(columns, "", fn tick ->
        case Map.get(cells, {pitch, tick}, :off) do
          :on -> "X"
          _ -> "."
        end
      end)

    prefix <> "  " <> body
  end
end
