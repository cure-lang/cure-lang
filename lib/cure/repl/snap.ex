defmodule Cure.REPL.Snap do
  @moduledoc """
  REPL session snapshot serialization for `cure snap` (v0.32.0).

  A `.cure-snap` file captures the entire interactive session state so
  it can be resumed in a later invocation or shared with a colleague.

  ## File format

      "CURESNAP\\0" <> <<0x01>> <> gzip(term_to_binary(snap_map))

  The `snap_map` contains:

    * `session_entries` -- the full `Cure.REPL.Session` entry list (all
      named declarations: `fn`, `type`, `rec`, `interface`, `implementation`,
      `proof`).
    * `history_entries` -- up to 500 most-recent history lines.
    * `uses`            -- the `use` import list (module name strings).
    * `defs`            -- compiled definition keyword list from the session.
    * `holes`           -- outstanding typed-hole records.
    * `stdlib_kind`     -- `:none`, `:all`, or a list of module names.
    * `theme`           -- theme name atom (`:dark`, `:light`, `:mono`).
    * `mode`            -- editing mode atom (`:emacs`, `:vi_insert`).
    * `loaded_paths`    -- paths previously given to `:load` (advisory).
    * `snap_vsn`        -- schema version string (`"0.1"`).

  ## Merge semantics on `:snap load`

    * `session_entries` -- last-writer-wins per key, same as live sessions.
    * `history_entries` -- appended to the current history (newer first).
    * `uses`            -- union (no duplicates).
    * `defs`, `holes`   -- replaced wholesale.
    * `theme`, `mode`, `stdlib_kind` -- replaced.
    * `loaded_paths`    -- warns (E070) for each path that no longer exists.
  """

  @magic "CURESNAP\0"
  @vsn <<0x01>>
  @snap_vsn "0.1"
  @history_cap 500

  @type snap_map :: map()

  # -- Saving -------------------------------------------------------------------

  @doc """
  Serialize the current REPL state to a `.cure-snap` file.

  Returns `:ok` on success, `{:error, reason}` on I/O failure.
  """
  @spec save(map(), String.t()) :: :ok | {:error, term()}
  def save(%{} = state, path) when is_binary(path) do
    snap = build_snap(state)
    bytes = serialize(snap)

    case File.write(path, bytes) do
      :ok -> :ok
      {:error, reason} -> {:error, {:file_write_error, path, reason}}
    end
  end

  # -- Loading ------------------------------------------------------------------

  @doc """
  Load a `.cure-snap` file.

  Returns `{:ok, snap_map}` on success, `{:error, :E069}` on schema
  mismatch, `{:error, :corrupt}` on malformed data, or
  `{:error, {:file_read_error, path, reason}}` on I/O failure.
  """
  @spec load(String.t()) :: {:ok, snap_map()} | {:error, term()}
  def load(path) when is_binary(path) do
    case File.read(path) do
      {:ok, bytes} -> deserialize(bytes)
      {:error, reason} -> {:error, {:file_read_error, path, reason}}
    end
  end

  @doc """
  Apply a loaded snap map onto a live REPL state struct.

  Returns the updated state. Emits an E070 warning for each
  `loaded_paths` entry that no longer exists at its saved path.
  """
  @spec apply_snap(map(), snap_map()) :: map()
  def apply_snap(%{} = state, snap_map) when is_map(snap_map) do
    # Warn for missing loaded files.
    loaded_paths = Map.get(snap_map, :loaded_paths, [])

    missing =
      Enum.filter(loaded_paths, fn p -> not File.exists?(p) end)

    Enum.each(missing, fn p ->
      Cure.Diagnostic.Host.emit_diagnostic(
        Cure.Diagnostic.Operational.snap_missing(p),
        output_device: :stderr
      )
    end)

    present_paths = Enum.reject(loaded_paths, &(&1 in missing))

    # Merge session entries: entries from the snap win over the current
    # session on key collisions (the snap is "newer" for this merge).
    current_defs = Map.get(state, :defs, [])
    snap_defs = Map.get(snap_map, :defs, [])
    merged_defs = merge_defs(current_defs, snap_defs)

    # Union uses.
    current_uses = Map.get(state, :uses, [])
    snap_uses = Map.get(snap_map, :uses, [])
    merged_uses = Enum.uniq(current_uses ++ snap_uses)

    # Append history (snap history at the top = most recent).
    current_history = Map.get(state, :history, [])
    snap_history = Map.get(snap_map, :history_entries, [])
    merged_history = Enum.uniq(snap_history ++ current_history)

    %{
      state
      | defs: merged_defs,
        uses: merged_uses,
        history: merged_history,
        holes: Map.get(snap_map, :holes, state.holes),
        loaded: Enum.uniq(present_paths ++ (state.loaded || []))
    }
  end

  # -- Snap file listing --------------------------------------------------------

  @doc """
  List `.cure-snap` files in `dir` (recursive).
  """
  @spec list(String.t()) :: [String.t()]
  def list(dir \\ ".") when is_binary(dir) do
    dir
    |> Path.join("**/*.cure-snap")
    |> Path.wildcard()
    |> Enum.sort()
  end

  # -- Internal ------------------------------------------------------------------

  defp build_snap(state) do
    %{
      session_entries: Map.get(state, :defs, []),
      history_entries: Enum.take(state.history || [], @history_cap),
      uses: state.uses || [],
      defs: state.defs || [],
      holes: state.holes || [],
      stdlib_kind: state.stdlib_kind || :none,
      theme: (state.theme && state.theme.name) || :dark,
      mode: state.mode || :emacs,
      loaded_paths: state.loaded || [],
      snap_vsn: @snap_vsn
    }
  end

  defp serialize(snap_map) do
    body = :zlib.gzip(:erlang.term_to_binary(snap_map))
    @magic <> @vsn <> body
  end

  defp deserialize(<<@magic, version::binary-size(1), rest::binary>>) do
    if version == @vsn do
      try do
        snap = rest |> :zlib.gunzip() |> :erlang.binary_to_term([:safe])

        case Map.get(snap, :snap_vsn) do
          @snap_vsn -> {:ok, snap}
          nil -> {:ok, snap}
          _other -> {:error, :E069}
        end
      rescue
        _ -> {:error, :corrupt}
      end
    else
      {:error, :E069}
    end
  end

  defp deserialize(_), do: {:error, :corrupt}

  defp merge_defs(current, snap) do
    # Both current and snap are lists of entry maps with a `:key` field.
    # Last-writer-wins semantics: snap entries overwrite current on same key.
    current_map =
      current
      |> Enum.filter(&is_map/1)
      |> Enum.map(fn e -> {Map.get(e, :key), e} end)
      |> Map.new()

    snap_map =
      snap
      |> Enum.filter(&is_map/1)
      |> Enum.map(fn e -> {Map.get(e, :key), e} end)
      |> Map.new()

    Map.merge(current_map, snap_map)
    |> Map.values()
  end
end
