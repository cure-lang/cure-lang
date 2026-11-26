defmodule Antigen.Corpus do
  @moduledoc """
  Committed, never-pruned, generator-independent stores (spec §7).

  Current decoding accepts only format 2 and the current universe checker
  epoch. Core pieces and diagnostic faults use separate bounded OTP JSON
  carriers. Historical records remain on disk and surface as decode errors;
  there is no automatic import, pruning, certification or seed regeneration.
  Replay runs the kernel, not the generator.
  """
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.{Serialize, Term, UniverseCodec}

  @marker "antigen-record"
  @format_version 2
  @antibody_version 3
  @universe_epoch UniverseCodec.identity() |> Tuple.to_list() |> Enum.map_join("/", &to_string/1)
  @key_prefix "antigen/2|" <> @universe_epoch <> "|"
  @max_record_bytes UniverseCodec.max_bytes()
  @required_fields ~w(format universe kind assay label seed note scaffold key pieces64)
  @optional_fields ~w(fault64)
  @fault_keys ~w(kind witness expected_head injected_head scope depth wrap_path expected_index actual_index reduction required carrier)
  @fault_paths [:app_arg, :ctor_nat, :case_scrut, :case_branch, :pair]

  def format_version, do: @format_version
  def antibody_version, do: @antibody_version
  def universe_epoch, do: @universe_epoch

  @doc "Encode a challenge to a one-line record, storing its antibody dedup key."
  @spec encode_record(Challenge.t()) :: String.t()
  def encode_record(%Challenge{} = c), do: encode_record(c, dedup_key(c, :antibody))

  @doc """
  Encode a challenge, scoping its supplied key by the current corpus/checker
  epoch. Already-scoped keys are retained verbatim. Both seed coverage keys
  and antibody keys therefore invalidate obsolete unchanged-source records.
  """
  @spec encode_record(Challenge.t(), String.t()) :: String.t()
  def encode_record(%Challenge{} = c, key) do
    unless is_binary(c.assay) and String.valid?(c.assay) and not String.contains?(c.assay, ["\t", "\r", "\n"]),
      do: raise(ArgumentError, "invalid corpus assay identity")

    {scaffold, pieces} = Challenge.to_pieces(c)

    pieces64 = pieces |> Enum.map(fn {id, term} -> [id, Serialize.encode(term)] end) |> json64()

    {fault, scaffold_rest} = Map.pop(scaffold, "fault")

    fault_field =
      case fault do
        nil -> []
        fault when is_map(fault) and not is_struct(fault) -> ["fault64=#{encode_fault(fault)}"]
        _ -> raise ArgumentError, "malformed fault metadata"
      end

    line =
      Enum.join(
        [
          @marker,
          "format=#{@format_version}",
          "universe=#{@universe_epoch}",
          "kind=#{c.kind}",
          "assay=#{c.assay}",
          "label=#{c.label}",
          "seed=#{c.seed || "-"}",
          "note=#{enc_note(c.note)}",
          "scaffold=#{encode_scaffold(scaffold_rest)}"
        ] ++
          fault_field ++
          [
            "key=#{Base.encode64(scope_key(key))}",
            "pieces64=#{pieces64}"
          ],
        "\t"
      )

    if byte_size(line) <= @max_record_bytes, do: line, else: raise(ArgumentError, "corpus record budget exceeded")
  end

  @spec decode_record(String.t()) :: {:ok, Challenge.t()} | {:error, term()}
  def decode_record(line) do
    # Force-intern the closed kind/label/name set BEFORE `decode_pieces` runs
    # `Serialize.decode` (which calls `String.to_existing_atom` on family/ctor
    # names like `:Dec`/`:Causal`). Loading `Challenge` interns every literal in
    # its `@known_atoms`; without this, a replay in a process that has not yet
    # loaded `Challenge` (async suite ordering) fails to decode. See spec §7.
    _ = Challenge.__known_atoms__()

    with {:ok, m} <- current_fields(line),
         {:ok, pieces} <- decode_pieces64(m["pieces64"]) do
      kind = Challenge.known_atom!(m["kind"])
      label = Challenge.known_atom!(m["label"])
      seed = if m["seed"] == "-", do: nil, else: String.to_integer(m["seed"])
      base_scaffold = decode_scaffold(m["scaffold"] || "-")
      if Map.has_key?(base_scaffold, "fault"), do: raise(ArgumentError, "fault metadata requires fault64")

      scaffold =
        case m["fault64"] do
          nil -> base_scaffold
          f_str -> Map.put(base_scaffold, "fault", decode_fault(f_str))
        end

      note = dec_note(m["note"])

      with {:ok, challenge} <- Challenge.safe_from_pieces(kind, m["assay"], label, seed, note, scaffold, pieces),
           :ok <- exact_pieces(challenge, scaffold, pieces) do
        {:ok, challenge}
      end
    else
      other -> {:error, {:bad_record, other}}
    end
  rescue
    e -> {:error, e}
  end

  @doc "Encode arbitrary (non-Term) challenge metadata for the `scaffold=` field. `%{}` → `\"-\"`."
  @spec encode_scaffold(map()) :: String.t()
  def encode_scaffold(scaffold) when scaffold == %{}, do: "-"

  def encode_scaffold(scaffold) when is_map(scaffold) and not is_struct(scaffold) do
    opaque_budget!(scaffold)
    Base.encode64(:erlang.term_to_binary(scaffold, [:deterministic]))
  end

  @doc "Decode the `scaffold=` field. `:safe` refuses to mint new atoms on decode — see the safety note in the plan."
  @spec decode_scaffold(String.t()) :: map()
  def decode_scaffold("-"), do: %{}

  def decode_scaffold(b64) when is_binary(b64) and byte_size(b64) <= @max_record_bytes do
    binary = Base.decode64!(b64)

    case binary do
      <<131, 80, _::binary>> -> raise ArgumentError, "compressed corpus scaffold is not current syntax"
      _ -> :ok
    end

    {scaffold, used} = :erlang.binary_to_term(binary, [:safe, :used])

    unless used == byte_size(binary) and is_map(scaffold) and not is_struct(scaffold),
      do: raise(ArgumentError, "malformed corpus scaffold")

    opaque_budget!(scaffold)
    scaffold
  end

  def decode_scaffold(_), do: raise(ArgumentError, "corpus scaffold budget exceeded")

  @spec append(String.t(), Challenge.t(), String.t()) ::
          :appended | :duplicate | {:rejected, term()}
  def append(path, %Challenge{} = c, dedup_key) do
    dedup_key = scope_key(dedup_key)
    File.mkdir_p!(Path.dirname(path))

    if seen?(path, dedup_key) do
      :duplicate
    else
      # Portability self-check BEFORE the write: a record that reconstructs an atom
      # absent from `Challenge.__known_atoms__/0` decodes fine here (the generating VM
      # already interned it) but crashes a fresh replay VM — so never bank it. The
      # check re-decodes the very line we would append; membership (not interning) is
      # what `known_atom!` enforces, so this catches the poison the local VM can't feel.
      line = encode_record(c, dedup_key)

      case portability_check(line) do
        :ok ->
          # single append syscall — atomic per record (spec §7.1)
          File.write!(path, line <> "\n", [:append])
          :appended

        {:error, reason} ->
          {:rejected, reason}
      end
    end
  rescue
    exception -> {:rejected, exception}
  end

  # A malformed current record must never be banked, regardless of which
  # structural decoder refused it. This check is not kernel admission.
  defp portability_check(line) do
    case decode_record(line) do
      {:ok, _} -> :ok
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Merge `sources` (record files) into `dest`, deduplicating by each record's own
  embedded `key=` field — the same key `append/3`/`seen?/2` use. Records are copied
  **verbatim** (raw lines, never decoded→re-encoded), so the merge is byte-preserving
  and cannot mint atoms; it is kind-agnostic (corpus OR seeds) because it trusts each
  record's stored key. Deduplicates across sources within one call too. Lines with no
  extractable key are skipped and counted (a keyless line has no dedup identity).
  Missing / empty sources contribute nothing. Returns an `%{added, duplicate, keyless}`
  tally.
  """
  @spec merge(String.t(), [String.t()]) :: %{
          added: non_neg_integer(),
          duplicate: non_neg_integer(),
          keyless: non_neg_integer()
        }
  def merge(dest, sources) when is_list(sources) do
    File.mkdir_p!(Path.dirname(dest))

    seen0 =
      dest |> record_lines() |> Enum.map(&raw_key/1) |> Enum.reject(&is_nil/1) |> MapSet.new()

    {rev_new, tally, _seen} =
      Enum.reduce(sources, {[], %{added: 0, duplicate: 0, keyless: 0}, seen0}, fn src, acc ->
        Enum.reduce(record_lines(src), acc, fn line, {out, t, seen} ->
          case raw_key(line) do
            nil ->
              {out, %{t | keyless: t.keyless + 1}, seen}

            key ->
              if MapSet.member?(seen, key) do
                {out, %{t | duplicate: t.duplicate + 1}, seen}
              else
                {[line | out], %{t | added: t.added + 1}, MapSet.put(seen, key)}
              end
          end
        end)
      end)

    case Enum.reverse(rev_new) do
      [] -> :ok
      lines -> File.write!(dest, newline_guard(dest) <> Enum.join(lines, "\n") <> "\n", [:append])
    end

    tally
  end

  @doc """
  Non-blank, newline-trimmed record lines of a file (empty list if the file is
  absent). Raw lines — no decode — so callers preserve byte identity. Used by
  `merge/2` and `Antigen.Prune`.
  """
  @spec record_lines(String.t()) :: [String.t()]
  def record_lines(path) do
    if File.exists?(path) do
      path |> File.stream!() |> Enum.map(&String.trim_trailing(&1, "\n")) |> Enum.reject(&(&1 == ""))
    else
      []
    end
  end

  # A leading "\n" iff `dest` is non-empty and does not already end in one, so an
  # appended record can never be glued onto a hand-edited last line without a newline.
  defp newline_guard(dest) do
    case File.read(dest) do
      {:ok, ""} -> ""
      {:ok, content} -> if String.ends_with?(content, "\n"), do: "", else: "\n"
      _ -> ""
    end
  end

  @spec stream(String.t()) :: Enumerable.t()
  def stream(path) do
    if File.exists?(path) do
      path
      |> File.stream!()
      |> Stream.map(fn line ->
        case decode_record(line) do
          {:ok, c} -> {:ok, c}
          {:error, reason} -> {:decode_error, String.trim(line), reason}
        end
      end)
    else
      []
    end
  end

  @spec dedup_key(Challenge.t(), :antibody | :seed) :: String.t()
  def dedup_key(%Challenge{} = c, :seed), do: scope_key(Coverage.key_string(Coverage.key(c)))

  def dedup_key(%Challenge{} = challenge, :antibody) do
    digest = challenge |> semantic_descriptor() |> UniverseCodec.semantic_hash() |> Base.encode16(case: :lower)
    scope_key("antibody/#{@antibody_version}|" <> digest)
  end

  @doc """
  Bounded deterministic antibody identity, excluding only nonsemantic capture
  metadata (`seed`, `note`, `cover_tag`). No normalization or inference occurs.

  The ordered descriptor includes the complete kind-specific scaffold, fault
  provenance and ordered canonical Core pieces. Thus zero-piece recipes and
  raw decoder inputs do not collapse merely because they have no Core pieces.
  """
  @spec semantic_descriptor(Challenge.t()) :: binary()
  def semantic_descriptor(%Challenge{} = challenge) do
    {scaffold, pieces} = Challenge.to_pieces(challenge)
    {fault, scaffold} = Map.pop(scaffold, "fault")
    fault = if is_nil(fault), do: "-", else: encode_fault(fault)

    descriptor = [
      ["identity", "antibody/#{@antibody_version}"],
      ["universe", @universe_epoch],
      ["kind", Atom.to_string(challenge.kind)],
      ["assay", challenge.assay],
      ["label", Atom.to_string(challenge.label)],
      ["scaffold", encode_scaffold(scaffold)],
      ["fault64", fault],
      ["pieces", Enum.map(pieces, fn {id, term} -> [id, Serialize.encode(term)] end)]
    ]

    case UniverseCodec.budget(descriptor) do
      :ok -> descriptor |> :json.encode() |> IO.iodata_to_binary()
      {:error, reason} -> raise ArgumentError, "antibody identity budget exceeded: #{inspect(reason)}"
    end
  end

  defp seen?(path, key) do
    File.exists?(path) and
      path |> File.stream!() |> Enum.any?(fn line -> extract_key(line) == key end)
  end

  @doc "The Base64-decoded stored dedup key of one record line, or nil if absent."
  @spec raw_key(String.t()) :: binary() | nil
  def raw_key(line) do
    case current_fields(line) do
      {:ok, fields} -> Base.decode64!(fields["key"])
      {:error, _} -> nil
    end
  rescue
    _ -> nil
  end

  defp extract_key(line), do: raw_key(line)

  defp current_fields(line) when is_binary(line) and byte_size(line) <= @max_record_bytes do
    line = if String.ends_with?(line, "\n"), do: binary_part(line, 0, byte_size(line) - 1), else: line

    with true <- String.valid?(line),
         [@marker | fields] <- String.split(line, "\t", parts: length(@required_fields) + length(@optional_fields) + 2),
         {:ok, fields} <- field_map(fields),
         true <- Enum.all?(@required_fields, &Map.has_key?(fields, &1)),
         true <- fields["format"] == Integer.to_string(@format_version),
         true <- fields["universe"] == @universe_epoch,
         true <- byte_size(fields["seed"]) <= UniverseCodec.max_digits() + 1,
         {:ok, key} <- Base.decode64(fields["key"]),
         true <- String.starts_with?(key, @key_prefix) do
      {:ok, fields}
    else
      _ -> {:error, :incompatible_or_malformed_corpus_record}
    end
  end

  defp current_fields(_), do: {:error, :corpus_record_budget_exceeded}

  defp field_map(fields) do
    Enum.reduce_while(fields, {:ok, %{}}, fn field, {:ok, acc} ->
      case String.split(field, "=", parts: 2) do
        [key, value] when key in @required_fields or key in @optional_fields ->
          if Map.has_key?(acc, key) or String.contains?(value, ["\n", "\r"]),
            do: {:halt, {:error, :duplicate_or_malformed_corpus_field}},
            else: {:cont, {:ok, Map.put(acc, key, value)}}

        _ ->
          {:halt, {:error, :unknown_corpus_field}}
      end
    end)
  end

  defp scope_key(@key_prefix <> _ = key), do: key
  defp scope_key(key) when is_binary(key), do: @key_prefix <> key

  defp opaque_budget!(value) do
    opaque_budget(value, 0, UniverseCodec.max_nodes())
    :ok
  end

  defp opaque_budget(_value, depth, remaining) when depth > 256 or remaining <= 0,
    do: raise(ArgumentError, "corpus scaffold budget exceeded")

  defp opaque_budget(value, depth, remaining) when is_map(value) and not is_struct(value) do
    if map_size(value) > remaining, do: raise(ArgumentError, "corpus scaffold budget exceeded")

    Enum.reduce(value, remaining - 1, fn
      {key, child}, budget when is_binary(key) ->
        opaque_budget(child, depth + 1, opaque_budget(key, depth + 1, budget))

      _, _ ->
        raise ArgumentError, "invalid corpus scaffold key"
    end)
  end

  defp opaque_budget(value, depth, remaining) when is_tuple(value),
    do: opaque_list(Tuple.to_list(value), depth + 1, remaining - 1)

  defp opaque_budget(value, depth, remaining) when is_list(value),
    do: opaque_list(value, depth + 1, remaining - 1)

  defp opaque_budget(value, _depth, remaining)
       when is_binary(value) or is_number(value) or is_atom(value),
       do: remaining - 1

  defp opaque_budget(_, _, _), do: raise(ArgumentError, "invalid corpus scaffold value")
  defp opaque_list([], _depth, remaining), do: remaining

  defp opaque_list([head | tail], depth, remaining),
    do: opaque_list(tail, depth, opaque_budget(head, depth, remaining))

  defp opaque_list(_, _, _), do: raise(ArgumentError, "improper corpus scaffold list")

  defp json64(value), do: value |> :json.encode() |> IO.iodata_to_binary() |> Base.encode64()

  defp decode_json64(encoded) when is_binary(encoded) and byte_size(encoded) <= @max_record_bytes do
    with {:ok, json} <- Base.decode64(encoded),
         :ok <- json_input_budget(json),
         {value, :ok, rest} <- :json.decode(json, :ok, json_decoders()),
         true <- String.trim(rest) == "",
         :ok <- UniverseCodec.budget(value) do
      {:ok, value}
    else
      {:error, _} = error -> error
      _ -> {:error, :invalid_corpus_json}
    end
  rescue
    _ -> {:error, :invalid_corpus_json}
  end

  defp decode_json64(_), do: {:error, :invalid_corpus_json}

  defp json_decoders do
    %{
      object_start: fn _ -> %{} end,
      object_push: fn key, value, map ->
        if Map.has_key?(map, key) or map_size(map) >= UniverseCodec.max_atoms(),
          do: raise(ArgumentError, "duplicate or oversized corpus JSON object")

        Map.put(map, key, value)
      end,
      object_finish: fn map, old -> {map, old} end,
      array_start: fn _ -> {0, []} end,
      array_push: fn value, {count, values} ->
        if count >= UniverseCodec.max_atoms(), do: raise(ArgumentError, "oversized corpus JSON array")
        {count + 1, [value | values]}
      end,
      array_finish: fn {_count, values}, old -> {Enum.reverse(values), old} end
    }
  end

  defp decode_pieces64(encoded) do
    with {:ok, rows} <- decode_json64(encoded),
         :ok <- UniverseCodec.bounded(rows, UniverseCodec.max_atoms()),
         {:ok, pieces} <- decode_piece_rows(rows, %{}, []),
         :ok <- UniverseCodec.budget(Enum.map(pieces, fn {id, term} -> [id, Term.to_external_node(term)] end)) do
      {:ok, pieces}
    end
  end

  defp decode_piece_rows([], _seen, acc), do: {:ok, Enum.reverse(acc)}

  defp decode_piece_rows([[id, body] | rest], seen, acc)
       when is_binary(id) and byte_size(id) > 0 and byte_size(id) <= 1024 and is_binary(body) do
    if Map.has_key?(seen, id) do
      {:error, :duplicate_corpus_piece_id}
    else
      with {:ok, term} <- Serialize.decode(body) do
        decode_piece_rows(rest, Map.put(seen, id, true), [{id, term} | acc])
      end
    end
  end

  defp decode_piece_rows(_, _, _), do: {:error, :malformed_corpus_piece}

  defp exact_pieces(challenge, scaffold, pieces) do
    {expected_scaffold, expected_pieces} = Challenge.to_pieces(challenge)

    if expected_scaffold == scaffold and expected_pieces == pieces do
      fault_terms =
        case scaffold["fault"] do
          fault when is_map(fault) -> for {_key, term} <- fault, is_tuple(term), Term.term?(term), do: term
          _ -> []
        end

      core = Enum.map(pieces, fn {id, term} -> [id, Term.to_external_node(term)] end)
      diagnostics = Enum.map(fault_terms, &Term.to_external_node/1)
      UniverseCodec.budget(core ++ diagnostics)
    else
      {:error, :noncanonical_corpus_pieces_or_scaffold}
    end
  end

  defp json_input_budget(json), do: scan_json(json, 0, false, false, 0)

  defp scan_json(_rest, depth, _quoted, _escaped, digits) when depth > 256 or digits > 4096,
    do: {:error, :corpus_json_budget_exceeded}

  defp scan_json(<<>>, _depth, _quoted, _escaped, _digits), do: :ok
  defp scan_json(<<_, rest::binary>>, depth, true, true, _digits), do: scan_json(rest, depth, true, false, 0)
  defp scan_json(<<?\\, rest::binary>>, depth, true, false, _digits), do: scan_json(rest, depth, true, true, 0)
  defp scan_json(<<?", rest::binary>>, depth, quoted, false, _digits), do: scan_json(rest, depth, not quoted, false, 0)
  defp scan_json(<<_, rest::binary>>, depth, true, false, _digits), do: scan_json(rest, depth, true, false, 0)

  defp scan_json(<<open, rest::binary>>, depth, false, false, _digits) when open in [?[, ?{],
    do: scan_json(rest, depth + 1, false, false, 0)

  defp scan_json(<<close, rest::binary>>, depth, false, false, _digits) when close in [?], ?}],
    do: scan_json(rest, depth - 1, false, false, 0)

  defp scan_json(<<digit, rest::binary>>, depth, false, false, digits) when digit in ?0..?9,
    do: scan_json(rest, depth, false, false, digits + 1)

  defp scan_json(<<_, rest::binary>>, depth, false, false, _digits), do: scan_json(rest, depth, false, false, 0)

  # Faults are diagnostic metadata, not checked Core or proof evidence. A Core
  # syntax witness is tagged explicitly and decoded by the strict current
  # syntax codec; malformed diagnostic trees never acquire a Core identity.
  defp encode_fault(map) do
    validate_fault!(map)
    map |> Map.new(fn {key, value} -> {Atom.to_string(key), enc_fault_val(value)} end) |> json64()
  end

  defp enc_fault_val(nil), do: %{"tag" => "nil"}
  defp enc_fault_val(value) when is_integer(value), do: %{"tag" => "integer", "value" => value}
  defp enc_fault_val({a, b}) when is_integer(a) and is_integer(b), do: %{"tag" => "pair", "value" => [a, b]}

  defp enc_fault_val(value) when is_atom(value) do
    name = Atom.to_string(value)
    Challenge.known_atom!(name)
    %{"tag" => "atom", "value" => name}
  end

  defp enc_fault_val(value) when is_list(value) do
    names = Enum.map(value, fn atom -> atom |> Atom.to_string() |> tap(&Challenge.known_atom!/1) end)
    %{"tag" => "list", "value" => names}
  end

  defp enc_fault_val(value) when is_tuple(value) do
    if Term.term?(value),
      do: %{"tag" => "core_syntax", "value" => Serialize.encode(value)},
      else: raise(ArgumentError, "malformed Core syntax in diagnostic metadata")
  end

  defp enc_fault_val(_), do: raise(ArgumentError, "unsupported fault metadata value")

  defp decode_fault(encoded) do
    with {:ok, map} when is_map(map) <- decode_json64(encoded) do
      fault =
        Map.new(map, fn {key, value} ->
          unless key in @fault_keys, do: raise(ArgumentError, "unknown fault metadata key")
          {Challenge.known_atom!(key), dec_fault_val(value)}
        end)

      validate_fault!(fault)
      fault
    else
      _ -> raise ArgumentError, "malformed fault metadata"
    end
  end

  defp dec_fault_val(%{"tag" => "nil"} = value) when map_size(value) == 1, do: nil

  defp dec_fault_val(%{"tag" => "integer", "value" => number} = value)
       when map_size(value) == 2 and is_integer(number), do: number

  defp dec_fault_val(%{"tag" => "pair", "value" => [a, b]} = value)
       when map_size(value) == 2 and is_integer(a) and is_integer(b), do: {a, b}

  defp dec_fault_val(%{"tag" => "atom", "value" => name} = value)
       when map_size(value) == 2 and is_binary(name), do: Challenge.known_atom!(name)

  defp dec_fault_val(%{"tag" => "list", "value" => names} = value)
       when map_size(value) == 2 and is_list(names), do: Enum.map(names, &Challenge.known_atom!/1)

  defp dec_fault_val(%{"tag" => "core_syntax", "value" => wire} = value)
       when map_size(value) == 2 and is_binary(wire) do
    case Serialize.decode(wire) do
      {:ok, term} -> term
      {:error, _} -> raise ArgumentError, "malformed Core syntax in diagnostic metadata"
    end
  end

  defp dec_fault_val(_), do: raise(ArgumentError, "unknown or malformed fault metadata tag")

  defp validate_fault!(map) do
    Enum.each(map, fn {key, _value} ->
      unless is_atom(key) and Atom.to_string(key) in @fault_keys,
        do: raise(ArgumentError, "unknown fault metadata key")

      Challenge.known_atom!(Atom.to_string(key))
    end)

    if Map.has_key?(map, :depth) and not (is_integer(map.depth) and map.depth >= 0 and map.depth <= 256),
      do: raise(ArgumentError, "invalid fault depth")

    if Map.has_key?(map, :wrap_path) and
         not (is_list(map.wrap_path) and length(map.wrap_path) <= 256 and
                Enum.all?(map.wrap_path, &(&1 in @fault_paths))),
       do: raise(ArgumentError, "invalid fault wrapper path")

    :ok
  end

  # note: nil -> "-"; a literal "-" -> "%2D"; else percent-escape %/tab/newline.
  # `%` MUST be escaped first (its own escape introduces further `%`).
  defp enc_note(nil), do: "-"
  defp enc_note("-"), do: "%2D"

  defp enc_note(s) do
    s
    |> String.replace("%", "%25")
    |> String.replace("\t", "%09")
    |> String.replace("\n", "%0A")
    |> String.replace("\r", "%0D")
  end

  defp dec_note("-"), do: nil

  defp dec_note(s) do
    s
    |> String.replace("%2D", "-")
    |> String.replace("%09", "\t")
    |> String.replace("%0A", "\n")
    |> String.replace("%0D", "\r")
    |> String.replace("%25", "%")
  end
end
