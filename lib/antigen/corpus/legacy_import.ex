defmodule Antigen.Corpus.LegacyImport do
  @moduledoc """
  Explicit offline import of the fixed-ceiling corpus era.

  This module is never called by `Corpus.decode_record/1`. It reconstructs
  unchecked syntax, not typing/certification evidence. A current-format failure
  is returned unchanged and never retried as historical input.
  """

  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.{Serialize, Sort, Term, UniverseCodec}

  @required ~w(kind assay label seed note scaffold key pieces)
  @optional ~w(fault)
  @metadata_atoms [:accept, :certified, :delta, :fuel, :fuel_exhausted, :mode, :stuck_cases, :whnf]
  @diagnostic_atoms ~w(type var pi lam let app data ctor case global prim int_type int_lit float_type float_lit nat_lit bounded_lit bounded_type atom_type atom_lit binary_type hole absurd effect_type effect_pure effect_bind linear affine)a
  @fault_keys ~w(kind witness expected_head injected_head scope depth wrap_path expected_index actual_index reduction required carrier)
  @bool_names %{True: :"Std.Bool#True", False: :"Std.Bool#False"}
  @max_bytes UniverseCodec.max_bytes()
  @recipe_fixture Path.expand("../../../test/antigen/fixtures/phase5_kernel_recipe_replacements.json", __DIR__)
  @recipe_fixture_sha "5522d0453cde53b8435551d4d410745ef66ac1de05d4dfe0fd310b39ba34af2d"

  @doc false
  def reviewed_recipe_fixture do
    bytes = File.read!(@recipe_fixture)

    unless Base.encode16(:crypto.hash(:sha256, bytes), case: :lower) == @recipe_fixture_sha,
      do: raise(ArgumentError, "reviewed recipe fixture hash mismatch")

    :json.decode(bytes)
  end

  defp reviewed_replacements do
    reviewed_recipe_fixture()["replacements"]
    |> Enum.reject(&(&1["stored_record_retag_required"] == false))
    |> Map.new(&{&1["old_tag"], &1})
  end

  @spec decode_record(binary(), keyword()) :: {:ok, map()} | {:error, term()}
  def decode_record(line, opts \\ []) do
    bootstrap_symbols()

    with :ok <- era(opts),
         {:ok, fields} <- fields(line) do
      if Enum.any?(~w(format universe pieces64), &Map.has_key?(fields, &1)) do
        case Corpus.decode_record(line) do
          {:ok, challenge} -> {:ok, %{challenge: challenge, fields: fields, actions: [], current: true}}
          {:error, reason} -> {:error, {:current_record_rejected, reason}}
        end
      else
        historical(fields, opts)
      end
    end
  rescue
    exception -> {:error, exception}
  end

  @doc "Load only trusted closed symbol declarations; never intern record strings."
  def bootstrap_symbols do
    Code.ensure_loaded!(Cure.Core.Builtins)
    _ = Challenge.__known_atoms__()
    :ok
  end

  defp era(opts) do
    if Keyword.get(opts, :from) == :fixed_ceiling_v1,
      do: :ok,
      else: {:error, :explicit_historical_era_required}
  end

  defp fields(line) when is_binary(line) and byte_size(line) <= @max_bytes do
    unless String.valid?(line), do: raise(ArgumentError, "invalid UTF-8 historical record")
    line = if String.ends_with?(line, "\n"), do: binary_part(line, 0, byte_size(line) - 1), else: line

    case String.split(line, "\t", parts: 16) do
      ["antigen-record" | fields] ->
        Enum.reduce_while(fields, {:ok, %{}}, fn field, {:ok, acc} ->
          case String.split(field, "=", parts: 2) do
            [key, value] ->
              if Map.has_key?(acc, key) or String.contains?(value, ["\t", "\r", "\n"]),
                do: {:halt, {:error, :duplicate_or_multiline_historical_field}},
                else: {:cont, {:ok, Map.put(acc, key, value)}}

            _ ->
              {:halt, {:error, :malformed_historical_field}}
          end
        end)

      _ ->
        {:error, :not_a_corpus_record}
    end
  end

  defp fields(_), do: {:error, :historical_record_budget_exceeded}

  defp historical(fields, opts) do
    with true <- Enum.all?(@required, &Map.has_key?(fields, &1)),
         true <- Map.keys(fields) -- (@required ++ @optional) == [],
         :ok <- legacy_key(fields["key"]),
         {:ok, pieces, base64?} <- pieces(fields["pieces"]),
         {:ok, scaffold} <- scaffold(fields["scaffold"]) do
      scaffold =
        if fields["fault"] do
          if Map.has_key?(scaffold, "fault"), do: raise(ArgumentError, "duplicate historical fault carrier")
          Map.put(scaffold, "fault", fault(fields["fault"]))
        else
          Map.update(scaffold, "fault", nil, &lift_embedded_fault/1)
          |> then(fn map -> if is_nil(map["fault"]), do: Map.delete(map, "fault"), else: map end)
        end

      {scaffold, pieces, actions} = family_sorts(fields["kind"], scaffold, pieces)
      {scaffold, actions} = decode_input(fields, scaffold, actions)

      {scaffold, actions} =
        recipe(scaffold, Keyword.get_lazy(opts, :recipe_replacements, &reviewed_replacements/0), actions)

      {scaffold, pieces, actions} = bool_names(scaffold, pieces, actions, Keyword.get(opts, :bool_qnames, true))
      seed = integer(fields["seed"], true)
      note = note(fields["note"], base64?)
      kind = Challenge.known_atom!(fields["kind"])
      label = Challenge.known_atom!(fields["label"])

      with {:ok, challenge} <-
             Challenge.safe_from_pieces(kind, fields["assay"], label, seed, note, scaffold, pieces),
           true <- Challenge.to_pieces(challenge) == {scaffold, pieces} do
        {:ok, %{challenge: challenge, fields: fields, actions: Enum.reverse(actions), current: false}}
      else
        false -> {:error, :historical_scaffold_or_piece_loss}
        error -> error
      end
    else
      false -> {:error, :unknown_or_missing_historical_fields}
      {:error, _} = error -> error
    end
  end

  defp legacy_key(encoded) do
    with {:ok, key} <- Base.decode64(encoded),
         true <- key != "" and String.valid?(key),
         true <- Base.encode64(key) == encoded,
         false <- String.contains?(key, ["\t", "\r", "\n", <<0>>]) do
      :ok
    else
      _ -> {:error, :malformed_historical_key}
    end
  end

  defp pieces(""), do: {:ok, [], false}

  defp pieces(string) do
    rows = String.split(string, ";;")
    :ok = UniverseCodec.bounded(rows, UniverseCodec.max_atoms())

    Enum.reduce_while(rows, {:ok, [], MapSet.new(), false}, fn row, {:ok, acc, seen, encoded?} ->
      case String.split(row, "::", parts: 2) do
        [id, body] when byte_size(id) > 0 and byte_size(id) <= 1024 ->
          if MapSet.member?(seen, id) do
            {:halt, {:error, :duplicate_historical_piece}}
          else
            base64? = not String.starts_with?(body, "(")

            if MapSet.size(seen) > 0 and encoded? != base64?,
              do: raise(ArgumentError, "mixed historical piece carrier grammars")

            body = if base64?, do: Base.decode64!(body), else: body

            case Serialize.decode_legacy(body) do
              {:ok, term} ->
                validate_symbols!(term)
                {:cont, {:ok, [{id, term} | acc], MapSet.put(seen, id), encoded? or base64?}}

              {:error, reason} ->
                {:halt, {:error, {:historical_piece_rejected, id, reason}}}
            end
          end

        _ ->
          {:halt, {:error, :malformed_historical_piece}}
      end
    end)
    |> case do
      {:ok, reversed, _seen, base64?} -> {:ok, Enum.reverse(reversed), base64?}
      error -> error
    end
  end

  defp scaffold("-"), do: {:ok, %{}}

  defp scaffold(encoded) do
    binary = Base.decode64!(encoded)
    if match?(<<131, 80, _::binary>>, binary), do: raise(ArgumentError, "compressed historical scaffold")
    {value, used} = :erlang.binary_to_term(binary, [:safe, :used])

    unless used == byte_size(binary) and is_map(value) and not is_struct(value),
      do: raise(ArgumentError, "malformed historical scaffold")

    metadata(value, 0, UniverseCodec.max_nodes())
    {:ok, value}
  end

  defp metadata(_value, depth, budget) when depth > 256 or budget <= 0,
    do: raise(ArgumentError, "historical metadata budget exceeded")

  defp metadata(value, depth, budget) when is_map(value) and not is_struct(value),
    do:
      Enum.reduce(value, budget - 1, fn {key, child}, b -> metadata(child, depth + 1, metadata(key, depth + 1, b)) end)

  defp metadata(value, depth, budget) when is_tuple(value), do: metadata(Tuple.to_list(value), depth + 1, budget - 1)

  defp metadata(value, depth, budget) when is_list(value),
    do: Enum.reduce(value, budget - 1, &metadata(&1, depth + 1, &2))

  defp metadata(value, _depth, budget) when is_integer(value) do
    :ok = UniverseCodec.natural(abs(value))
    budget - 1
  end

  defp metadata(value, _depth, budget) when is_binary(value) or is_float(value), do: budget - 1
  defp metadata(value, _depth, budget) when value in [nil, true, false], do: budget - 1

  defp metadata(value, _depth, budget) when is_atom(value) do
    unless value in @metadata_atoms or value in @diagnostic_atoms or value in Challenge.__known_atoms__(),
      do: raise(ArgumentError, "unknown historical metadata atom")

    budget - 1
  end

  defp metadata(_, _, _), do: raise(ArgumentError, "runtime object in historical metadata")

  defp family_sorts("family", scaffold, pieces) do
    {scaffold, piece} = family_sort(scaffold, "fam_sort")
    {scaffold, [piece | pieces], [%{"action" => "family_sort_piece", "id" => "fam_sort"}]}
  end

  defp family_sorts(kind, scaffold, pieces) when kind in ["indexed_case", "rewrite_eq"] do
    prefixes = scaffold["families"] |> Enum.with_index() |> Enum.map(fn {_, index} -> "fam:#{index}:" end)

    if Enum.any?(pieces, fn {id, _} ->
         String.starts_with?(id, "fam:") and not Enum.any?(prefixes, &String.starts_with?(id, &1))
       end),
       do: raise(ArgumentError, "orphan historical family piece")

    {families, groups} =
      scaffold["families"]
      |> Enum.with_index()
      |> Enum.map_reduce([], fn {family, index}, acc ->
        prefix = "fam:#{index}:"
        {family, sort} = family_sort(family, prefix <> "sort")
        {family, acc ++ [sort | Enum.filter(pieces, fn {id, _} -> String.starts_with?(id, prefix) end)]}
      end)

    rest = Enum.reject(pieces, fn {id, _} -> String.starts_with?(id, "fam:") end)
    {Map.put(scaffold, "families", families), groups ++ rest, [%{"action" => "nested_family_sort_pieces"}]}
  end

  defp family_sorts(_, scaffold, pieces), do: {scaffold, pieces, []}

  defp family_sort(scaffold, id) do
    unless Map.has_key?(scaffold, "fam_level"), do: raise(ArgumentError, "missing historical family level")
    level = Map.fetch!(scaffold, "fam_level")
    unless level in 0..2, do: raise(ArgumentError, "family level is outside fixed-ceiling era")
    {Map.delete(scaffold, "fam_level"), {id, {:type, Sort.finite_closed(level)}}}
  end

  defp decode_input(%{"kind" => "decode_probe", "label" => "valid_sexp"}, scaffold, actions) do
    old = Map.fetch!(scaffold, "input")
    {:ok, term} = Serialize.decode_legacy(old)
    validate_symbols!(term)
    current = Serialize.encode(term)

    {Map.put(scaffold, "input", current),
     [%{"action" => "current_valid_decoder_input", "before" => old, "after" => current} | actions]}
  end

  defp decode_input(%{"kind" => "decode_probe", "label" => "invalid_sexp"}, scaffold, actions) do
    old = Map.fetch!(scaffold, "input")

    current =
      case old do
        "" ->
          ""

        "5 6" ->
          "(cure-core 2 (int 0)) " <> old

        "(case (var 0) (type 0) (branch Z -3 (var 0)))" ->
          "(cure-core 2 (case (var 0) (type (finite (level-nf 0))) (branch Z -3 (var 0))))"

        _ ->
          "(cure-core 2 " <> old <> ")"
      end

    unless match?({:error, _}, Serialize.decode(current)),
      do: raise(ArgumentError, "historical negative changed polarity")

    {Map.put(scaffold, "input", current),
     [%{"action" => "current_invalid_decoder_input", "before" => old, "after" => current} | actions]}
  end

  defp decode_input(_, scaffold, actions), do: {scaffold, actions}

  defp validate_symbols!({tag, name, args}) when tag in [:ctor, :prim] do
    if tag == :ctor, do: Challenge.known_atom!(Atom.to_string(name))
    Enum.each(args, &validate_symbols!/1)
  end

  defp validate_symbols!({:data, name, params, indices}) do
    Challenge.known_atom!(Atom.to_string(name))
    Enum.each(params ++ indices, &validate_symbols!/1)
  end

  defp validate_symbols!({tag, name}) when tag in [:global, :atom_lit],
    do: Challenge.known_atom!(Atom.to_string(name))

  defp validate_symbols!({:case, scrut, motive, branches}) do
    validate_symbols!(scrut)
    validate_symbols!(motive)

    Enum.each(branches, fn {name, _arity, body} ->
      Challenge.known_atom!(Atom.to_string(name))
      validate_symbols!(body)
    end)
  end

  defp validate_symbols!(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.each(&validate_symbols!/1)

  defp validate_symbols!(list) when is_list(list), do: Enum.each(list, &validate_symbols!/1)
  defp validate_symbols!(_), do: :ok

  defp recipe(%{"probe" => old} = scaffold, replacements, actions) do
    case Map.fetch(replacements, old) do
      {:ok, replacement} ->
        new = Map.fetch!(replacement, "new_tag")
        Challenge.known_atom!(new)

        {Map.put(scaffold, "probe", new),
         [
           %{
             "action" => "reviewed_recipe_replacement",
             "before" => old,
             "after" => new,
             "reviewed_fixture_entry" => replacement,
             "fixture_sha256" => @recipe_fixture_sha
           }
           | actions
         ]}

      :error ->
        {scaffold, actions}
    end
  end

  defp recipe(scaffold, _replacements, actions), do: {scaffold, actions}

  defp bool_names(scaffold, pieces, actions, false), do: {scaffold, pieces, actions}

  defp bool_names(scaffold, pieces, actions, true) do
    renamed = Enum.map(pieces, fn {id, term} -> {id, rename_bool(term)} end)
    scaffold = rename_bool_declarations(scaffold)
    actions = if renamed == pieces, do: actions, else: [%{"action" => "reviewed_bool_ctor_and_branch_qnames"} | actions]
    {scaffold, renamed, actions}
  end

  @doc false
  def rename_bool({:ctor, name, args}), do: {:ctor, Map.get(@bool_names, name, name), Enum.map(args, &rename_bool/1)}

  def rename_bool({:case, scrut, motive, branches}),
    do:
      {:case, rename_bool(scrut), rename_bool(motive),
       Enum.map(branches, fn {name, arity, body} -> {Map.get(@bool_names, name, name), arity, rename_bool(body)} end)}

  def rename_bool(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.map(&rename_bool/1) |> List.to_tuple()

  def rename_bool(list) when is_list(list), do: Enum.map(list, &rename_bool/1)
  def rename_bool(value), do: value

  defp rename_bool_declarations(%{"fam_name" => "Bool", "ctors" => ctors} = family),
    do:
      Map.put(
        family,
        "ctors",
        Enum.map(ctors, fn ctor ->
          Map.update!(ctor, "name", fn name -> if name in ["True", "False"], do: "Std.Bool#" <> name, else: name end)
        end)
      )

  defp rename_bool_declarations(%{"families" => families} = scaffold),
    do: Map.put(scaffold, "families", Enum.map(families, &rename_bool_declarations/1))

  defp rename_bool_declarations(scaffold), do: scaffold

  defp fault(string) do
    tokens = Regex.scan(~r/\(|\)|[^()\s]+/, string) |> List.flatten()
    :ok = UniverseCodec.bounded(tokens, UniverseCodec.max_nodes())
    {tree, []} = parse(tokens, 0)

    Enum.reduce(tree, %{}, fn
      [key | values], acc when key in @fault_keys ->
        key = Challenge.known_atom!(key)
        if Map.has_key?(acc, key), do: raise(ArgumentError, "duplicate historical fault key")
        Map.put(acc, key, fault_value(values))

      _, _ ->
        raise(ArgumentError, "unknown historical fault key")
    end)
  end

  defp parse(_tokens, depth) when depth > 256, do: raise(ArgumentError, "historical fault nesting exceeded")
  defp parse(["(" | rest], depth), do: parse_list(rest, depth + 1, [])
  defp parse([word | rest], _depth) when word not in ["(", ")"], do: {word, rest}
  defp parse(_, _), do: raise(ArgumentError, "malformed historical fault")
  defp parse_list([")" | rest], _depth, acc), do: {Enum.reverse(acc), rest}

  defp parse_list(tokens, depth, acc) do
    {value, rest} = parse(tokens, depth)
    parse_list(rest, depth, [value | acc])
  end

  defp fault_value(["nil"]), do: nil
  defp fault_value([["pair", a, b]]), do: {integer(a, false), integer(b, false)}
  defp fault_value([["list" | values]]), do: Enum.map(values, &Challenge.known_atom!/1)

  defp fault_value([["term", tree]]) do
    {:ok, term} = Serialize.decode_legacy(print_tree(tree))
    validate_symbols!(term)
    term
  end

  defp fault_value([word]) do
    if byte_size(word) > UniverseCodec.max_digits() + 1,
      do: raise(ArgumentError, "historical fault scalar budget exceeded")

    if Regex.match?(~r/^-?[0-9]+$/, word), do: integer(word, false), else: Challenge.known_atom!(word)
  end

  defp fault_value(_), do: raise(ArgumentError, "unsupported historical fault value")
  defp print_tree(words) when is_list(words), do: "(" <> Enum.map_join(words, " ", &print_tree/1) <> ")"
  defp print_tree(word) when is_binary(word), do: word

  defp lift_embedded_fault(map) when is_map(map) do
    Map.new(map, fn {key, value} ->
      unless is_atom(key) and Atom.to_string(key) in @fault_keys,
        do: raise(ArgumentError, "unknown embedded historical fault key")

      {key, lift_fault_value(value)}
    end)
  end

  defp lift_embedded_fault(_), do: raise(ArgumentError, "malformed embedded historical fault")
  defp lift_fault_value({a, b} = pair) when is_integer(a) and is_integer(b), do: pair

  defp lift_fault_value(tuple) when is_tuple(tuple) do
    term = lift_diagnostic_tree(tuple)
    unless Term.term?(term), do: raise(ArgumentError, "malformed embedded Core witness")
    validate_symbols!(term)
    term
  end

  defp lift_fault_value(list) when is_list(list), do: Enum.map(list, &lift_fault_value/1)
  defp lift_fault_value(value), do: value

  defp lift_diagnostic_tree({:type, level}) when level in 0..2, do: {:type, Sort.finite_closed(level)}

  defp lift_diagnostic_tree(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.map(&lift_diagnostic_tree/1) |> List.to_tuple()

  defp lift_diagnostic_tree(list) when is_list(list), do: Enum.map(list, &lift_diagnostic_tree/1)
  defp lift_diagnostic_tree(value), do: value

  defp integer("-", true), do: nil

  defp integer(string, _optional) when byte_size(string) <= 4097 do
    digits = if String.starts_with?(string, "-"), do: byte_size(string) - 1, else: byte_size(string)

    unless digits in 1..4096 and Regex.match?(~r/^-?[0-9]+$/, string),
      do: raise(ArgumentError, "historical integer budget or grammar exceeded")

    String.to_integer(string)
  end

  defp integer(_, _), do: raise(ArgumentError, "historical integer budget exceeded")
  defp note("-", _), do: nil
  defp note(string, true), do: Base.decode64!(string)

  defp note(string, false),
    do:
      string
      |> String.replace("%2D", "-")
      |> String.replace("%09", "\t")
      |> String.replace("%0A", "\n")
      |> String.replace("%0D", "\r")
      |> String.replace("%25", "%")
end
