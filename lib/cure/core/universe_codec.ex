defmodule Cure.Core.UniverseCodec do
  @moduledoc """
  Portable representation of canonical maximum-plus levels and finite/limit sorts.

  These helpers reconstruct syntax, not typing evidence. They never normalize
  malformed wire input. Scope, level-atom typing and certified conversion require
  independent contextual kernel admission after decoding.
  """

  alias Cure.Core.UniverseLevel

  @identity {:cure_universe, 1, :max_plus_finite_omega}
  @version 2
  @max_bytes 1_048_576
  @max_nodes 100_000
  @max_depth 256
  @max_digits 4096
  @max_atoms 10_000
  @max_natural Integer.pow(10, @max_digits)

  def identity, do: @identity
  def version, do: @version
  def max_bytes, do: @max_bytes
  def max_nodes, do: @max_nodes
  def max_depth, do: @max_depth
  def max_digits, do: @max_digits
  def max_atoms, do: @max_atoms

  @doc "Domain-separated identity for authenticated semantic data."
  def semantic_hash(data),
    do: :crypto.hash(:sha256, :erlang.term_to_binary({@identity, data}, [:deterministic]))

  @doc "Unframed portable term bytes; does not recursively invoke validation."
  def atom_order_key(term), do: Cure.Core.Serialize.encode_node(term)

  @doc "Expose the stable public normal form without normalizing it."
  def public_nf(%UniverseLevel{constant: constant, atoms: atoms}),
    do: {:level_nf, constant, atoms}

  def public_nf({:level_nf, _, _} = level), do: level

  @doc "Reconstruct an internal level only if the tagged input is already canonical."
  def internal_nf({:level_nf, constant, atoms}) do
    level = %UniverseLevel{constant: constant, atoms: atoms}

    with :ok <- bounded(atoms, @max_atoms),
         :ok <- validate_level(level) do
      {:ok, level}
    end
  end

  def internal_nf(_), do: error(:invalid_level_nf)

  def encode_level(level, encode_atom) when is_function(encode_atom, 1) do
    {:level_nf, constant, atoms} = public_nf(level)

    %{
      "tag" => "level_nf",
      "constant" => constant,
      "atoms" =>
        Enum.map(atoms, fn {atom, offset} ->
          %{"term" => encode_atom.(atom), "offset" => offset}
        end)
    }
  end

  def decode_level(
        %{"tag" => "level_nf", "constant" => constant, "atoms" => atoms} = wire,
        decode_atom
      )
      when map_size(wire) == 3 and is_function(decode_atom, 1) do
    with :ok <- natural(constant),
         :ok <- bounded(atoms, @max_atoms),
         {:ok, entries} <- decode_atoms(atoms, decode_atom, []),
         {:ok, level} <- internal_nf({:level_nf, constant, entries}) do
      {:ok, level}
    end
  end

  def decode_level(_, _), do: error(:invalid_level_nf)

  def encode_sort({:finite, level}, encode_atom),
    do: %{"tag" => "finite", "level" => encode_level(level, encode_atom)}

  def encode_sort({:omega, index}, _encode_atom), do: %{"tag" => "omega", "index" => index}

  def decode_sort(%{"tag" => "finite", "level" => wire} = sort, decode_atom)
      when map_size(sort) == 2 do
    with {:ok, level} <- decode_level(wire, decode_atom), do: {:ok, {:finite, level}}
  end

  def decode_sort(%{"tag" => "omega", "index" => index} = sort, _decode_atom)
      when map_size(sort) == 2 do
    with :ok <- natural(index), do: {:ok, {:omega, index}}
  end

  def decode_sort(_, _), do: error(:invalid_sort)

  @doc "A current whole-term external frame; inner node maps are intentionally unframed."
  def frame(node), do: %{"format" => "cure-core", "version" => @version, "term" => node}

  def unframe(%{"format" => "cure-core", "version" => @version, "term" => node} = frame)
      when map_size(frame) == 3 do
    with :ok <- budget(frame), do: {:ok, node}
  end

  def unframe(_), do: {:error, :incompatible_core_format}

  @doc "Bound allocation/traversal before recursively reconstructing external syntax."
  def budget(value) do
    case budget(value, 0, @max_nodes, @max_bytes) do
      {:ok, _nodes, _bytes} -> :ok
      {:error, _} = error -> error
    end
  end

  def natural(value) when is_integer(value) and value >= 0 do
    # Compare compact integers before asking Integer.to_string/1 to allocate.
    if value < @max_natural, do: :ok, else: {:error, :integer_too_large}
  end

  def natural(_), do: error(:invalid_natural)

  def bounded(values, maximum), do: bounded_list(values, maximum)
  defp bounded_list([], _remaining), do: :ok

  defp bounded_list([_ | tail], remaining) when remaining > 0,
    do: bounded_list(tail, remaining - 1)

  defp bounded_list(_, _), do: {:error, :collection_too_large_or_improper}

  defp decode_atoms([], _decode, acc), do: {:ok, Enum.reverse(acc)}

  defp decode_atoms([%{"term" => atom, "offset" => offset} = entry | rest], decode, acc)
       when map_size(entry) == 2 do
    with :ok <- natural(offset),
         {:ok, term} <- decode_atom(decode, atom) do
      decode_atoms(rest, decode, [{term, offset} | acc])
    end
  end

  defp decode_atoms(_, _, _), do: error(:invalid_atom_entry)

  # A Term raw decoder raises ArgumentError; Serialize's builder returns a
  # result tuple. Both callers retain their public error convention.
  defp decode_atom(decode, atom) do
    case decode.(atom) do
      {:ok, term} -> {:ok, term}
      {:error, _} = error -> error
      term -> {:ok, term}
    end
  rescue
    ArgumentError -> error(:invalid_atom_term)
    FunctionClauseError -> error(:invalid_atom_term)
  end

  defp validate_level(level) do
    with :ok <- natural(level.constant),
         :ok <- validate_offsets(level.atoms),
         :ok <- UniverseLevel.validate(level, nil) do
      :ok
    end
  rescue
    ArgumentError -> error(:invalid_level_nf)
    FunctionClauseError -> error(:invalid_level_nf)
  end

  defp validate_offsets([]), do: :ok

  defp validate_offsets([{term, offset} | rest]) do
    with :ok <- natural(offset),
         true <- hole_free?(term) do
      validate_offsets(rest)
    else
      false -> error(:hole_in_level_atom)
      error -> error
    end
  end

  defp validate_offsets(_), do: error(:invalid_atom_entry)

  defp hole_free?({:hole, _}), do: false

  defp hole_free?(%UniverseLevel{atoms: atoms}),
    do: Enum.all?(atoms, fn {term, _} -> hole_free?(term) end)

  defp hole_free?(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.all?(&hole_free?/1)

  defp hole_free?(terms) when is_list(terms), do: Enum.all?(terms, &hole_free?/1)
  defp hole_free?(_), do: true

  defp budget(_value, depth, nodes, bytes) when depth > @max_depth or nodes <= 0 or bytes < 0,
    do: {:error, :core_input_budget_exceeded}

  defp budget(value, _depth, nodes, bytes) when is_binary(value) do
    if byte_size(value) <= bytes,
      do: {:ok, nodes - 1, bytes - byte_size(value)},
      else: {:error, :core_input_budget_exceeded}
  end

  defp budget(value, depth, nodes, bytes)
       when is_map(value) and not is_struct(value) and map_size(value) <= @max_nodes,
       do: budget_entries(Map.to_list(value), depth + 1, nodes - 1, bytes - 2)

  defp budget(value, depth, nodes, bytes) when is_list(value),
    do: budget_list(value, depth + 1, nodes - 1, bytes - 2)

  defp budget(value, _depth, nodes, bytes) when is_integer(value) and abs(value) < @max_natural do
    size = byte_size(Integer.to_string(value))

    if size <= bytes,
      do: {:ok, nodes - 1, bytes - size},
      else: {:error, :core_input_budget_exceeded}
  end

  defp budget(value, _depth, nodes, bytes)
       when is_float(value) or is_boolean(value) or is_nil(value) do
    if bytes >= 32, do: {:ok, nodes - 1, bytes - 32}, else: {:error, :core_input_budget_exceeded}
  end

  defp budget(value, _depth, _nodes, _bytes) when is_integer(value),
    do: {:error, :integer_too_large}

  defp budget(_, _, _, _), do: {:error, :invalid_external_value}

  defp budget_list([], _depth, nodes, bytes) when bytes >= 0, do: {:ok, nodes, bytes}

  defp budget_list([head | tail], depth, nodes, bytes) do
    with {:ok, nodes, bytes} <- budget(head, depth, nodes, bytes),
         do: budget_list(tail, depth, nodes, bytes)
  end

  defp budget_list(_, _, _, _), do: {:error, :improper_core_input}
  defp budget_entries([], _depth, nodes, bytes) when bytes >= 0, do: {:ok, nodes, bytes}

  defp budget_entries([{key, value} | rest], depth, nodes, bytes) when is_binary(key) do
    with {:ok, nodes, bytes} <- budget(key, depth, nodes, bytes),
         {:ok, nodes, bytes} <- budget(value, depth, nodes, bytes),
         do: budget_entries(rest, depth, nodes, bytes)
  end

  defp budget_entries(_, _, _, _), do: {:error, :invalid_external_map}

  defp error(reason), do: {:error, {:noncanonical_level_encoding, reason}}
end
