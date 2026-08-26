defmodule Cure.Compiler.MacroPacket do
  @moduledoc "Pure packet-layout elaboration for the concrete macro library."

  @scalar_widths %{u8: 1, i8: 1, u16: 2, i16: 2, u32: 4, i32: 4, byte: 1}
  @endian_values [:be, :le]

  @spec build(String.t() | atom(), [map()], keyword()) :: {:ok, map()} | {:error, term()}
  def build(name, fields, opts \\ []) when is_list(fields) do
    endian = Keyword.get(opts, :endian)

    with :ok <- validate_name(name),
         :ok <- validate_endian(endian),
         :ok <- validate_fields(fields, endian),
         {:ok, layout} <- layout(fields),
         {:ok, [declaration]} <- declaration(name, endian, fields) do
      {:ok,
       %{
         kind: :quoted_packet,
         name: name,
         endian: endian,
         fields: fields,
         layout: layout,
         declarations: [declaration],
         properties: [:round_trip, :total_parse, :fault_rejection]
       }}
    end
  end

  defp validate_name(name) when is_atom(name) or is_binary(name), do: :ok
  defp validate_name(name), do: {:error, {:invalid_packet_name, name}}

  defp validate_endian(nil), do: :ok
  defp validate_endian(endian) when endian in @endian_values, do: :ok
  defp validate_endian(endian), do: {:error, {:invalid_packet_endian, endian}}

  defp validate_fields(fields, packet_endian) do
    names = Enum.map(fields, fn field -> if is_map(field), do: Map.get(field, :name), else: nil end)

    cond do
      not Enum.all?(fields, &is_map/1) -> {:error, :invalid_packet_field}
      Enum.any?(names, &is_nil/1) -> {:error, :invalid_packet_field_name}
      length(names) != MapSet.size(MapSet.new(names)) -> {:error, :duplicate_packet_field}
      true -> validate_field_sequence(fields, packet_endian, MapSet.new())
    end
  end

  defp validate_field_sequence([], _packet_endian, _seen), do: :ok

  defp validate_field_sequence([field | rest], packet_endian, seen) do
    with :ok <- validate_field(field, packet_endian, seen),
         :ok <- validate_field_sequence(rest, packet_endian, MapSet.put(seen, field.name)) do
      :ok
    end
  end

  defp validate_field(%{name: _name, kind: :const, value: value}, _endian, _seen)
       when is_integer(value) or is_binary(value),
       do: :ok

  defp validate_field(%{name: _name, kind: :scalar, type: type} = field, packet_endian, _seen)
       when is_atom(type) do
    cond do
      not Map.has_key?(@scalar_widths, type) ->
        {:error, {:unknown_packet_scalar, type}}

      @scalar_widths[type] > 1 and Map.get(field, :endian, packet_endian) not in @endian_values ->
        {:error, {:missing_packet_endian, field.name}}

      true ->
        :ok
    end
  end

  defp validate_field(%{name: _name, kind: :bytes, length: length}, _endian, _seen)
       when is_integer(length) and length > 0,
       do: :ok

  defp validate_field(%{name: name, kind: :bytes, length: length}, _endian, seen)
       when is_atom(length) do
    if MapSet.member?(seen, length), do: :ok, else: {:error, {:forward_packet_length, name, length}}
  end

  defp validate_field(%{name: name, kind: :crc, over: fields}, _endian, seen) when is_list(fields) do
    missing = Enum.reject(fields, &MapSet.member?(seen, &1))
    if missing == [], do: :ok, else: {:error, {:invalid_packet_crc_fields, name, missing}}
  end

  defp validate_field(field, _endian, _seen), do: {:error, {:invalid_packet_field, field}}

  defp layout(fields) do
    {layout, _offset} =
      Enum.map_reduce(fields, 0, fn field, offset ->
        width = fixed_width(field)
        {{field.name, offset, width}, if(is_integer(width), do: offset + width, else: offset)}
      end)

    {:ok, layout}
  end

  defp fixed_width(%{kind: :const, value: value}) when is_integer(value), do: 1
  defp fixed_width(%{kind: :const, value: value}) when is_binary(value), do: byte_size(value)
  defp fixed_width(%{kind: :scalar, type: type}), do: Map.get(@scalar_widths, type)
  defp fixed_width(%{kind: :bytes, length: length}) when is_integer(length), do: length
  defp fixed_width(_field), do: nil

  defp declaration(name, endian, fields) do
    {:ok, [{:packet_def, [name: name, endian: endian], fields}]}
  end
end
