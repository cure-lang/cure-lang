defmodule Cure.Compiler.MacroBoard do
  @moduledoc "Pure board-definition validation for the concrete macro library."

  @capabilities [:input, :output, :adc, :dac, :strapping, :usb, :touch]

  @spec build(String.t() | atom(), map()) :: {:ok, map()} | {:error, term()}
  def build(name, definition) when is_map(definition) do
    with :ok <- validate_name(name),
         {:ok, chip} <- validate_chip(Map.fetch(definition, :chip)),
         {:ok, pins} <- validate_pins(Map.get(definition, :pins)),
         :ok <- validate_capabilities(Map.get(definition, :capabilities, %{}), pins),
         :ok <- validate_buses(Map.get(definition, :buses, %{}), pins, definition),
         :ok <- validate_flash(Map.get(definition, :flash, %{})) do
      {:ok,
       %{
         kind: :quoted_board,
         name: name,
         chip: chip,
         pins: pins,
         capabilities: Map.get(definition, :capabilities, %{}),
         buses: Map.get(definition, :buses, %{}),
         flash: Map.get(definition, :flash, %{}),
         declarations: [{:board_def, [name: name], definition}]
       }}
    end
  end

  def build(_name, _definition), do: {:error, :invalid_board_definition}

  defp validate_name(name) when is_atom(name) or is_binary(name), do: :ok
  defp validate_name(name), do: {:error, {:invalid_board_name, name}}

  defp validate_chip({:ok, chip}) when is_atom(chip) or is_binary(chip), do: {:ok, chip}
  defp validate_chip({:ok, chip}), do: {:error, {:invalid_board_chip, chip}}
  defp validate_chip(:error), do: {:error, :missing_board_chip}

  defp validate_pins({first, last}) when is_integer(first) and is_integer(last) and first >= 0 and last >= first,
    do: {:ok, MapSet.new(first..last)}

  defp validate_pins(pins) when is_list(pins) do
    if Enum.all?(pins, &is_integer/1) and Enum.all?(pins, &(&1 >= 0)),
      do: {:ok, MapSet.new(pins)},
      else: {:error, :invalid_board_pins}
  end

  defp validate_pins(_), do: {:error, :invalid_board_pins}

  defp validate_capabilities(capabilities, pins) when is_map(capabilities) do
    case Enum.reduce_while(capabilities, :ok, fn {pin, caps}, :ok ->
           cond do
             not MapSet.member?(pins, pin) ->
               {:halt, {:unknown_board_pin, pin}}

             not is_list(caps) or Enum.any?(caps, &(&1 not in @capabilities)) ->
               {:halt, {:invalid_board_capability, pin}}

             true ->
               {:cont, :ok}
           end
         end) do
      :ok -> :ok
      error -> {:error, error}
    end
  end

  defp validate_capabilities(_capabilities, _pins), do: {:error, :invalid_board_capabilities}

  defp validate_buses(buses, pins, definition) when is_map(buses) do
    capabilities = Map.get(definition, :capabilities, %{})

    case Enum.reduce_while(buses, :ok, fn {name, wiring}, :ok ->
           assigned = if is_map(wiring), do: wiring |> Map.values() |> Enum.uniq(), else: :invalid

           cond do
             assigned == :invalid ->
               {:halt, {:invalid_board_bus, name}}

             not is_atom(name) ->
               {:halt, {:invalid_board_bus, name}}

             Enum.any?(assigned, &(not MapSet.member?(pins, &1))) ->
               {:halt, {:unknown_bus_pin, name}}

             Enum.any?(assigned, &(not Map.has_key?(capabilities, &1))) ->
               {:halt, {:missing_bus_capability, name}}

             true ->
               {:cont, :ok}
           end
         end) do
      :ok -> :ok
      error -> {:error, error}
    end
  end

  defp validate_buses(_buses, _pins, _definition), do: {:error, :invalid_board_buses}

  defp validate_flash(%{size: size, app_offset: app, libs_offset: libs})
       when is_integer(size) and size > 0 and is_integer(app) and is_integer(libs) and app >= 0 and libs >= 0 do
    if app < size and libs < size, do: :ok, else: {:error, :flash_offset_out_of_bounds}
  end

  defp validate_flash(_), do: {:error, :invalid_board_flash}
end
