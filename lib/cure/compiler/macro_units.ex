defmodule Cure.Compiler.MacroUnits do
  @moduledoc "Pure unit registry and literal elaboration for Tier-1 macros."

  @spec register(map(), String.t(), number(), atom()) :: {:ok, map()} | {:error, term()}
  def register(registry, suffix, scale, dimension)
      when is_map(registry) and is_binary(suffix) and is_number(scale) and scale > 0 and is_atom(dimension) do
    if Map.has_key?(registry, suffix),
      do: {:error, {:duplicate_unit, suffix}},
      else: {:ok, Map.put(registry, suffix, %{scale: scale, dimension: dimension})}
  end

  def register(_registry, suffix, _scale, _dimension), do: {:error, {:invalid_unit, suffix}}

  @spec literal(map(), number(), String.t()) :: {:ok, map()} | {:error, term()}
  def literal(registry, value, suffix) when is_map(registry) and is_number(value) and is_binary(suffix) do
    case Map.fetch(registry, suffix) do
      {:ok, %{scale: scale, dimension: dimension} = unit}
      when is_number(scale) and scale > 0 and is_atom(dimension) ->
        {:ok, %{kind: :unit_literal, value: value, suffix: suffix, unit: unit, scaled: value * scale}}

      {:ok, _unit} ->
        {:error, {:invalid_unit, suffix}}

      :error ->
        {:error, {:unknown_unit, suffix}}
    end
  end

  def literal(_registry, value, suffix), do: {:error, {:invalid_unit_literal, value, suffix}}
end
