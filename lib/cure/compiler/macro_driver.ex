defmodule Cure.Compiler.MacroDriver do
  @moduledoc "Pure register-map validation for the concrete driver macro library."

  @widths [8, 16, 32]
  @access [:read, :write, :read_write]

  @spec build(String.t() | atom(), [map()], keyword()) :: {:ok, map()} | {:error, term()}
  def build(name, registers, opts \\ []) when is_list(registers) and is_list(opts) do
    with :ok <- validate_registers(registers),
         :ok <- validate_base(Keyword.get(opts, :base, 0)) do
      {:ok,
       %{
         kind: :quoted_driver,
         name: name,
         base: Keyword.get(opts, :base, 0),
         bus: Keyword.get(opts, :bus),
         registers: registers,
         declarations: [{:driver_def, [name: name], registers}]
       }}
    end
  end

  defp validate_base(base) when is_integer(base) and base >= 0, do: :ok
  defp validate_base(base), do: {:error, {:invalid_driver_base, base}}

  defp validate_registers(registers) do
    if Enum.all?(registers, &valid_register?/1) do
      names = Enum.map(registers, &Map.fetch!(&1, :name))

      cond do
        length(names) != MapSet.size(MapSet.new(names)) -> {:error, :duplicate_driver_register}
        overlapping?(registers) -> {:error, :overlapping_driver_register}
        true -> :ok
      end
    else
      {:error, :invalid_driver_register}
    end
  end

  defp valid_register?(%{name: name, offset: offset, width: width, access: access})
       when (is_atom(name) or is_binary(name)) and is_integer(offset) and offset >= 0 and width in @widths and
              access in @access,
       do: true

  defp valid_register?(_), do: false

  defp overlapping?(registers) do
    ranges =
      registers
      |> Enum.with_index()
      |> Enum.map(fn {%{offset: offset, width: width}, index} -> {index, offset, offset + div(width, 8)} end)

    Enum.any?(ranges, fn {index, start, finish} ->
      Enum.any?(ranges, fn {other_index, other_start, other_finish} ->
        index < other_index and start < other_finish and other_start < finish
      end)
    end)
  end
end
