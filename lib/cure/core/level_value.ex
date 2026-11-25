defmodule Cure.Core.LevelValue do
  @moduledoc """
  Private NbE representation of a maximum-plus level.

  Unlike `UniverseLevel`, atoms here are semantic neutral values with absolute
  de Bruijn levels and captured argument environments. They are never Core,
  serialized artifacts, or evidence of atom typing. `Eval` creates them and
  `Quote` converts them back to canonical Core at the requested binder depth.
  """

  alias Cure.Core.{UniverseLevel, Value}

  @enforce_keys [:constant, :atoms]
  defstruct [:constant, :atoms]

  @type t :: %__MODULE__{
          constant: non_neg_integer(),
          atoms: [{{:vneutral, Value.neutral()}, non_neg_integer()}]
        }

  @spec closed(non_neg_integer()) :: t()
  def closed(n) when is_integer(n) and n >= 0, do: %__MODULE__{constant: n, atoms: []}

  @spec from_core(UniverseLevel.t(), (Cure.Core.Term.t() -> Value.t())) :: t()
  def from_core(%UniverseLevel{constant: constant, atoms: atoms}, evaluate) do
    Enum.reduce(atoms, closed(constant), fn {term, offset}, acc ->
      add(acc, evaluate.(term), offset)
    end)
  end

  @spec to_core(t(), (Value.t() -> Cure.Core.Term.t())) :: UniverseLevel.t()
  def to_core(%__MODULE__{constant: constant, atoms: atoms}, quote_atom) do
    UniverseLevel.normalize(%UniverseLevel{
      constant: constant,
      atoms: Enum.map(atoms, fn {value, offset} -> {quote_atom.(value), offset} end)
    })
  end

  @spec map(t(), (Value.t() -> Value.t())) :: t()
  def map(%__MODULE__{constant: constant, atoms: atoms}, transform) do
    Enum.reduce(atoms, closed(constant), fn {value, offset}, acc ->
      add(acc, transform.(value), offset)
    end)
  end

  @spec succ(t()) :: t()
  def succ(%__MODULE__{constant: constant, atoms: atoms}),
    do: canonical(constant + 1, Enum.map(atoms, fn {value, offset} -> {value, offset + 1} end))

  @spec max(t(), t()) :: t()
  def max(%__MODULE__{} = left, %__MODULE__{} = right),
    do: canonical(Kernel.max(left.constant, right.constant), left.atoms ++ right.atoms)

  @spec valid?(term()) :: boolean()
  def valid?(%__MODULE__{constant: constant, atoms: atoms} = level)
      when is_integer(constant) and constant >= 0 and is_list(atoms) do
    Enum.all?(atoms, fn
      {{:vneutral, neutral}, offset} when is_integer(offset) and offset >= 0 -> Value.neutral?(neutral)
      _ -> false
    end) and canonical(constant, atoms) == level
  end

  def valid?(_), do: false

  defp add(acc, {:vlevel, %__MODULE__{} = inner}, offset)
       when is_integer(offset) and offset >= 0 do
    canonical(
      Kernel.max(acc.constant, inner.constant + offset),
      acc.atoms ++ Enum.map(inner.atoms, fn {value, k} -> {value, k + offset} end)
    )
  end

  defp add(acc, {:vneutral, _} = value, offset) when is_integer(offset) and offset >= 0,
    do: canonical(acc.constant, [{value, offset} | acc.atoms])

  defp add(_acc, _value, _offset),
    do: raise(ArgumentError, "a universe level atom evaluated to a non-level value")

  # Ordering here is private and never contributes artifact identity. Portable
  # Core ordering is applied after depth-correct quotation by UniverseLevel.
  defp canonical(constant, atoms) do
    atoms =
      atoms
      |> Enum.reduce(%{}, fn {value, offset}, acc ->
        Map.update(acc, value, offset, &Kernel.max(&1, offset))
      end)
      |> Enum.sort_by(fn {value, _offset} -> :erlang.term_to_binary(value) end)

    constant =
      if Enum.any?(atoms, fn {_value, offset} -> constant <= offset end), do: 0, else: constant

    %__MODULE__{constant: constant, atoms: atoms}
  end
end
