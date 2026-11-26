defmodule Cure.Elab.UniverseTraversal do
  @moduledoc """
  Meta-aware reconstruction of elaborator universe payloads.

  Pending elaborator terms are not checked Core. If a transformed atom is not
  yet Core-shaped, preserve its syntax without invoking the Core serializer or
  evaluator. This may be an unsolved term meta or malformed input, never
  evidence that elaboration is complete. Final zonking reconstructs canonical
  levels once every atom has Core shape; final shape validation and independent
  kernel admission remain mandatory.
  """

  alias Cure.Core.{Term, UniverseLevel}

  def map_sort({:finite, level}, transform), do: {:finite, map_level(level, transform)}
  def map_sort({:omega, _} = sort, _transform), do: sort

  def map_level(%UniverseLevel{} = level, transform) do
    mapped = %UniverseLevel{
      constant: level.constant,
      atoms: Enum.map(level.atoms, fn {term, offset} -> {transform.(term), offset} end)
    }

    if Enum.all?(mapped.atoms, fn {term, _offset} -> Term.term?(term) end),
      do: UniverseLevel.normalize(mapped),
      else: mapped
  end
end
