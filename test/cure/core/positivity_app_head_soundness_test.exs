defmodule Cure.Core.PositivityAppHeadSoundnessTest do
  @moduledoc """
  Strict positivity must not fail OPEN on a field type whose head is not a data
  family or Π. A field `Neg Bad` (a type-level function applied to the family)
  or a type-level λ mentioning the family can hide a negative occurrence
  (`Neg := λt. t -> Empty` ⇒ `Neg Bad = Bad -> Empty`). The `:app`/`:lam`/… cases
  fell through to a `true` catch-all, admitting the family in an unanalyzable
  position — inconsistent with the `:data`-other clause, which conservatively
  REJECTS the family occurring in another family's arguments.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  @empty {:data, :Empty, [], []}
  @bad {:data, :Bad, [], []}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Empty, [], [], 0), [])
  end

  defp positive_of(field_type) do
    env =
      Inductive.declare(base(), Inductive.family(:Bad, [], [], 0), [Inductive.ctor(:mk, [{:f, field_type}], [])])

    Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  test "family under an application head (Neg Bad) is rejected" do
    # {:app, Neg, Bad} — Neg an opaque type-level fn; Bad occurs in an
    # unanalyzable position, so positivity cannot be guaranteed.
    field = {:app, {:global, :Neg}, @bad}
    assert {:error, {:non_strictly_positive, :mk}} == positive_of(field)
  end

  test "family under a type-level lambda is rejected" do
    # λ(t : Type). (Bad -> Empty) — a negative occurrence hidden under a binder.
    field = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:pi, Cure.Core.Grade.unrestricted(), @bad, @empty}}
    assert {:error, {:non_strictly_positive, :mk}} == positive_of(field)
  end

  test "an application head NOT mentioning the family is still accepted" do
    # {:app, Neg, Empty} — Bad does not occur, so nothing to reject.
    field = {:app, {:global, :Neg}, @empty}
    assert :ok == positive_of(field)
  end
end
