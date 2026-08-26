defmodule Cure.Core.PositivitySelfParamSoundnessTest do
  @moduledoc """
  Regression for the strict-positivity hole where a field headed by the family
  being defined returned positive UNCONDITIONALLY, ignoring the family's own
  parameters/indices. A negative occurrence buried in the family's own argument
  (`Bad ((Bad Unit) -> Empty)`) was admitted, even though the identical negative
  occurrence under ANOTHER family's head was correctly rejected.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  @unit {:data, :Unit, [], []}
  @empty {:data, :Empty, [], []}
  # neg = (Bad Unit) -> Empty : Bad occurs to the LEFT of an arrow (negative).
  @neg {:pi, Cure.Core.Grade.unrestricted(), {:data, :Bad, [@unit], []}, @empty}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Unit, [], [], 0), [Inductive.ctor(:unit, [], [])])
    |> Inductive.declare(Inductive.family(:Empty, [], [], 0), [])
    |> Inductive.declare(Inductive.family(:Other, [], [], 0), [])
  end

  test "negative occurrence under ANOTHER family's head is rejected (control)" do
    env =
      Inductive.declare(base(), Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:mk, [{:f, {:data, :Other, [@neg], []}}], [])
      ])

    assert {:error, {:non_strictly_positive, :mk}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  test "the SAME negative occurrence under the family's OWN head is also rejected" do
    env =
      Inductive.declare(base(), Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:mk, [{:f, {:data, :Bad, [@neg], []}}], [])
      ])

    # THE FIX: the self-family field must inspect its own params/indices too.
    assert {:error, {:non_strictly_positive, :mk}} ==
             Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end

  test "a genuinely strictly-positive recursive field is still accepted" do
    # Bad (Unit) -- self-head, argument is inert, no negative occurrence.
    env =
      Inductive.declare(base(), Inductive.family(:Bad, [], [], 0), [
        Inductive.ctor(:mk, [{:f, {:data, :Bad, [@unit], []}}], [])
      ])

    assert :ok == Inductive.positive?(env, Inductive.get_family(env, :Bad))
  end
end
