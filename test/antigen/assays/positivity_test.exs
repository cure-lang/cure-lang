defmodule Antigen.Assays.PositivityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Positivity, as: A
  alias Antigen.Generators.Positivity, as: G

  test "passes a labeled-negative family (checker correctly rejects it)" do
    assert :ok == A.run(G.negative_family())
  end

  test "passes a labeled-positive family (checker accepts it)" do
    assert :ok == A.run(G.positive_family())
  end

  test "a mislabeled family (labeled positive but actually negative) is a violation" do
    mislabeled = %{G.negative_family() | label: :positive}
    assert {:violation, _} = A.run(mislabeled)
  end

  # -- W4: classic positivity escape hatches (pre-port banking spec §4 W4) ----
  # All three are :negative by construction; :ok means the kernel rejected them.
  # AUDIT (D4): if a test fails with {:wrongly_accepted, :Bad}, that is a LIVE
  # positivity hole — fixed red-green in the kernel by the next task, then these
  # become its permanent regression guards.

  test "W4: double negation ((Bad -> Dec) -> Dec) is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(Antigen.Generators.Positivity.double_negation_family())
  end

  test "W4: negative occurrence hidden under a sigma is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(Antigen.Generators.Positivity.sigma_negative_family())
  end

  test "W4: through-constructor negative occurrence (Bad -> via Box) is rejected" do
    assert :ok == Antigen.Assays.Positivity.run(Antigen.Generators.Positivity.through_constructor_negative())
  end
end
