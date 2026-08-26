defmodule Cure.Core.ConvFuelTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Conv, Env}
  alias Antigen.Generators.Forcing

  test "conv_within? returns {:ok, _} for a terminating conversion" do
    # two obviously-equal closed terms, no divergence
    assert {:ok, true} = Conv.conv_within?({:type, 0}, {:type, 0}, [], 0, nil, 1000)
  end

  test "conv_within? bounds δ on a certified diverging global (the hazard fuel guards against)" do
    # The fixed certifier will NOT certify a diverging cycle, so to isolate the
    # fuel mechanism we certify it manually — simulating a hypothetical future
    # totality hole. δ-unfolding such a global must halt at the budget, not loop.
    c = Forcing.forcing_pair()

    env =
      c.payload.defs
      |> Enum.reduce(Env.empty(), fn d, e -> Env.add_def(e, d.name, d.type, d.body) end)
      |> Env.certify(:f)
      |> Env.certify(:g)

    assert :fuel_exhausted = Conv.conv_within?(c.payload.t, c.payload.tprime, [], 0, env, 200)
  end

  test "the un-fueled conv?/5 path is unaffected (no fuel key leaks)" do
    assert Conv.conv?({:type, 0}, {:type, 0}, [], 0, nil) == true
    assert Process.get({Conv, :fuel}) == nil
  end
end
