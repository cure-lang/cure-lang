defmodule Antigen.HealthGateTest do
  use ExUnit.Case, async: true
  alias Antigen.Runner
  alias Antigen.Generators.Term
  alias Antigen.Backend.StreamData, as: B

  test "health_metrics computes binder-usage and reduction-activity over :typed_term" do
    challenges = B.interp(Term.default_gen()) |> Enum.take(200)
    m = Runner.health_metrics(challenges)
    assert is_float(m.binder_usage)
    assert is_float(m.reduction_activity)
    assert is_integer(m.fuel_exhausted_count)
    # the v1 engine must clear its own floors
    assert m.binder_usage >= 0.60, "binder-usage #{m.binder_usage} below floor"
    assert m.reduction_activity >= 0.25, "reduction-activity #{m.reduction_activity} below floor"
  end

  test "the three term assay ids resolve to Assays.Term" do
    for id <- Term.assay_ids() do
      assert Runner.assay_module_for(id) == Antigen.Assays.Term
    end
  end
end
