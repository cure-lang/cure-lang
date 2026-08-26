defmodule Cure.Elab.RewriteGradePreservationTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Rewrite

  test "abstracting a motive preserves Pi and lambda grades" do
    target = {:var, 0}

    term =
      {:pi, :erased, {:data, :Proof, [], [target]},
       {:lam, :linear, {:data, :Payload, [], []}, {:app, {:var, 1}, target}}}

    assert {:pi, :erased, _domain, {:lam, :linear, _lambda_domain, _body}} =
             Rewrite.abstract_term(term, target, 0)
  end
end
