defmodule Cure.Core.QuoteTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Eval, Quote}

  test "identity lambda reifies to lam over var 0" do
    v = Eval.eval({:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, [])
    assert {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}} == Quote.reify(v, 0)
  end

  test "round-trips a neutral applied under binders (level->index correct)" do
    t =
      {:lam, Cure.Core.Grade.unrestricted(), {:type, 0},
       {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:var, 1}, {:var, 0}}}}

    assert t == Quote.reify(Eval.eval(t, []), 0)
  end

  test "reify produces a beta-normal form (no residual redex)" do
    t = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}}
    assert {:type, 0} == Quote.reify(Eval.eval(t, []), 0)
  end

  test "round-trips Pi and Sigma binders" do
    pi = {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}
    assert pi == Quote.reify(Eval.eval(pi, []), 0)
    # Inductive Sigma (D2): the family application round-trips (0 indices, so the
    # sig-less reify splits all args as params correctly).
    sg = {:data, :Sigma, [{:type, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}], []}
    assert sg == Quote.reify(Eval.eval(sg, []), 0)
  end
end
