defmodule Antigen.BuiltinBoolDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Eval, Normalise}

  # Task 6 hardcodes :True/:False in eval.ex's fold (it has no sig on its path);
  # Task 2/3 seed the schema. This antibody fails if the two ever drift.
  # K2 update: comparisons are builtin-op GLOBAL spines folded by the
  # certified-δ engine (Eval alone leaves globals neutral), so the drift pin
  # normalizes spines over a seeded env — the fold table is the same.
  test "fold's hardcoded True/False agree with the seeded :bool schema names" do
    names = Builtins.schema(:bool) |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    assert names == [:False, :True]

    ctx = Context.empty(Builtins.seed(Env.empty()))
    lt = fn a, b -> {:app, {:app, {:global, :int_lt}, {:int_lit, a}}, {:int_lit, b}} end

    true_ctor = Cure.Elab.Name.qualify("Std.Bool", :True)
    false_ctor = Cure.Elab.Name.qualify("Std.Bool", :False)

    assert Normalise.nf(ctx, lt.(1, 2), delta: :certified) ==
             Normalise.nf(ctx, {:ctor, true_ctor, []}, delta: :certified)

    assert Normalise.nf(ctx, lt.(2, 1), delta: :certified) ==
             Normalise.nf(ctx, {:ctor, false_ctor, []}, delta: :certified)

    # the shared table itself (Eval.fold) still lands on the ctor VALUES
    assert Eval.fold(:lt, [{:vint, 1}, {:vint, 2}]) == {:ok, Eval.eval({:ctor, true_ctor, []}, [])}
    assert Eval.fold(:lt, [{:vint, 2}, {:vint, 1}]) == {:ok, Eval.eval({:ctor, false_ctor, []}, [])}
  end
end
