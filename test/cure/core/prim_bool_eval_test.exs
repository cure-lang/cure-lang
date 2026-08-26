defmodule Cure.Core.PrimBoolEvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Normalise}

  # K2 (spec 2026-07-09): comparisons are builtin-op GLOBAL spines folded by
  # the certified-δ engine (Eval alone leaves every global neutral).
  defp ctx, do: Context.empty(Builtins.seed(Env.empty()))
  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "certified delta folds a comparison to the True constructor" do
    t = Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert t == {:ctor, :"Std.Bool#True", []}
    refute t == {:bool_lit, true}
  end

  test "certified delta folds a false comparison to the False constructor" do
    assert {:ctor, :"Std.Bool#False", []} =
             Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 5}, {:int_lit, 3}), delta: :certified)
  end

  test "the connectives are not builtin ops: an and/not spine stays neutral" do
    # `and`/`or`/`not` are Std.Bool case-defs, not registered ops; their spines
    # stay stuck over the bare seeded env.
    t1 = app2(:and, {:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#True", []})
    assert t1 == Normalise.nf(ctx(), t1, delta: :certified)
    t2 = {:app, {:global, :not}, {:ctor, :"Std.Bool#False", []}}
    assert t2 == Normalise.nf(ctx(), t2, delta: :certified)
  end

  test "Bool-operand equality never folds via the numeric twin: only literal int_eq folds" do
    # `==` on Bool is the Std.Bool def `eq`; an int_eq spine over ctor args
    # stays NEUTRAL (the fold requires int/float literal values). Numeric
    # int_eq still folds.
    t = app2(:int_eq, {:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#False", []})
    assert t == Normalise.nf(ctx(), t, delta: :certified)

    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx(), app2(:int_eq, {:int_lit, 3}, {:int_lit, 3}), delta: :certified)
  end
end
