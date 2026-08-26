defmodule Cure.Core.BoolPrimTest do
  @moduledoc """
  Numeric comparisons in the kernel — now registry-keyed builtin-op GLOBALS
  (K2, spec 2026-07-09). `Bool` is a real inductive family: comparison spines
  infer to the `Bool` inductive type value and the certified-δ engine folds
  literal spines to the `True`/`False` constructor values. The boolean
  CONNECTIVES (`and`/`or`/`not`) and Bool-operand equality are Std.Bool
  `case`-defs — an `and`-headed spine over a bare seeded env is an ordinary
  unknown global (`:unknown_global` in infer, neutral in normalization).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "certified delta folds integer comparisons to Bool constructor values" do
    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)

    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx(), app2(:int_eq, {:int_lit, 4}, {:int_lit, 4}), delta: :certified)

    assert {:ctor, :"Std.Bool#False", []} =
             Normalise.nf(ctx(), app2(:int_ge, {:int_lit, 2}, {:int_lit, 9}), delta: :certified)
  end

  test "the boolean connectives are NOT builtin ops: an and/or/not spine stays neutral" do
    for t <- [
          app2(:and, {:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#False", []}),
          app2(:or, {:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#False", []}),
          {:app, {:global, :not}, {:ctor, :"Std.Bool#False", []}}
        ] do
      assert t == Normalise.nf(ctx(), t, delta: :certified)
    end
  end

  test "definitional equality across comparisons" do
    assert Conv.conv?(app2(:int_lt, {:int_lit, 3}, {:int_lit, 5}), {:ctor, :"Std.Bool#True", []}, [], 0, env())
    refute Conv.conv?({:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#False", []}, [], 0, env())
  end

  test "kernel types numeric comparison spines at Bool and rejects connective globals as unknown" do
    bool = {:vdata, :"Std.Bool#Bool", []}
    assert {:ok, ^bool} = Kernel.infer(ctx(), app2(:int_lt, {:int_lit, 1}, {:int_lit, 2}))

    # The connectives are Std.Bool defs, absent from the bare seeded env — an
    # `and`-headed spine is an ordinary unknown global (was {:unknown_prim, :and}).
    assert {:error, {:unknown_global, :and, _details}} =
             Kernel.infer(ctx(), app2(:and, {:ctor, :"Std.Bool#True", []}, {:ctor, :"Std.Bool#False", []}))

    assert {:error, _} = Kernel.infer(ctx(), app2(:int_lt, {:ctor, :"Std.Bool#True", []}, {:int_lit, 2}))
  end
end
