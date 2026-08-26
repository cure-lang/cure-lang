defmodule Cure.Core.FloatPrimTest do
  @moduledoc """
  Primitive `Float` in the kernel — now via registry-keyed builtin-op GLOBALS
  (K2, spec 2026-07-09; the `{:prim}` node is retired). Float-indexed types
  (`Rate`, `PositiveAmount`, …) still evaluate and compare inside `Cure.Core`:
  the certified-δ engine folds saturated literal float spines; §G.1 rule 1
  (zero-divisor stays neutral) survives verbatim.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, Normalise, Quote}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "certified delta folds float arithmetic" do
    assert {:float_lit, 3.5} =
             Normalise.nf(ctx(), app2(:float_add, {:float_lit, 1.5}, {:float_lit, 2.0}), delta: :certified)

    assert {:float_lit, 6.0} =
             Normalise.nf(ctx(), app2(:float_mul, {:float_lit, 2.0}, {:float_lit, 3.0}), delta: :certified)

    assert {:float_lit, 3.5} =
             Normalise.nf(ctx(), app2(:float_div, {:float_lit, 7.0}, {:float_lit, 2.0}), delta: :certified)
  end

  test "float division by zero stays stuck rather than reducing (K2 §G.1 rule 1)" do
    # A partial op must NOT fire when undefined: the spine stays a neutral term
    # (compared syntactically by conversion), so normalization stays total and
    # the kernel never invents a value for x / 0.0.
    t = app2(:float_div, {:float_lit, 7.0}, {:float_lit, 0.0})
    assert t == Normalise.nf(ctx(), t, delta: :certified)
  end

  test "certified delta folds float comparisons to Bool constructor values" do
    true_ctor = Cure.Elab.Name.qualify("Std.Bool", :True)

    assert {:ctor, ^true_ctor, []} =
             Normalise.nf(ctx(), app2(:float_lt, {:float_lit, 1.0}, {:float_lit, 2.0}), delta: :certified)
  end

  test "reify round-trips Float type and literals" do
    assert Quote.reify({:vfloat_type}) == {:float_type}
    assert Quote.reify({:vfloat, 3.5}) == {:float_lit, 3.5}
  end

  test "definitional equality on floats" do
    assert Conv.conv?(app2(:float_add, {:float_lit, 1.5}, {:float_lit, 2.0}), {:float_lit, 3.5}, [], 0, env())
    refute Conv.conv?({:float_lit, 3.5}, {:float_lit, 3.6}, [], 0, env())
  end

  test "kernel types Float literals and arithmetic spines" do
    ctx = ctx()
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx, {:float_type})
    assert {:ok, {:vfloat_type}} = Kernel.infer(ctx, {:float_lit, 1.5})
    assert {:ok, {:vfloat_type}} = Kernel.infer(ctx, app2(:float_add, {:float_lit, 1.0}, {:float_lit, 2.0}))

    bool_family = Cure.Elab.Name.qualify("Std.Bool", :Bool)

    assert {:ok, {:vdata, ^bool_family, []}} =
             Kernel.infer(ctx, app2(:float_lt, {:float_lit, 1.0}, {:float_lit, 2.0}))

    assert {:error, _} = Kernel.infer(ctx, app2(:float_add, {:float_lit, 1.0}, {:int_lit, 2}))
  end
end
