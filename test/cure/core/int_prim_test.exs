defmodule Cure.Core.IntPrimTest do
  @moduledoc """
  Primitive `Int` in the kernel — now via registry-keyed builtin-op GLOBALS
  (K2, spec 2026-07-09; the `{:prim}` node is retired). Arithmetic type indices
  (`Vector(T, m + n)`) still reduce and compare *inside the kernel*: the
  certified-δ engine folds saturated literal spines through the audited
  `Eval.fold` table; §G.1's rules survive verbatim (partial ops stay neutral,
  open spines stay stuck and compare by napp congruence).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel, Normalise, Quote}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "certified delta folds integer arithmetic on literal spines" do
    assert {:int_lit, 8} = Normalise.nf(ctx(), app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:int_lit, 7} = Normalise.nf(ctx(), app2(:int_sub, {:int_lit, 10}, {:int_lit, 3}), delta: :certified)
    assert {:int_lit, 24} = Normalise.nf(ctx(), app2(:int_mul, {:int_lit, 4}, {:int_lit, 6}), delta: :certified)
    assert {:int_lit, 5} = Normalise.nf(ctx(), app2(:int_div, {:int_lit, 20}, {:int_lit, 4}), delta: :certified)
  end

  test "arithmetic over a free variable stays stuck as a neutral spine" do
    ctx1 = Context.extend(ctx(), {:vint_type})
    t = app2(:int_add, {:var, 0}, {:int_lit, 1})
    assert t == Normalise.nf(ctx1, t, delta: :certified)
  end

  test "division by zero stays stuck rather than crashing" do
    t = app2(:int_div, {:int_lit, 1}, {:int_lit, 0})
    assert t == Normalise.nf(ctx(), t, delta: :certified)
  end

  test "remainder by zero stays stuck rather than crashing (K2 §G.1 rule 1)" do
    # rem is partial like div: on a zero divisor the fold must not fire — the
    # spine stays a neutral term so normalization is total and conversion
    # compares it syntactically. Completes the partial-op coverage with div.
    t = app2(:int_rem, {:int_lit, 7}, {:int_lit, 0})
    assert t == Normalise.nf(ctx(), t, delta: :certified)
  end

  test "reify round-trips Int type, literals, and stuck op spines" do
    assert Quote.reify({:vint_type}) == {:int_type}
    assert Quote.reify({:vint, 8}) == {:int_lit, 8}

    stuck =
      {:vneutral, {:napp, {:napp, {:nglobal, :int_add}, {:vneutral, {:nvar, 0}}}, {:vint, 1}}}

    assert Quote.reify(stuck, 1) == app2(:int_add, {:var, 0}, {:int_lit, 1})
  end

  test "definitional equality: 3 + 5 converts with 8; 7 does not" do
    assert Conv.conv?(app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), {:int_lit, 8}, [], 0, env())
    refute Conv.conv?({:int_lit, 7}, {:int_lit, 8}, [], 0, env())
  end

  test "kernel infers Int for literals and arithmetic spines, and Int : Type0" do
    assert {:ok, {:vdata, :"Std.Int#Int", []}} = Kernel.infer(ctx(), {:int_lit, 42})
    assert {:ok, {:vdata, :"Std.Int#Int", []}} = Kernel.infer(ctx(), app2(:int_add, {:int_lit, 1}, {:int_lit, 2}))
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:int_type})
  end

  test "kernel rejects arithmetic on a non-Int argument (app-argument check, R5)" do
    assert {:error, _} = Kernel.infer(ctx(), app2(:int_add, {:int_lit, 1}, {:type, 0}))
  end
end
