defmodule Cure.Core.PrimBoolInductiveTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel}

  # K2 (spec 2026-07-09): comparisons are builtin-op GLOBAL spines.
  setup do
    %{ctx: Context.empty(Builtins.seed(Env.empty()))}
  end

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "a comparison spine infers to the Bool inductive, not {:vbool_type}", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, app2(:int_lt, {:int_lit, 3}, {:int_lit, 5}))
    assert ty == {:vdata, :"Std.Bool#Bool", []}
  end

  test "equality infers to the Bool inductive", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, app2(:int_eq, {:int_lit, 3}, {:int_lit, 3}))
    assert ty == {:vdata, :"Std.Bool#Bool", []}
  end

  test "the connectives are not ops: an :and spine is an unknown global", %{ctx: ctx} do
    tt = app2(:int_lt, {:int_lit, 1}, {:int_lit, 2})
    # `and` is the Std.Bool case-def, absent from the bare seeded env
    # (was {:unknown_prim, :and} in the prim world).
    assert {:error, {:unknown_global, :and, _details}} = Kernel.infer(ctx, app2(:and, tt, tt))
  end
end
