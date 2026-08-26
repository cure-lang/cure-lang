defmodule Antigen.StructEqAtomAntibodyTest do
  @moduledoc """
  TCB antibody for Atom literals entering the existing `struct_eq`/`struct_ne`
  primitive fold. The extension must compute only two known Atom values, leave
  neutral or cross-kind spines stuck, add no conversion equations, and remain
  bounded on nested reductions.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())
  defp app2(global, left, right), do: {:app, {:app, {:global, global}, left}, right}
  defp app3(global, type, left, right), do: {:app, app2(global, type, left), right}

  test "known Atom literals reduce through the shared primitive fold" do
    true_ctor = Cure.Elab.Name.qualify("Std.Bool", :True)
    false_ctor = Cure.Elab.Name.qualify("Std.Bool", :False)

    assert {:ctor, ^true_ctor, []} =
             Normalise.nf(
               ctx(),
               app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :node}),
               delta: :certified
             )

    assert {:ctor, ^false_ctor, []} =
             Normalise.nf(
               ctx(),
               app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :leaf}),
               delta: :certified
             )

    assert {:ctor, ^true_ctor, []} =
             Normalise.nf(
               ctx(),
               app3(:struct_ne, {:atom_type}, {:atom_lit, :node}, {:atom_lit, :leaf}),
               delta: :certified
             )
  end

  test "neutral and cross-kind values do not acquire a new reduction equation" do
    neutral_ctx = Context.extend(ctx(), {:vatom_type})
    neutral = app3(:struct_eq, {:atom_type}, {:var, 0}, {:atom_lit, :node})
    assert neutral == Normalise.nf(neutral_ctx, neutral, delta: :certified)

    mixed = app3(:struct_eq, {:atom_type}, {:atom_lit, :node}, {:int_lit, 1})
    assert mixed == Normalise.nf(ctx(), mixed, delta: :certified)

    refute Conv.conv?({:atom_lit, :node}, {:atom_lit, :leaf}, [], 0, env())
    refute Conv.conv?({:atom_lit, :node}, {:int_lit, 1}, [], 0, env())
  end

  test "nested primitive equality reduction terminates by structural descent" do
    nested =
      Enum.reduce(1..128, {:atom_lit, :node}, fn _, value ->
        app3(:struct_eq, {:atom_type}, value, {:atom_lit, :node})
      end)

    task = Task.async(fn -> Normalise.nf(ctx(), nested, delta: :certified, fuel: 10_000) end)

    assert {:ok, _result} = Task.yield(task, 5_000)
  end
end
