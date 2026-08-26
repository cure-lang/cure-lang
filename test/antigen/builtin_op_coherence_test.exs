defmodule Antigen.BuiltinOpCoherenceTest do
  @moduledoc """
  K2 antibody (spec 2026-07-09 §3/§4.2): coherence pins for the builtin-op
  GLOBAL representation of primitive arithmetic. Independent of the T1 kernel
  suite — this file patrols the invariants Antigen's generators lean on:

    * §G.1 literal folds (comparisons land on the canonical inductive Bool);
    * §G.1 rule 1 — div/rem by literal ZERO stays neutral (never crashes,
      never folds);
    * open spines stay stuck and compare by generic napp congruence (§1.8 —
      the same judgement strength as the retired {:nprim} clause);
    * R1 — a USER def named `int_add` (the actual reserved registry key)
      normalizes by ITS body, never the builtin table (registry keying via the
      def-record marker, not the bare atom).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "§G.1 literal folds: arithmetic on literals computes; comparisons land on inductive Bool" do
    assert {:int_lit, 8} =
             Normalise.nf(ctx(), app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)

    assert {:int_lit, -6} =
             Normalise.nf(ctx(), app2(:int_mul, {:int_lit, 2}, {:int_lit, -3}), delta: :certified)

    assert {:float_lit, 3.5} =
             Normalise.nf(ctx(), app2(:float_add, {:float_lit, 1.5}, {:float_lit, 2.0}), delta: :certified)

    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx(), app2(:int_le, {:int_lit, 2}, {:int_lit, 2}), delta: :certified)

    assert {:ctor, :"Std.Bool#False", []} =
             Normalise.nf(ctx(), app2(:float_gt, {:float_lit, 1.0}, {:float_lit, 2.0}), delta: :certified)
  end

  test "§G.1 rule 1: div/rem by literal zero stays NEUTRAL (partial ops never fold or crash)" do
    for g <- [:int_div, :int_rem] do
      spine = app2(g, {:int_lit, 7}, {:int_lit, 0})
      assert spine == Normalise.nf(ctx(), spine, delta: :certified)
    end

    zdiv = app2(:float_div, {:float_lit, 1.0}, {:float_lit, 0.0})
    assert zdiv == Normalise.nf(ctx(), zdiv, delta: :certified)
  end

  test "§1.8 open-spine congruence: stuck spines compare like the retired :nprim neutrals" do
    ctx1 = Context.extend(ctx(), {:vint_type})
    same = app2(:int_add, {:var, 0}, {:int_lit, 1})
    diff_arg = app2(:int_add, {:var, 0}, {:int_lit, 2})
    diff_op = app2(:int_sub, {:var, 0}, {:int_lit, 1})

    # stays stuck under nf
    assert same == Normalise.nf(ctx1, same, delta: :certified)

    venv = Context.env(ctx1)
    assert Conv.conv?(same, same, venv, 1, env())
    refute Conv.conv?(same, diff_arg, venv, 1, env())
    refute Conv.conv?(same, diff_op, venv, 1, env())
  end

  test "R1: a user-registered int_add normalizes by its OWN body, never the builtin table" do
    ty =
      {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
       {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), {:int_type},
       {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 42}}}

    user_env = Env.empty() |> Env.add_def(:int_add, ty, body) |> Env.certify(:int_add)
    user_ctx = Context.empty(user_env)

    assert {:int_lit, 42} =
             Normalise.nf(user_ctx, app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
  end
end
