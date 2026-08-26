defmodule Antigen.BitwiseFoldAntibodyTest do
  @moduledoc """
  Antibody for #2 (Int bitwise delta-globals, batch 2026-07-10). The bitwise
  ops (`band`/`bor`/`bxor`/`bsl`/`bsr`/`bnot`) are additions to the audited δ
  fold table (TCB: `Eval.fold` reached via `Normalise.builtin_op_fold`), so this
  file patrols the same invariants the arithmetic ops carry:

    * a saturated int-literal spine folds to the correct literal (the fold
      terminates and computes the true BEAM `band`/… value);
    * shifts are TOTAL — no divisor-style neutrality (unlike int_div/int_rem),
      negative shift is well-defined, so a literal shift always folds;
    * an OPEN spine (variable operand) stays neutral and compares by generic
      napp congruence — equating no two distinct normal forms.

  This exercises the kernel normalise/conversion path (used in type-checking),
  which is distinct from the emit path covered by `bitwise_ops_test.exs`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app1(g, a), do: {:app, {:global, g}, a}
  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  defp nf(term), do: Normalise.nf(ctx(), term, delta: :certified)

  test "saturated int-literal bitwise spines fold to the correct literal" do
    assert {:int_lit, 2} = nf(app2(:int_band, {:int_lit, 6}, {:int_lit, 3}))
    assert {:int_lit, 7} = nf(app2(:int_bor, {:int_lit, 6}, {:int_lit, 1}))
    assert {:int_lit, 5} = nf(app2(:int_bxor, {:int_lit, 6}, {:int_lit, 3}))
    assert {:int_lit, 16} = nf(app2(:int_bsl, {:int_lit, 1}, {:int_lit, 4}))
    assert {:int_lit, 3} = nf(app2(:int_bsr, {:int_lit, 12}, {:int_lit, 2}))
    assert {:int_lit, -1} = nf(app1(:int_bnot, {:int_lit, 0}))
  end

  test "shifts are total: a negative literal shift folds (no divisor-style neutrality)" do
    # bsl by a negative amount shifts right; bsr by a negative amount shifts
    # left — both defined, both fold, never stuck.
    assert {:int_lit, 4} = nf(app2(:int_bsl, {:int_lit, 16}, {:int_lit, -2}))
    assert {:int_lit, 16} = nf(app2(:int_bsr, {:int_lit, 4}, {:int_lit, -2}))
  end

  test "open bitwise spines stay neutral and equate no distinct normal forms" do
    ctx1 = Context.extend(ctx(), {:vint_type})
    same = app2(:int_band, {:var, 0}, {:int_lit, 6})
    diff_arg = app2(:int_band, {:var, 0}, {:int_lit, 7})
    diff_op = app2(:int_bor, {:var, 0}, {:int_lit, 6})

    # A spine with a free variable operand cannot fold: it stays stuck.
    assert same == Normalise.nf(ctx1, same, delta: :certified)

    venv = Context.env(ctx1)
    assert Conv.conv?(same, same, venv, 1, env())
    refute Conv.conv?(same, diff_arg, venv, 1, env())
    refute Conv.conv?(same, diff_op, venv, 1, env())
  end
end
