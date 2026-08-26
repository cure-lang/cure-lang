defmodule Cure.Core.ReduceUnfoldedFreezeConsistencyTest do
  @moduledoc """
  Regression + termination antibody for the A6 lazy-unfolding freeze in
  `Normalise.reduce_unfolded` (finding K1).

  The freeze keeps a certified def-application FOLDED when unfolding only
  re-exposes a stuck eliminator. Before the fix it fired INCONSISTENTLY:
  `f(<literal-ctor>, x)` froze (the outer `case` ι-fired inside `eval`, leaving a
  stuck inner `case x`) while `f(<reducible-global>, x)` did NOT (the outer case
  was forced inside `reduce_unfolded`, which returned the residual `case x`
  expanded). Two definitionally-equal terms then had different normal forms and
  `conv?` returned false.

  The fix recurses on the ι-result so a residual stuck `ncase` propagates `:stuck`
  up and the WHOLE application freezes — consistently. It only ever freezes MORE,
  so NF termination is preserved (verified here on mutually-recursive stuck defs).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Normalise}

  @u Cure.Core.Grade.unrestricted()
  @nat {:data, :Nat, [], []}
  @m {:data, :M, [], []}
  @unit {:data, :Unit, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}
  defp mkm(a), do: {:ctor, :MkM, [a]}
  @mku {:ctor, :MkU, []}

  # plus a b = case a { Z -> b | S k -> S (plus k b) }
  defp plus_body do
    {:lam, @u, @nat,
     {:lam, @u, @nat,
      {:case, {:var, 1}, {:lam, @u, @nat, @nat},
       [{:Z, 0, {:var, 0}}, {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}]}}}
  end

  defp plus_type, do: {:pi, @u, @nat, {:pi, @u, @nat, @nat}}

  # g u = case u { MkU -> MkM Z }   (a non-recursive def that reduces on a ctor)
  defp g_body, do: {:lam, @u, @unit, {:case, {:var, 0}, {:lam, @u, @unit, @m}, [{:MkU, 0, mkm(@z)}]}}
  defp g_type, do: {:pi, @u, @unit, @m}

  # combine m n = case m { MkM a -> case n { MkM b -> MkM (plus a b) } }  (non-recursive)
  defp combine_body do
    {:lam, @u, @m,
     {:lam, @u, @m,
      {:case, {:var, 1}, {:lam, @u, @m, @m},
       [
         {:MkM, 1,
          {:case, {:var, 1}, {:lam, @u, @m, @m},
           [{:MkM, 1, mkm({:app, {:app, {:global, :plus}, {:var, 1}}, {:var, 0}})}]}}
       ]}}}
  end

  defp combine_type, do: {:pi, @u, @m, {:pi, @u, @m, @m}}

  # f n = case n { Z -> Z | S k -> h k }   and   h n = case n { Z -> Z | S k -> f k }  (MUTUAL)
  defp f_body(callee) do
    {:lam, @u, @nat,
     {:case, {:var, 0}, {:lam, @u, @nat, @nat}, [{:Z, 0, @z}, {:S, 1, {:app, {:global, callee}, {:var, 0}}}]}}
  end

  defp env do
    Builtins.seed(Env.empty())
    |> Env.add_def(:plus, plus_type(), plus_body())
    |> Env.certify(:plus)
    |> Env.add_def(:g, g_type(), g_body())
    |> Env.certify(:g)
    |> Env.add_def(:combine, combine_type(), combine_body())
    |> Env.certify(:combine)
    |> Env.add_def(:f, {:pi, @u, @nat, @nat}, f_body(:h))
    |> Env.certify(:f)
    |> Env.add_def(:h, {:pi, @u, @nat, @nat}, f_body(:f))
    |> Env.certify(:h)
  end

  # A context with one free variable of type M => {:var, 0} is a stuck neutral.
  defp ctx_m, do: Context.extend(Context.empty(env()), @m)
  defp ctx_nat, do: Context.extend(Context.empty(env()), @nat)

  defp combine(x, y), do: {:app, {:app, {:global, :combine}, x}, y}

  test "K1: combine(MkM Z, x) and combine(g MkU, x) have the SAME normal form" do
    ctx = ctx_m()
    a = combine(mkm(@z), {:var, 0})
    b = combine({:app, {:global, :g}, @mku}, {:var, 0})

    assert Normalise.nf(ctx, a) == Normalise.nf(ctx, b),
           "definitionally-equal terms must share a normal form (freeze consistency)"

    assert Conv.conv?(a, b, Context.env(ctx), Context.length(ctx), Context.signature(ctx)),
           "conv? must accept the two forms"
  end

  test "K1: the shared normal form is the folded application (freeze, not expand)" do
    ctx = ctx_m()
    nf = Normalise.nf(ctx, combine({:app, {:global, :g}, @mku}, {:var, 0}))
    assert {:app, {:app, {:global, :combine}, {:ctor, :MkM, [{:ctor, :Z, []}]}}, {:var, 0}} = nf
  end

  test "NF terminates on mutually-recursive stuck defs (freeze antibody)" do
    ctx = ctx_nat()
    # f (S (S x)) unwinds f->h->f by two and freezes at the stuck `f x`; must not loop.
    nf = Normalise.nf(ctx, {:app, {:global, :f}, s(s({:var, 0}))})
    assert {:app, {:global, :f}, {:var, 0}} = nf
  end
end
