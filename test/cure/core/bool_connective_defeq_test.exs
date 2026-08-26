defmodule Cure.Core.BoolConnectiveDefeqTest do
  @moduledoc """
  Phase 4 of retiring the Boolean-connective primitives.

  The headline win: with the connectives defined as `case`-eliminating functions
  over the inductive `Bool` (Std.Bool), the equations hold DEFINITIONALLY (by
  `refl`) — including on OPEN terms with a free Boolean variable `b`. The old
  primitive `and`/`or`/`not` fired only when BOTH operands reduced to concrete
  `True`/`False`, so `and(True, b)` stayed a stuck neutral and never unfolded.
  Now `and(True, b) ≡ b`, `and(False, b) ≡ False`, `not(not b) ≡ b`, etc.

  Also pins the retirement itself (K2 update: `{:prim}` left the grammar
  entirely — a connective SPINE over a bare seeded env is an ordinary unknown
  global, and the numeric equality twins `int_eq`/`int_ne` fold/type as before).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Kernel}

  # An env carrying the certified Std.Bool connective defs (`and`/`or`/`not`/...).
  defp bool_env do
    {:ok, env} =
      Cure.Elab.Program.elaborate("mod M\n  use Std.Bool\n  fn __use(a: Bool) -> Bool = a\nend\n")

    env
  end

  @tt {:ctor, :"Std.Bool#True", []}
  @ff {:ctor, :"Std.Bool#False", []}

  # A single free Boolean variable `b` at de Bruijn index 0.
  @conv_env [{:vneutral, {:nvar, 0}}]
  @depth 1
  @b {:var, 0}

  defp band(a, b), do: {:app, {:app, {:global, :and}, a}, b}
  defp bor(a, b), do: {:app, {:app, {:global, :or}, a}, b}
  defp bnot(a), do: {:app, {:global, :not}, a}

  test "closed equations hold by conversion: not True ≡ False, not False ≡ True" do
    env = bool_env()
    assert Conv.conv?(bnot(@tt), @ff, [], 0, env)
    assert Conv.conv?(bnot(@ff), @tt, [], 0, env)
  end

  test "OPEN-term win: and(True, b) ≡ b and or(False, b) ≡ b for a variable b" do
    env = bool_env()
    assert Conv.conv?(band(@tt, @b), @b, @conv_env, @depth, env)
    assert Conv.conv?(bor(@ff, @b), @b, @conv_env, @depth, env)
  end

  test "OPEN-term win: and(False, b) ≡ False and or(True, b) ≡ True" do
    env = bool_env()
    assert Conv.conv?(band(@ff, @b), @ff, @conv_env, @depth, env)
    assert Conv.conv?(bor(@tt, @b), @tt, @conv_env, @depth, env)
  end

  test "double negation not(not b) is propositional, NOT definitional (as in Agda/Lean)" do
    env = bool_env()
    # `not (not b)` on a neutral `b` produces a stuck `case`-of-`case`; reducing it
    # to `b` needs case-analysis on `b` (a propositional proof), not `refl`. This
    # matches intensional type theory — the kernel does NOT do case-commuting
    # conversion. (The spec's §6 listing of not(not b) ≡ b as definitional
    # overstates it; the one-step equations above are the real definitional wins.)
    refute Conv.conv?(bnot(bnot(@b)), @b, @conv_env, @depth, env)
  end

  test "the win is genuine δ-reduction, not a structural accident" do
    env = bool_env()
    # Without the signature no global unfolds, so the open redex is NOT structural
    # equal to `b`; and even with δ, `and(True, b) ≢ not b`.
    refute Conv.conv?(band(@tt, @b), @b, @conv_env, @depth, nil)
    refute Conv.conv?(band(@tt, @b), bnot(@b), @conv_env, @depth, env)
  end

  # -- retirement of the primitive path --------------------------------------

  defp ctx, do: Context.empty(Builtins.seed(Env.empty()))

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "a connective spine over the bare seeded env is an unknown global (was {:unknown_prim, _})" do
    assert {:error, {:unknown_global, :and, _details}} = Kernel.infer(ctx(), app2(:and, @tt, @ff))
    assert {:error, {:unknown_global, :or, _details}} = Kernel.infer(ctx(), app2(:or, @tt, @ff))
    assert {:error, {:unknown_global, :not, _details}} = Kernel.infer(ctx(), {:app, {:global, :not}, @tt})
  end

  test "a connective spine over the bare seeded env does not fold in eval (stuck neutral)" do
    v = Eval.eval({:app, {:app, {:global, :and}, @tt}, @ff}, [])
    refute v == Eval.eval(@ff, [])
    assert match?({:vneutral, _}, v)
  end

  test "numeric equality twins int_eq/int_ne fold and type to Bool (K2 spines)" do
    ctx = ctx()
    alias Cure.Core.Normalise

    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx, app2(:int_eq, {:int_lit, 4}, {:int_lit, 4}), delta: :certified)

    assert {:ctor, :"Std.Bool#True", []} =
             Normalise.nf(ctx, app2(:int_ne, {:int_lit, 4}, {:int_lit, 5}), delta: :certified)

    assert {:ok, {:vdata, :"Std.Bool#Bool", []}} = Kernel.infer(ctx, app2(:int_eq, {:int_lit, 1}, {:int_lit, 1}))
    assert {:ok, {:vdata, :"Std.Bool#Bool", []}} = Kernel.infer(ctx, app2(:int_ne, {:int_lit, 1}, {:int_lit, 2}))
  end
end
