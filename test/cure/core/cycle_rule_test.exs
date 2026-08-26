defmodule Cure.Core.CycleRuleTest do
  @moduledoc """
  Agda Cycle rule (Rules/LHS/Unify.hs): an index equation `x =?= v` is ABSURD
  when the datatype variable `x` occurs STRONGLY RIGID in `v` — i.e. the path
  from `v` down to the `x` occurrence passes through constructors only, never a
  defined-function application or other neutral. Agda emits `NoUnify`/`UnifyCycle`
  there; Cure's `branch_unify` must return `:impossible`.

  Soundness crux (why the guard is ctor/data-spine-only): `x = S(x)` is absurd by
  acyclicity of the inductive, but `x = f(x)` for a DEFINED `f` is NOT — `f` might
  be the identity. So the discharge fires only through rigid constructor spines.

  This is the precise (Idris/Agda-faithful) verdict; it supersedes the earlier
  conservative choice that degraded every cycle to `:undecided`/`:trivial`
  (roadmap A2/#23 hardening). See `unify_indices_test` (a) and
  `branch_unify_occurs_test`, updated in the same change.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}

  # `same : SameLen(k, k)` — a refl-shaped index constraint. Matched against a
  # scrutinee `SameLen(a, S(a))` it forces `a = S(a)` (via a = k, k = S(a)): the
  # merged strongly-rigid cycle. This is EXACTLY the shape of oracle cyc01
  # (`MyEq(Nat, n, S(n))` vs `mrefl : MyEq(a, w, w)`).
  @same_src "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"
  defp same_sig,
    do:
      (fn ->
         {:ok, s} = Cure.Elab.Program.elaborate(@same_src)
         s
       end).()

  defp one_var_ctx(s), do: Context.extend(Context.empty(s), {:vdata, :Nat, []})

  test "merged strongly-rigid cycle: `same : SameLen(k,k)` vs SameLen(a, S(a)) is :impossible" do
    s = same_sig()
    ctx = one_var_ctx(s)
    # scrutinee indices [a, S(a)] over the single outer var a
    scrut = [{:vneutral, {:nvar, 0}}, {:vctor, :S, [{:vneutral, {:nvar, 0}}]}]
    assert :impossible = Kernel.branch_unify(ctx, :SameLen, :same, scrut)
  end

  test "direct strongly-rigid cycle `MkWr(x) ~ x` (adversarial dangling index) is :impossible" do
    # Mirror of branch_unify_occurs_test's adversary: a ctor whose result index
    # references a var OUTSIDE its own telescope, producing `x = MkWr(x)` in a
    # single equation. Under the Cycle rule this is absurd, not a degrade.
    dec = {:data, :Dec, [], []}
    wr = {:data, :Wr, [], []}

    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [
        Inductive.ctor(:MkWr, [{:d, dec}], [])
      ])
      |> Inductive.declare(Inductive.family(:IW, [], [{:w, wr}], 0), [
        Inductive.ctor(:iw, [{:p, dec}], [{:ctor, :MkWr, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(wr, []))
    scrut_index = {:vneutral, {:nvar, 0}}
    assert :impossible = Kernel.branch_unify(ctx, :IW, :iw, [scrut_index])
  end

  test "conservative guard: a WEAKLY-rigid occurrence (index var under a neutral app, not a ctor) does NOT fire :impossible" do
    # Adversary: a ctor whose result index wraps the dangling outer var under a
    # NEUTRAL APPLICATION head `(x x)` rather than a constructor. The occurrence
    # is not strongly rigid (path goes through an application, which for a defined
    # head could be the identity), so the Cycle rule must NOT discharge it — the
    # verdict degrades to :trivial/:undecided, never :impossible.
    wr = {:data, :Wr, [], []}

    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [
        Inductive.ctor(:MkWr, [], [])
      ])
      # result index {:app, {:var,1}, [{:var,1}]} : the outer var applied to itself,
      # a neutral spine — NOT a ctor/data spine.
      |> Inductive.declare(Inductive.family(:IA, [], [{:w, wr}], 0), [
        Inductive.ctor(:ia, [], [{:app, {:var, 1}, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(wr, []))
    scrut_index = {:vneutral, {:nvar, 0}}
    refute :impossible == Kernel.branch_unify(ctx, :IA, :ia, [scrut_index])
  end
end
