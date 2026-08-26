defmodule Cure.Elab.UnifyMetaCompletenessTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}
  alias Cure.Core.{Env, Inductive}

  # The metavariable traversals in `Unify` (`zonk`, `meta_free?`, `occurs?`) must
  # recurse into EVERY subterm-bearing Core shape. They previously stopped at
  # `{:data}`/`{:ctor}`/`{:app}`/`{:pi}`/`{:lam}` and treated `{:eq}`/`{:sigma}`/
  # `{:pair}`/`{:fst}`/`{:snd}`/`{:refl}`/`{:prim}` as opaque leaves. A meta buried
  # in one of those then (a) survived `zonk` unsubstituted and (b) slipped past
  # `meta_free?`, so the δ-convertibility fallback handed a `{:meta, _}`-bearing
  # term to the TRUSTED evaluator — `no function clause in Cure.Core.Eval.eval/2`,
  # an elaborator crash of the kernel (seen on a higher-order implicit like
  # `subst({P},{x},{y}, e: Eq(a,x,y), px: P(x))`).

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  defp nat_sig do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
  end

  test "zonk substitutes a solution buried in Eq / refl endpoints" do
    ctx = MetaCtx.put_solution(elem(MetaCtx.fresh(MetaCtx.new()), 0), 0, @z)
    t = {:eq, {:meta, 0}, {:meta, 0}, {:refl, {:meta, 0}}}
    assert {:eq, @z, @z, {:refl, @z}} == Unify.zonk(t, ctx)
  end

  test "zonk substitutes a solution buried in inductive Sigma / mk_pair / projections" do
    ctx = MetaCtx.put_solution(elem(MetaCtx.fresh(MetaCtx.new()), 0), 0, @z)

    # Inductive Sigma (D2): the former is `{:data, :Sigma}`, intro `{:ctor,
    # :mk_pair}`, projections the elaborator's `sigma_first`/`sigma_second` global
    # spines — zonk recurses into each and substitutes the buried meta.
    assert {:data, :Sigma, [@z, @z], []} ==
             Unify.zonk({:data, :Sigma, [{:meta, 0}, {:meta, 0}], []}, ctx)

    assert {:ctor, :mk_pair, [@z, @z]} ==
             Unify.zonk({:ctor, :mk_pair, [{:meta, 0}, {:meta, 0}]}, ctx)

    assert {:app, {:global, :sigma_first}, @z} ==
             Unify.zonk({:app, {:global, :sigma_first}, {:meta, 0}}, ctx)

    assert {:app, {:global, :sigma_second}, @z} ==
             Unify.zonk({:app, {:global, :sigma_second}, {:meta, 0}}, ctx)
  end

  test "a metavariable in a builtin-op spine argument unifies structurally (never crashes the kernel)" do
    # ENUMERATED VERDICT FLIP (K2): the retired `{:prim}` node had no structural
    # do_unify clause, so this row used to fall to the δ-convertibility fallback,
    # which had to REFUSE the meta-bearing term ({:error, _} — the old pin was
    # "reject cleanly rather than pass {:meta,_} to the trusted Eval"). The
    # builtin-op GLOBAL spine is an ordinary application, so structural
    # decomposition now runs FIRST and soundly SOLVES the meta — strictly
    # stronger: still no meta ever reaches Eval, and op-argument metas are now
    # solvable (a first-class-ops benefit, spec §0).
    {ctx, m} = MetaCtx.fresh(MetaCtx.new())
    t1 = {:app, {:app, {:global, :int_add}, {:meta, m}}, {:int_lit, 0}}
    t2 = {:app, {:app, {:global, :int_add}, {:int_lit, 1}}, {:int_lit, 0}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nat_sig())
    assert Unify.zonk({:meta, m}, ctx2) == {:int_lit, 1}
  end
end
