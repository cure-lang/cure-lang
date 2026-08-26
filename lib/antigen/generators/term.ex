defmodule Antigen.Generators.Term do
  @moduledoc """
  The dependent Core term generator (spec §6). Mode-directed inversion of the
  kernel's bidirectional rules; every semantic side-condition is discharged by
  the kernel's own fuel-bounded conversion (`@gen_fuel`). A canonical-inhabitant
  fallback (`SigMenu.canon/2`) makes generation total — at size 0 or an empty
  option set the generator emits the canonical term (spec §6.4).
  """
  alias Antigen.Gen
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Antigen.Generators.Context, as: CtxGen
  alias Cure.Core.{Context, Eval, Inductive, Normalise}

  @gen_fuel 500
  def gen_fuel, do: @gen_fuel

  # Effective-size cap. `gen/3` now constructs lazily (see the `gen/3` seam
  # below), so this is no longer bounding an exponential eager tree — it bounds
  # the *typechecking cost* the assays pay per generated term (a depth-N term is
  # O(N)+ to `infer`/`nf`/`conv`). Raised well past the former eager-era `3` now
  # that construction is O(depth): the generator reaches genuinely deep terms
  # while keeping per-term assay work bounded.
  @max_size 12
  def max_size, do: @max_size

  @spec gen_term(Context.t(), Cure.Core.Term.t()) :: Gen.t()
  def gen_term(ctx, goal), do: Gen.sized(fn size -> gen(ctx, goal, min(size, @max_size)) end)

  @assay_ids ["term/infer_check", "term/subject_reduction", "term/normalization", "term/erasure_preservation"]
  def assay_ids, do: @assay_ids

  @doc "A `Gen` of a `:typed_term` challenge tagged for `assay_id`."
  @spec typed_term(String.t()) :: Gen.t()
  def typed_term(assay_id) when is_binary(assay_id) do
    env = SigMenu.env_of(:v1)

    Gen.bind(CtxGen.gen(env), fn ctx_types ->
      ctx = SigMenu.rebuild_context(env, ctx_types)

      Gen.bind(goal_gen(ctx), fn goal ->
        Gen.bind(gen_term(ctx, goal), fn term ->
          Gen.return(
            Challenge.new(
              kind: :typed_term,
              assay: assay_id,
              label: :well_typed,
              payload: %{sig: :v1, ctx: ctx_types, type: goal, term: top_level_term(ctx, goal, term)}
            )
          )
        end)
      end)
    end)
  end

  # Route a check-mode-only top-level term through an identity-application wrap so
  # Assays.Term.run/2's unconditional `k.infer.(ctx, p.term)` never hits a shape
  # with no infer path (a bare `:pair` has no infer clause; a bare param-bearing
  # `:ctor` errors `:ctor_requires_checking_mode`). `infer` on `{:app, {:lam, Cure.Core.Grade.unrestricted(), goal,
  # {:var,0}}, term}` infers the identity lambda's `goal -> goal`, then CHECKS
  # `term` against the domain `goal` — the check-mode path these shapes need — and
  # the overall type reduces back to `goal`, so downstream use of `inferred` is
  # unaffected. Every other v1 top-level shape already has a working infer path.
  defp top_level_term(ctx, goal, term) do
    if check_mode_only?(ctx, term),
      do: {:app, {:lam, Cure.Core.Grade.unrestricted(), goal, {:var, 0}}, term},
      else: term
  end

  # The Sigma pair `mk_pair` is check-mode-only (a ctor of a params-carrying family),
  # handled by the general ctor clause below — no separate primitive-pair clause (D2).
  defp check_mode_only?(ctx, {:ctor, cname, _args}) do
    sig = Context.signature(ctx)

    case Inductive.ctor_family(sig, cname) do
      nil -> false
      fam -> Inductive.param_count(sig, fam) > 0
    end
  end

  defp check_mode_only?(_ctx, _other), do: false

  # A goal over the current context: a closed menu goal, or the (possibly
  # stuck-indexed) Vec type of a Vec-typed context variable. Offering the *exact*
  # type of an existing variable guarantees the goal is inhabitable (that var
  # inhabits it), so `canon`'s stuck-Vec fallback always finds a witness — never
  # `nil`. This is what drives stuck-index generation (spec §6.3/§6.4).
  defp goal_gen(ctx) do
    base = Enum.map(SigMenu.goal_types(), fn g -> {1, Gen.return(g)} end)

    depth = Context.length(ctx)

    vec_var_goals =
      for k <- if(depth == 0, do: [], else: Enum.to_list(0..(depth - 1))),
          ty = Normalise.quote(Context.lookup(ctx, k), depth),
          match?({:data, :Vec, _, _}, ty),
          do: {1, Gen.return(ty)}

    Gen.frequency(base ++ vec_var_goals)
  end

  @spec default_gen() :: Gen.t()
  def default_gen do
    Gen.frequency(Enum.map(@assay_ids, fn id -> {1, typed_term(id)} end))
  end

  # The lazy seam: every recursive descent goes through `gen/3`, which defers the
  # actual rule construction (`gen_build/3`) behind `Gen.lazy`. So building one
  # level yields only thin lazy thunks for its sub-goals; the backend forces a
  # thunk only when sampling descends into that branch. Construction is therefore
  # O(depth) along the sampled path, not O(branching^depth) — this is what lifts
  # the depth ceiling that the eager reified AST imposed (the `@max_size 3`
  # workaround). `gen_build/3` and all its helpers call `gen/3` (never
  # `gen_build/3` directly), so laziness is pervasive with a single wrapper.
  defp gen(ctx, goal, size), do: Gen.lazy(fn -> gen_build(ctx, goal, size) end)

  # size 0 → canonical inhabitant (total, no search).
  defp gen_build(ctx, goal, 0), do: Gen.return(SigMenu.canon(ctx, goal))

  defp gen_build(ctx, goal, size) do
    wgoal = whnf(ctx, goal)
    rules = intro_rules(ctx, goal, wgoal, size) ++ elim_rules(ctx, goal, size)

    case rules do
      [] -> Gen.return(SigMenu.canon(ctx, goal))
      rs -> Gen.frequency([{1, Gen.return(SigMenu.canon(ctx, goal))} | rs])
    end
  end

  # -- check-mode introductions ----------------------------------------------
  defp intro_rules(ctx, _goal, {:pi, _g, dom, cod}, size) do
    body_ctx = Context.extend(ctx, Eval.eval(dom, Context.env(ctx)))

    [
      {3,
       Gen.bind(gen(body_ctx, cod, size - 1), fn b -> Gen.return({:lam, Cure.Core.Grade.unrestricted(), dom, b}) end)}
    ]
  end

  defp intro_rules(ctx, _goal, {:data, :Sigma, [a, {:lam, _g, _a, b}], []}, size) do
    [
      {3,
       Gen.bind(gen(ctx, a, size - 1), fn av ->
         # `b` is the Σ codomain body, one binder deeper than `ctx` (the `{:lam, Cure.Core.Grade.unrestricted(), a, b}`
         # binds the first component); the second component inside `{:ctor, :mk_pair,
         # [av, bv]}` must be a term in the UNEXTENDED `ctx`, so β-substitute `av` for
         # `b`'s own bound variable via `SigMenu.subst0/3` (same reasoning as
         # `SigMenu.canon`'s Sigma clause). Unreachable in v1 but must stay correct.
         Gen.bind(gen(ctx, SigMenu.subst0(b, av, ctx), size - 1), fn bv ->
           Gen.return({:ctor, :mk_pair, [av, bv]})
         end)
       end)}
    ]
  end

  # The kernel's reified data normal form places Vec's sole (index) argument in
  # the *params* slot with an empty *indices* slot (see SigMenu.vec_index/2), so
  # match position-agnostically over `params ++ indices`.
  defp intro_rules(ctx, _goal, {:data, :Vec, p, idx}, size) do
    [i] = p ++ idx
    ctor_rules_for_vec(ctx, i, size)
  end

  defp intro_rules(_ctx, _goal, {:data, :Nat, _, _}, size) do
    [
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return(n) end)}
    ]
  end

  defp intro_rules(_ctx, _goal, {:data, :Bd, _, _}, _size) do
    [{2, Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])}]
  end

  defp intro_rules(_ctx, _goal, {:type, _}, _size) do
    [{2, Gen.member_of([SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})])}]
  end

  defp intro_rules(ctx, _goal, {:data, :List, [a], _}, size) do
    nil_rule = {2, Gen.return({:ctor, :Nil, []})}

    cons_rules =
      if SigMenu.inhabitable?(ctx, a) do
        [
          {2,
           Gen.bind(gen(ctx, a, size - 1), fn hd ->
             Gen.bind(gen(ctx, {:data, :List, [a], []}, size - 1), fn tl ->
               Gen.return({:ctor, :Cons, [hd, tl]})
             end)
           end)}
        ]
      else
        []
      end

    [nil_rule | cons_rules]
  end

  defp intro_rules(_ctx, _goal, _other, _size), do: []

  # Constructor choice under indices (spec §6.3): vnil iff i≡Z, vcons iff i≡S(j).
  defp ctor_rules_for_vec(ctx, i, size) do
    case whnf(ctx, i) do
      {:ctor, :Z, []} ->
        [{2, Gen.return({:ctor, :vnil, []})}]

      {:ctor, :S, [j]} ->
        if SigMenu.inhabitable?(ctx, SigMenu.vec(j)) do
          [
            {2,
             Gen.bind(gen(ctx, SigMenu.nat(), size - 1), fn x ->
               Gen.bind(gen(ctx, SigMenu.vec(j), size - 1), fn tail ->
                 Gen.return({:ctor, :vcons, [j, x, tail]})
               end)
             end)}
          ]
        else
          []
        end

      _stuck ->
        # stuck index: only eliminations apply (Task 4); intros offer nothing
        []
    end
  end

  # A small closed Nat generator (numerals), for variety at Nat goals.
  defp gen_nat(0), do: Gen.return({:ctor, :Z, []})

  defp gen_nat(size) do
    Gen.frequency([
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return({:ctor, :S, [n]}) end)}
    ])
  end

  # -- infer-mode eliminations (available at every goal) ----------------------
  # Each elimination builds a term whose inferred type must convert with `goal`
  # under @gen_fuel; candidates that don't converge are simply not offered.
  defp elim_rules(ctx, goal, size) do
    var_rules(ctx, goal) ++
      indir_rules(ctx, goal, size) ++
      app_rule(ctx, goal, size) ++
      case_rule(ctx, goal, size) ++
      proj_rules(ctx, goal)
  end

  # Context variables whose type converts with the goal.
  defp var_rules(ctx, goal) do
    depth = Context.length(ctx)

    for k <- if(depth == 0, do: [], else: Enum.to_list(0..(depth - 1))),
        accept_infer?(ctx, {:var, k}, goal) do
      {3, Gen.return({:var, k})}
    end
  end

  # INDIR: saturate a certified-def head into the goal. v1 heads: plus/2, dbl/1.
  # We generate all arguments at their (dependent) domain types, then accept iff
  # the saturated application's inferred type converges with the goal.
  defp indir_rules(ctx, goal, size) when size > 1 do
    Enum.flat_map([:plus, :dbl], fn head ->
      saturate(ctx, {:global, head}, def_type(ctx, head), goal, size)
    end)
  end

  # Weight for the redex-producing eliminations (β-`app`, ι-`case`, δ-INDIR).
  # Deliberately higher than the leaf/intro weights so a comfortable majority of
  # generated terms contain a firing redex — keeps the reduction-activity health
  # metric (spec §8, floor 0.25) well clear of its floor rather than hovering at
  # it (which made it flaky at weight 2). Tuning, not floor-lowering (spec §11).
  @redex_weight 5

  defp indir_rules(_ctx, _goal, _size), do: []

  # Plain application (manufactures β-redexes INDIR cannot): apply a freshly
  # generated lambda. Restricted to a Nat goal so the Nat-typed binder can be
  # USED by the body (via `gen_referencing/4`) rather than shipped unused — a
  # Bd/Vec-goal body cannot reference a Nat argument, so such a lam would be
  # dead weight that only drags down the binder-usage health metric (spec §8).
  # Redex coverage at other goals still comes from the binderless Bd-`case`
  # (ι-redex) and INDIR (δ/ι), so nothing is lost.
  defp app_rule(ctx, goal, size) when size > 1 do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} ->
        dom = SigMenu.nat()
        body_ctx = Context.extend(ctx, Eval.eval(dom, Context.env(ctx)))

        [
          {@redex_weight,
           Gen.bind(gen_referencing(body_ctx, shift_goal(goal), size - 1, 0), fn body ->
             Gen.bind(gen(ctx, dom, size - 1), fn arg ->
               Gen.return({:app, {:lam, Cure.Core.Grade.unrestricted(), dom, body}, arg})
             end)
           end)}
        ]

      _ ->
        []
    end
  end

  defp app_rule(_ctx, _goal, _size), do: []

  # A generator biased to REFERENCE de Bruijn index `k` (a Nat variable in
  # scope), so binders it sits under don't ship unused (health gate §8). Only
  # meaningful when the goal is Nat (the sole v1 type reachable from a bare Nat
  # variable); otherwise it falls back to the ordinary generator.
  defp gen_referencing(ctx, goal, size, k) do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} ->
        Gen.frequency([
          {4, Gen.return({:var, k})},
          {2, Gen.return({:ctor, :S, [{:var, k}]})},
          {2,
           Gen.bind(gen(ctx, SigMenu.nat(), size - 1), fn m ->
             Gen.return({:app, {:app, {:global, :plus}, {:var, k}}, m})
           end)},
          {1, gen(ctx, goal, size)}
        ])

      _ ->
        gen(ctx, goal, size)
    end
  end

  # case on a menu family scrutinee (Nat or Bd), constant motive λ_. goal.
  # Gated on the goal's (whnf'd) shape, mirroring `app_rule`: spec §6.1's
  # `Type 0` row is deliberately narrower than the full elimination menu
  # (var/INDIR only) — WITHOUT this guard, `case` would still typecheck at a
  # `{:type, _}` goal, silently broadening the generator past what the rule
  # table documents and making Task 3's Type-0-goal test unreliable.
  defp case_rule(ctx, goal, size) when size > 1 do
    case whnf(ctx, goal) do
      {:type, _} ->
        # Spec §6.1's Type-0 row is var/INDIR only.
        []

      {:data, :Nat, _, _} ->
        # At a Nat goal both families are useful: the Bd-`case` is binderless,
        # and the Nat-`case`'s S-branch predecessor (a Nat) CAN be used by the
        # Nat-typed branch body (`branches/4` biases toward it).
        case_for(ctx, :Bd, goal, size) ++ case_for(ctx, :Nat, goal, size)

      _ ->
        # At a Bd/Vec goal only the binderless Bd-`case` is offered: a Nat-`case`
        # here would bind a Nat predecessor its non-Nat body can never reference,
        # producing a dead binder that only hurts binder-usage (spec §8). Redex
        # coverage is preserved (Bd-`case` on a constructor scrutinee is an
        # ι-redex; INDIR supplies δ/ι).
        case_for(ctx, :Bd, goal, size)
    end
  end

  defp case_rule(_ctx, _goal, _size), do: []

  defp case_for(ctx, fam, goal, size) do
    scrut_ty = {:data, fam, [], []}
    motive = {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, shift_goal(goal)}

    [
      {@redex_weight,
       Gen.bind(gen(ctx, scrut_ty, size - 1), fn scrut ->
         Gen.bind(branches(ctx, fam, goal, size - 1), fn brs ->
           Gen.return({:case, scrut, motive, brs})
         end)
       end)}
    ]
  end

  # Projection (via single-branch ι-on-case over mk_pair) of a Γ-variable of Sigma
  # type whose relevant component meets the goal. The Σ is Sigma(Nat, const-Nat) in
  # v1 (a, b closed), so the case motive is the constant component type.
  defp proj_rules(ctx, goal) do
    depth = Context.length(ctx)

    Enum.flat_map(if(depth == 0, do: [], else: Enum.to_list(0..(depth - 1))), fn k ->
      case whnf(ctx, Normalise.quote(Context.lookup(ctx, k), depth)) do
        {:data, :Sigma, [a, {:lam, _g, _a, b}], []} = st ->
          fst_t = {:case, {:var, k}, {:lam, Cure.Core.Grade.unrestricted(), st, a}, [{:mk_pair, 2, {:var, 1}}]}
          snd_t = {:case, {:var, k}, {:lam, Cure.Core.Grade.unrestricted(), st, b}, [{:mk_pair, 2, {:var, 0}}]}
          fst_r = if accept_infer?(ctx, fst_t, goal), do: [{2, Gen.return(fst_t)}], else: []
          snd_r = if accept_infer?(ctx, snd_t, goal), do: [{2, Gen.return(snd_t)}], else: []
          fst_r ++ snd_r

        _ ->
          []
      end
    end)
  end

  # Saturate `head : head_ty` (a Π-telescope) with generated args, accepting only
  # if the result's inferred type converges with `goal`. Args are generated at
  # each domain with earlier args substituted (via the closure env) into later
  # domains — the dependent-generation core (spec §6.2).
  defp saturate(ctx, head_term, head_ty, goal, size) do
    args_gen = gen_args(ctx, head_ty, size, [])

    [
      {@redex_weight,
       Gen.bind(args_gen, fn args ->
         term = Enum.reduce(args, head_term, fn a, acc -> {:app, acc, a} end)
         if accept_infer?(ctx, term, goal), do: Gen.return(term), else: Gen.return(SigMenu.canon(ctx, goal))
       end)}
    ]
  end

  # Walk a Π-telescope, generating each domain argument.
  defp gen_args(ctx, ty, size, acc) do
    case whnf(ctx, ty) do
      {:pi, _g, dom, cod} ->
        Gen.bind(gen(ctx, dom, size - 1), fn a ->
          # substitute `a` into `cod` by evaluating cod's closure with a's value
          cod_ctx_ty = subst_cod(cod, a, ctx)
          gen_args(ctx, cod_ctx_ty, size, [a | acc])
        end)

      _ ->
        Gen.return(Enum.reverse(acc))
    end
  end

  # cod is a Term with de Bruijn 0 = the just-bound arg; substitute `a` for it.
  defp subst_cod(cod, a, ctx) do
    env = Context.env(ctx)
    Normalise.quote(Eval.eval(cod, [Eval.eval(a, env) | env]), Context.length(ctx))
  end

  # Branch bodies for a `case` on `fam` at (constant-motive) goal. The Nat
  # S-branch's body is generated with `gen_referencing/4` so it tends to USE the
  # bound predecessor (var 0) — this is only invoked at a Nat goal (see
  # `case_rule`), where the predecessor is type-compatible with the body.
  defp branches(ctx, :Nat, goal, size) do
    Gen.bind(gen(ctx, goal, size), fn zbody ->
      kctx = Context.extend(ctx, Eval.eval(SigMenu.nat(), Context.env(ctx)))

      Gen.bind(gen_referencing(kctx, shift_goal(goal), size, 0), fn sbody ->
        Gen.return([{:Z, 0, zbody}, {:S, 1, sbody}])
      end)
    end)
  end

  defp branches(ctx, :Bd, goal, size) do
    Gen.bind(gen(ctx, goal, size), fn tb ->
      Gen.bind(gen(ctx, goal, size), fn fb ->
        Gen.return([{:T, 0, tb}, {:F, 0, fb}])
      end)
    end)
  end

  # Accept an infer-mode candidate iff its inferred type converts with the goal
  # under @gen_fuel (spec §6.1). Fuel exhaustion or false ⇒ not offered.
  defp accept_infer?(ctx, term, goal) do
    case Cure.Core.Kernel.infer(ctx, term) do
      {:ok, inferred_val} ->
        depth = Context.length(ctx)
        inferred_term = Normalise.quote(inferred_val, depth)

        case Cure.Core.Conv.conv_within?(
               inferred_term,
               goal,
               Context.env(ctx),
               depth,
               Context.signature(ctx),
               @gen_fuel
             ) do
          {:ok, true} -> true
          _ -> false
        end

      {:error, _} ->
        false
    end
  end

  defp def_type(ctx, name) do
    %{type: ty} = Cure.Core.Env.get_def(Context.signature(ctx), name)
    ty
  end

  # A goal moved under one extra binder (its free de Bruijn indices shift by 1).
  defp shift_goal(goal), do: Cure.Core.Term.shift(goal, 1, 0)

  # whnf that degrades to the input term on fuel exhaustion (never crashes gen).
  # Bounded by @gen_fuel, not the default :infinity — spec §6.3: the shape/
  # index inspections this backs ("is the goal a Pi/data/Vec(S j)?") are
  # semantic conditions and must run under the same @gen_fuel-bounded kernel
  # calls as the acceptance rule, "not a separate unbounded check".
  defp whnf(ctx, term) do
    case Normalise.whnf(ctx, term, fuel: @gen_fuel) do
      :fuel_exhausted -> term
      w -> w
    end
  end
end
