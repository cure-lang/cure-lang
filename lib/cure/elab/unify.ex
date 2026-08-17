defmodule Cure.Elab.MetaCtx do
  @moduledoc """
  The elaborator's metavariable context (design spec §5.3): fresh unknowns
  created during elaboration (e.g. a constructor's erased index arguments) and
  their solutions once unification determines them.

  Metavariables live only in the untrusted elaborator. A term reaching the
  trusted kernel must be fully solved (`Unify.zonk/2` substitutes every solution
  away); an unsolved metavariable at that point is an elaboration error.
  """

  defstruct next: 0, solutions: %{}, types: %{}, revision: 0, change_log: %{}

  @type id :: non_neg_integer()
  @type t :: %__MODULE__{
          next: non_neg_integer(),
          solutions: %{id() => Cure.Core.Term.t()},
          types: %{id() => Cure.Core.Term.t()},
          revision: non_neg_integer(),
          change_log: %{non_neg_integer() => [id()]}
        }

  @doc "A fresh, empty metavariable context."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Allocate a fresh metavariable, returning `{ctx, id}`. An optional `type` (the
  metavariable's expected type as a Core term, in the ambient frame) is recorded
  so higher-order (Miller) unification can recover the abstraction-lambda domains
  when solving `?m x̄ := λx̄. t`.
  """
  @spec fresh(t(), Cure.Core.Term.t() | nil) :: {t(), id()}
  def fresh(ctx, type \\ nil)

  def fresh(%__MODULE__{next: n, types: ts} = ctx, type),
    do: {%{ctx | next: n + 1, types: Map.put(ts, n, type)}, n}

  @doc "The recorded type for `id`, or nil if unknown."
  @spec meta_type(t(), id()) :: Cure.Core.Term.t() | nil
  def meta_type(%__MODULE__{types: ts}, id), do: Map.get(ts, id)

  @doc "The solution term for `id`, or nil if unsolved."
  @spec solution(t(), id()) :: Cure.Core.Term.t() | nil
  def solution(%__MODULE__{solutions: s}, id), do: Map.get(s, id)

  @doc "Is `id` solved?"
  @spec solved?(t(), id()) :: boolean()
  def solved?(%__MODULE__{solutions: s}, id), do: Map.has_key?(s, id)

  @doc "Monotone revision of the solution set for attempt-local caches."
  @spec revision(t()) :: non_neg_integer()
  def revision(%__MODULE__{revision: revision}), do: revision

  @doc "Return metavariable ids assigned after `revision` on this context lineage."
  @spec changed_ids_since(t(), non_neg_integer()) :: [id()]
  def changed_ids_since(%__MODULE__{revision: current}, revision) when revision >= current,
    do: []

  def changed_ids_since(%__MODULE__{revision: current, change_log: log}, revision)
      when revision >= 0 do
    (revision + 1)..current
    |> Enum.flat_map(&Map.get(log, &1, []))
    |> Enum.uniq()
  end

  @doc false
  def put_solution(%__MODULE__{solutions: s, revision: revision, change_log: log} = ctx, id, term) do
    if Map.get(s, id) == term do
      ctx
    else
      next_revision = revision + 1

      %{
        ctx
        | solutions: Map.put(s, id, term),
          revision: next_revision,
          change_log: Map.put(log, next_revision, [id])
      }
    end
  end
end

defmodule Cure.Elab.Unify do
  @moduledoc """
  First-order unification of Core terms with metavariables (design spec §5.3).

  Slice 1's index terms are first-order — constructor/data applications over
  `{:ctor, …}`, `{:data, …}`, and applied globals like `andd(d1, d2)` — so
  syntactic unification with occurs-checked metavariable solving is complete for
  them. (Higher-order Miller-pattern unification is a documented extension point
  for indices that apply a metavariable to bound variables.)

  A metavariable is the elaboration-only term `{:meta, id}`. `unify/3` follows
  existing solutions (`force`), solves unsolved metavariables against the other
  side, and otherwise recurses structurally. `zonk/2` finalises a term by
  substituting every solution away.
  """

  alias Cure.Elab.MetaCtx

  @type uterm :: Cure.Core.Term.t() | {:meta, MetaCtx.id()}

  @doc """
  Unify two (possibly metavariable-bearing) terms, refining the context.

  When `sig` (a `Cure.Core.Env` signature) is supplied, a syntactic failure on
  two CLOSED, metavariable-free terms falls back to the trusted δ-capable
  conversion (`Cure.Core.Conv`) — so a computed index like `dmeet(DDec, DDec)`
  unifies with its normal form `DDec` (Idris parity for composed computed
  indices). This is a COMPLETENESS improvement only: it uses the same conversion
  the kernel uses, and the kernel independently re-checks the assembled term, so
  no soundness rests on this fallback (a wrong accept here is caught downstream).
  Without `sig` the behaviour is exactly the prior purely-syntactic unification.
  """
  @spec unify(uterm(), uterm(), MetaCtx.t(), Cure.Core.Env.t() | nil) ::
          {:ok, MetaCtx.t()} | {:error, term()}
  def unify(t1, t2, ctx, sig \\ nil) do
    unify_d(t1, t2, ctx, sig, 0)
  end

  # Depth-tracked unification: `depth` counts the binders crossed so far (Π/λ/Σ
  # codomains). A metavariable is allocated in the *ambient* context (depth 0), so
  # its solution is stored in that frame. The two directions are duals:
  #   * on *solve* (`?m := t` under `depth` binders) the term is strengthened back
  #     to the ambient frame (`solve/4`), and
  #   * on *force* (reading `?m`'s solution under `depth` binders) the ambient
  #     solution is shifted *up* by `depth` into the current scope (`force_d/3`).
  # Together they keep `(a) -> b` vs `(?a) -> ?b` — and the endomorphism `(a) -> a`,
  # whose variable recurs on both sides of the binder — correctly levelled.
  defp unify_d(t1, t2, ctx, sig, depth) do
    f1 = force_d(t1, ctx, depth)
    f2 = force_d(t2, ctx, depth)

    # The overwhelmingly common call-argument case has already-identical Core
    # types. Do not normalise and recursively rediscover that fact: whnf may
    # unfold a large closed datatype and structural unification then repeats the
    # same work for every child. Metavariable solutions have already been forced,
    # so exact equality here is a complete successful unification with no context
    # refinement left to perform.
    if f1 == f2 do
      {:ok, ctx}
    else
      do_unify(whnf_pre(f1, ctx, sig, depth), whnf_pre(f2, ctx, sig, depth), ctx, sig, depth)
    end
  end

  # Weak-head-normalise a forced term BEFORE structural comparison (Idris `nf`,
  # Agda `reduceB`, Lean `whnfCoreAtDefEq` — ledger #11), reusing the meta-aware
  # whnf (unsolved metavariables stay opaque neutrals). This lets a reducible redex
  # like `plus(Z, ?m)` (which δι-reduces to `?m`) unify with `S(Z)` by solving
  # `?m := S(Z)`, instead of failing a naive `{:app,…}` vs `{:ctor,…}` comparison.
  #
  # whnf is applied EXACTLY ONCE per `unify_d` step — `do_unify`'s structural
  # descent re-enters `unify_d` on subterms, which whnf them in turn, so there is
  # NO recurse-on-change loop (an earlier version re-fed the reduced pair to
  # `unify_d`, which diverged whenever whnf's fold/unfold shape oscillated). Gated
  # to:
  #   * `sig != nil` — whnf needs the signature to δ-unfold globals; sig-less
  #     callers keep the prior purely-syntactic behaviour; and
  #   * `depth == 0` (the ambient frame) — where `zonk` (inside `whnf_meta_aware`)
  #     and the binder-shifting `force_d` coincide, so a solved metavariable's
  #     ambient-framed solution needs no shift. Under binders (`depth > 0`) fall
  #     through unchanged; reducing there is a documented future extension.
  defp whnf_pre(t, _ctx, nil, _depth), do: t
  defp whnf_pre(t, _ctx, _sig, depth) when depth != 0, do: t
  defp whnf_pre({:pi, _g, _, _} = t, _ctx, _sig, _depth), do: t
  defp whnf_pre({:lam, _g, _, _} = t, _ctx, _sig, _depth), do: t

  defp whnf_pre(t, ctx, sig, depth) do
    r = whnf_meta_aware(t, ctx, sig, depth)

    # A reduction that turns a NON-lambda into a lambda is an under-applied
    # function being β-expanded to its arity — e.g. a partial spine `app(xs)`
    # (`app` given 1 of its 2 arguments) reduces to `λys. case xs {…}`. That
    # destroys the neutral/syntactic spine the first-order unifier relies on to
    # solve `app(xs) =? app(?a)` (and there is no `:case` unify clause to fall back
    # on), so KEEP the original there. Every ι-reduction WIN this feature targets
    # (`plus(Z, ?m)` → `?m`, `plus(Z, S(Z))` → `S(Z)`) produces a ctor/meta/neutral,
    # never a lambda, so this guard preserves them all.
    if match?({:lam, _g, _, _}, r), do: t, else: r
  end

  # Resolve a metavariable's solution and lift it from the ambient frame into the
  # current binder `depth`. A non-metavariable head is already in the current
  # scope, so it is returned unshifted.
  defp force_d({:meta, id} = t, ctx, depth) do
    case MetaCtx.solution(ctx, id) do
      nil -> t
      sol -> force_d(Cure.Elab.Subst.shift(sol, depth, 0), ctx, depth)
    end
  end

  defp force_d(t, _ctx, _depth), do: t

  # Follow the chain of solutions until the head is not a solved metavariable
  # (depth-agnostic; used by `occurs?`/`zonk` where no binder lifting applies).
  defp force({:meta, id} = t, ctx) do
    case MetaCtx.solution(ctx, id) do
      nil -> t
      sol -> force(sol, ctx)
    end
  end

  defp force(t, _ctx), do: t

  # Try higher-order (Miller) pattern unification before the first-order rules:
  # when one side is a metavariable applied to a spine of DISTINCT bound variables
  # (`?m x̄`) and the other is rigid, solve `?m := λx̄. t` by abstracting `t` over
  # `x̄`, taking the abstraction-lambda domains from `?m`'s recorded type. Any
  # condition unmet → `:fallthrough` to the structural rules, so this is never
  # worse than the prior first-order behaviour. The kernel independently re-checks
  # the zonked solution, so no soundness rests on this (a wrong solve is caught
  # downstream). Idris/Agda pattern-unification parity (ledger #10).
  defp do_unify(t1, t2, ctx, sig, depth) do
    case {flex_application(t1), flex_application(t2)} do
      {{id, argument}, _} ->
        flex_or(flex_rigid_solve(id, argument, t2, ctx, depth), t1, t2, ctx, sig, depth)

      {_, {id, argument}} ->
        flex_or(flex_rigid_solve(id, argument, t1, ctx, depth), t1, t2, ctx, sig, depth)

      _ ->
        case {miller_pattern(t1), miller_pattern(t2)} do
          {{id, vars}, _} -> miller_or(miller_solve(id, vars, t2, ctx, depth), t1, t2, ctx, sig, depth)
          {_, {id, vars}} -> miller_or(miller_solve(id, vars, t1, ctx, depth), t1, t2, ctx, sig, depth)
          _ -> do_unify_struct(t1, t2, ctx, sig, depth)
        end
    end
  end

  # A one-argument flex-rigid equation over a computed argument, for example
  # `?predicate(product) = IsPositive(product)`. This is not a Miller pattern
  # because `product` is not a variable, but it has the canonical abstraction
  # solution `?predicate := λvalue. IsPositive(value)` when the exact argument
  # occurs in the rigid side. Restricted to the ambient frame, one application,
  # a known unary Π type, and meta-free terms; every candidate is occurs-checked
  # and the assembled program is independently checked by the kernel.
  defp flex_application({:app, {:meta, id}, argument}), do: {id, argument}
  defp flex_application(_term), do: nil

  defp flex_rigid_solve(id, argument, rhs, ctx, 0) do
    with true <- meta_free?(argument),
         true <- meta_free?(rhs),
         true <- match?({:data, _, _, _}, rhs),
         true <- contains_term?(rhs, argument),
         {:pi, _grade, domain, _codomain} <- MetaCtx.meta_type(ctx, id),
         body = abstract_exact_term(rhs, argument, 0),
         solution = {:lam, Cure.Core.Grade.unrestricted(), domain, body},
         false <- occurs?(id, solution, ctx) do
      {:ok, MetaCtx.put_solution(ctx, id, solution)}
    else
      _ -> :fallthrough
    end
  end

  defp flex_rigid_solve(_id, _argument, _rhs, _ctx, _depth), do: :fallthrough

  defp flex_or({:ok, ctx2}, _t1, _t2, _ctx, _sig, _depth), do: {:ok, ctx2}

  defp flex_or(:fallthrough, t1, t2, ctx, sig, depth) do
    case {miller_pattern(t1), miller_pattern(t2)} do
      {{id, vars}, _} -> miller_or(miller_solve(id, vars, t2, ctx, depth), t1, t2, ctx, sig, depth)
      {_, {id, vars}} -> miller_or(miller_solve(id, vars, t1, ctx, depth), t1, t2, ctx, sig, depth)
      _ -> do_unify_struct(t1, t2, ctx, sig, depth)
    end
  end

  defp contains_term?(term, target) when term == target, do: true

  defp contains_term?(term, target) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_term?(&1, target))

  defp contains_term?(term, target) when is_list(term), do: Enum.any?(term, &contains_term?(&1, target))
  defp contains_term?(_term, _target), do: false

  defp abstract_exact_term(term, target, depth) when term == target, do: {:var, depth}
  defp abstract_exact_term({:var, i}, _target, depth) when i >= depth, do: {:var, i + 1}
  defp abstract_exact_term({:var, _} = variable, _target, _depth), do: variable

  defp abstract_exact_term({:pi, grade, domain, codomain}, target, depth),
    do: {:pi, grade, abstract_exact_term(domain, target, depth), abstract_exact_term(codomain, target, depth + 1)}

  defp abstract_exact_term({:lam, grade, domain, body}, target, depth),
    do: {:lam, grade, abstract_exact_term(domain, target, depth), abstract_exact_term(body, target, depth + 1)}

  defp abstract_exact_term({:let, grade, type, value, body}, target, depth),
    do:
      {:let, grade, abstract_exact_term(type, target, depth), abstract_exact_term(value, target, depth),
       abstract_exact_term(body, target, depth + 1)}

  defp abstract_exact_term({:app, function, argument}, target, depth),
    do: {:app, abstract_exact_term(function, target, depth), abstract_exact_term(argument, target, depth)}

  defp abstract_exact_term({:data, name, parameters, indices}, target, depth),
    do:
      {:data, name, Enum.map(parameters, &abstract_exact_term(&1, target, depth)),
       Enum.map(indices, &abstract_exact_term(&1, target, depth))}

  defp abstract_exact_term({:ctor, name, arguments}, target, depth),
    do: {:ctor, name, Enum.map(arguments, &abstract_exact_term(&1, target, depth))}

  defp abstract_exact_term({:case, scrutinee, motive, branches}, target, depth) do
    {:case, abstract_exact_term(scrutinee, target, depth), abstract_exact_term(motive, target, depth),
     Enum.map(branches, fn {constructor, arity, body} ->
       {constructor, arity, abstract_exact_term(body, target, depth + arity)}
     end)}
  end

  defp abstract_exact_term({:effect_type, type}, target, depth),
    do: {:effect_type, abstract_exact_term(type, target, depth)}

  defp abstract_exact_term({:effect_pure, value}, target, depth),
    do: {:effect_pure, abstract_exact_term(value, target, depth)}

  defp abstract_exact_term({:effect_bind, effect, continuation}, target, depth),
    do: {:effect_bind, abstract_exact_term(effect, target, depth), abstract_exact_term(continuation, target, depth)}

  defp abstract_exact_term(leaf, _target, _depth), do: leaf

  defp miller_or({:ok, ctx2}, _t1, _t2, _ctx, _sig, _depth), do: {:ok, ctx2}
  defp miller_or(:fallthrough, t1, t2, ctx, sig, depth), do: do_unify_struct(t1, t2, ctx, sig, depth)

  # A spine `?id a_1 … a_n` (n ≥ 1) where every `a_k` is a variable →
  # `{id, [a_1, …, a_n]}` (application order); `nil` otherwise.
  defp miller_pattern(t), do: mpat(t, [])
  defp mpat({:app, f, {:var, i}}, acc), do: mpat(f, [i | acc])
  defp mpat({:app, _f, _x}, _acc), do: nil
  defp mpat({:meta, id}, acc) when acc != [], do: {id, acc}
  defp mpat(_t, _acc), do: nil

  # Solve `?id x̄ := λx̄. abstract(rhs)`. `:fallthrough` when the pattern side
  # conditions are unmet (non-distinct vars, a var that is not a crossed binder,
  # unknown/insufficient metavariable type, a non-pattern free var in `rhs`, or an
  # occurs-check failure) — the caller then uses the first-order rules.
  defp miller_solve(id, vars, rhs, ctx, depth) do
    n = length(vars)

    with true <- vars_ok?(vars, depth),
         mtype when not is_nil(mtype) <- MetaCtx.meta_type(ctx, id),
         {:ok, doms} <- peel_pi_domains(mtype, n),
         {:ok, body} <- miller_abstract(rhs, depth, vars, n),
         false <- occurs?(id, body, ctx) do
      {:ok, MetaCtx.put_solution(ctx, id, wrap_lams(doms, body))}
    else
      _ -> :fallthrough
    end
  end

  # Pattern args must be DISTINCT and each a variable crossed by one of the
  # `depth` binders (so it can be abstracted into a lambda of the solution).
  defp vars_ok?(vars, depth),
    do: Enum.all?(vars, &(&1 >= 0 and &1 < depth)) and length(Enum.uniq(vars)) == length(vars)

  defp peel_pi_domains(_type, 0), do: {:ok, []}

  defp peel_pi_domains({:pi, _g, d, c}, n) when n > 0 do
    with {:ok, rest} <- peel_pi_domains(c, n - 1), do: {:ok, [d | rest]}
  end

  defp peel_pi_domains(_type, _n), do: :error

  defp wrap_lams([], body), do: body
  defp wrap_lams([d | ds], body), do: {:lam, Cure.Core.Grade.unrestricted(), d, wrap_lams(ds, body)}

  # Abstract `rhs` (at binder `depth`) over the pattern vars: a pattern var `x_k`
  # becomes the k-th solution-lambda binder; an ambient var is shifted up by `n`
  # (removing the `depth` crossed binders, adding `n` lambdas); a crossed binder
  # that is NOT a pattern var escapes (no pattern solution). `local` tracks
  # binders internal to `rhs`.
  defp miller_abstract(rhs, depth, vars, n) do
    {:ok, mabs(rhs, depth, vars, n, 0)}
  catch
    :throw, :miller_escape -> :error
  end

  defp mabs({:var, v}, depth, vars, n, local) do
    cond do
      v < local ->
        {:var, v}

      v - local >= depth ->
        {:var, n + v - depth}

      true ->
        case Enum.find_index(vars, &(&1 == v - local)) do
          nil -> throw(:miller_escape)
          k0 -> {:var, local + n - 1 - k0}
        end
    end
  end

  defp mabs({:pi, g, d, c}, dep, vs, n, l), do: {:pi, g, mabs(d, dep, vs, n, l), mabs(c, dep, vs, n, l + 1)}
  defp mabs({:lam, g, d, b}, dep, vs, n, l), do: {:lam, g, mabs(d, dep, vs, n, l), mabs(b, dep, vs, n, l + 1)}
  defp mabs({:app, f, x}, dep, vs, n, l), do: {:app, mabs(f, dep, vs, n, l), mabs(x, dep, vs, n, l)}

  defp mabs({:data, nm, ps, is}, dep, vs, n, l),
    do: {:data, nm, Enum.map(ps, &mabs(&1, dep, vs, n, l)), Enum.map(is, &mabs(&1, dep, vs, n, l))}

  defp mabs({:ctor, c, args}, dep, vs, n, l), do: {:ctor, c, Enum.map(args, &mabs(&1, dep, vs, n, l))}

  defp mabs({:case, s, m, brs}, dep, vs, n, l) do
    {:case, mabs(s, dep, vs, n, l), mabs(m, dep, vs, n, l),
     Enum.map(brs, fn {cn, ar, b} -> {cn, ar, mabs(b, dep, vs, n, l + ar)} end)}
  end

  defp mabs({:let, g, ty, value, body}, dep, vs, n, l),
    do: {:let, g, mabs(ty, dep, vs, n, l), mabs(value, dep, vs, n, l), mabs(body, dep, vs, n, l + 1)}

  defp mabs({:effect_type, inner}, dep, vs, n, l), do: {:effect_type, mabs(inner, dep, vs, n, l)}
  defp mabs({:effect_pure, value}, dep, vs, n, l), do: {:effect_pure, mabs(value, dep, vs, n, l)}

  defp mabs({:effect_bind, effect, continuation}, dep, vs, n, l),
    do: {:effect_bind, mabs(effect, dep, vs, n, l), mabs(continuation, dep, vs, n, l)}

  defp mabs({:meta, _} = m, _dep, _vs, _n, _l), do: m
  defp mabs(leaf, _dep, _vs, _n, _l), do: leaf

  defp do_unify_struct({:meta, id}, {:meta, id}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify_struct({:meta, id}, t, ctx, _sig, depth), do: solve(id, t, ctx, depth)
  defp do_unify_struct(t, {:meta, id}, ctx, _sig, depth), do: solve(id, t, ctx, depth)

  defp do_unify_struct({:type, l}, {:type, l}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify_struct({:var, i}, {:var, i}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify_struct({:global, g}, {:global, g}, ctx, _sig, _depth), do: {:ok, ctx}

  defp do_unify_struct({:data, f, ps1, is1}, {:data, f, ps2, is2}, ctx, sig, depth),
    do: unify_lists(ps1 ++ is1, ps2 ++ is2, ctx, sig, depth)

  # Effect is a type former, so expected-result solving must continue through
  # it to reach return-only implicits in an effectful operation. Without this
  # case, `Effect(RawPid(?m, ?m))` falls through to rigid conversion instead of
  # solving `?m` from a concrete `Effect(Pid(Atom))` goal.
  defp do_unify_struct({:effect_type, inner1}, {:effect_type, inner2}, ctx, sig, depth),
    do: unify_d(inner1, inner2, ctx, sig, depth)

  defp do_unify_struct({:ctor, c, a1}, {:ctor, c, a2}, ctx, sig, depth),
    do: unify_lists(a1, a2, ctx, sig, depth)

  # Two applications unify by CONGRUENCE (head-to-head, arg-to-arg) — the fast path for a
  # rigid neutral spine. But an application may also be a REDEX whose normal form matches the
  # other side even though the spines differ: a `data` index `elt(EFin x, EFin k)` vs its
  # ι-reduct `slt(x, k)`, or `mem(x, Node(l, v, r))` vs `mem(x, l)`. Congruence decomposes those
  # to a head/arg mismatch (`elt` vs `slt`, `Node(…)` vs `l`) and fails before conversion is
  # ever tried. So on a congruence failure, fall back to deciding the WHOLE applications by
  # δ/ι-convertibility (sound: `conv?` is the trusted decision, and only meta-free terms qualify).
  defp do_unify_struct({:app, f1, x1} = t1, {:app, f2, x2} = t2, ctx, sig, depth) do
    case with {:ok, ctx} <- unify_d(f1, f2, ctx, sig, depth), do: unify_d(x1, x2, ctx, sig, depth) do
      {:ok, _} = ok ->
        ok

      {:error, _} = err ->
        if delta_convertible?(t1, t2, ctx, sig, depth), do: {:ok, ctx}, else: err
    end
  end

  defp do_unify_struct({:pi, _g1, d1, c1}, {:pi, _g2, d2, c2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(d1, d2, ctx, sig, depth),
         do: unify_d(c1, c2, ctx, sig, depth + 1)
  end

  defp do_unify_struct({:lam, _g1, d1, b1}, {:lam, _g2, d2, b2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(d1, d2, ctx, sig, depth),
         do: unify_d(b1, b2, ctx, sig, depth + 1)
  end

  # Structurally identical (literals, atoms, etc.).
  defp do_unify_struct(t, t, ctx, _sig, _depth), do: {:ok, ctx}

  # Last resort: two terms that are not syntactically unifiable may still be
  # DEFINITIONALLY equal via δ/ι (e.g. `DDec` vs the redex `dmeet(DDec, DDec)`, or a
  # `data` INDEX like `elt(EFin x, EFin k)` vs its ι-reduct `slt(x, k)`). Only attempt
  # this when a signature is available and both sides are metavariable-free — then they
  # carry no unification variables to solve, so a convertibility check is exactly the right
  # question. The terms may be OPEN (free de Bruijn vars < `depth`, e.g. index positions
  # under the binders unification has entered); evaluating them under a neutral env of that
  # depth — precisely how the kernel checks under binders — treats those vars as rigid, so
  # `conv?` decides them soundly. `depth` is the binder depth threaded by `unify_d`.
  defp do_unify_struct(t1, t2, ctx, sig, depth) do
    if delta_convertible?(t1, t2, ctx, sig, depth) do
      {:ok, ctx}
    else
      {:error, {:cannot_unify, t1, t2}}
    end
  end

  defp delta_convertible?(_t1, _t2, _ctx, nil, _depth), do: false

  defp delta_convertible?(t1, t2, ctx, sig, depth) do
    z1 = zonk(t1, ctx)
    z2 = zonk(t2, ctx)

    meta_free?(z1) and meta_free?(z2) and
      Cure.Core.Conv.conv?(z1, z2, Cure.Core.Context.neutral_env(depth), depth, sig)
  end

  # Structurally complete: walk EVERY subterm-bearing shape so a metavariable
  # buried anywhere (`{:eq}`/`{:refl}`/
  # `{:prim}`/`{:case}`/…) is detected. A missed shape here would let a
  # `{:meta, _}`-bearing term pass the `delta_convertible?` guard and reach the
  # TRUSTED `Eval.eval`, which has no `{:meta, _}` clause — an elaborator crash of
  # the kernel. Tag atoms and ids are non-tuple/non-list leaves → `true`.
  defp meta_free?({:meta, _}), do: false
  defp meta_free?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.all?(&meta_free?/1)
  defp meta_free?(l) when is_list(l), do: Enum.all?(l, &meta_free?/1)
  defp meta_free?(_), do: true

  defp unify_lists([], [], ctx, _sig, _depth), do: {:ok, ctx}

  defp unify_lists([x | xs], [y | ys], ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(x, y, ctx, sig, depth), do: unify_lists(xs, ys, ctx, sig, depth)
  end

  defp unify_lists(l1, l2, _ctx, _sig, _depth),
    do: {:error, {:arity_mismatch, length(l1), length(l2)}}

  # Solve `?id := t`, first strengthening `t` from the current binder `depth` back
  # to the ambient frame the metavariable lives in. A free variable that points
  # *into* those `depth` local binders would escape its scope, so the solve fails
  # (not a first-order solution — a higher-order/Miller case we do not attempt).
  # At depth 0 this is the identity, so every existing (top-level) unification is
  # unchanged.
  defp solve(id, t, ctx, depth) do
    case strengthen(t, depth) do
      :escape -> {:error, {:escaping_variable, id}}
      {:ok, t2} -> solve_strengthened(id, t2, ctx)
    end
  end

  defp solve_strengthened(id, t, ctx) do
    if occurs?(id, t, ctx) do
      {:error, {:occurs_check, id, t}}
    else
      {:ok, MetaCtx.put_solution(ctx, id, t)}
    end
  end

  # Strengthen `t` by `depth`: subtract `depth` from every variable free in `t`
  # (accounting for `t`'s own binders), returning `:escape` if any free variable
  # points into the `depth` binders being removed. `depth == 0` is the identity.
  defp strengthen(t, 0), do: {:ok, t}

  defp strengthen(t, depth) do
    if escapes?(t, depth, 0), do: :escape, else: {:ok, Cure.Elab.Subst.shift(t, -depth, 0)}
  end

  # Does `t` reference (freely) any of the outermost `depth` binders? `local`
  # counts binders internal to `t`; a variable `i >= local` is free, at free index
  # `i - local`, and escapes iff that index is `< depth`.
  #
  # This walker is FAIL-CLOSED: its catch-all answers `true` (escapes). `strengthen/2`
  # reads `false` as "safe to solve this metavariable", so a `false` for a shape we
  # failed to enumerate would let a term mentioning a crossed binder be lifted out of
  # its scope. Previously a `{:case, ...}` fell into a `_other -> false` catch-all and
  # was silently declared scope-safe.
  #
  # Note a generic structural tuple-walk would NOT be a correct catch-all here, the way
  # it is for `Inductive.occurs?`: binder-introducing nodes must bump `local`, and
  # walking a branch body without bumping it *under*-estimates the free index
  # (`i - local` too large ⇒ `< depth` less often ⇒ escapes missed). So every binder is
  # enumerated explicitly, every leaf is enumerated explicitly, and anything unknown is
  # assumed to escape. Refusing to solve a metavariable is soundly incomplete; solving
  # it out of scope is not.
  defp escapes?({:var, i}, depth, local), do: i >= local and i - local < depth

  # Binders. `:case` binds `ar` fields in each branch body; the motive is already a
  # lambda, so it is walked at `local` (mirrors `Subst.shift`'s `:case` clause).
  defp escapes?({:pi, _g, d, c}, depth, local), do: escapes?(d, depth, local) or escapes?(c, depth, local + 1)
  defp escapes?({:lam, _g, d, b}, depth, local), do: escapes?(d, depth, local) or escapes?(b, depth, local + 1)

  defp escapes?({:case, s, m, brs}, depth, local) do
    escapes?(s, depth, local) or escapes?(m, depth, local) or
      Enum.any?(brs, fn {_c, ar, b} -> escapes?(b, depth, local + ar) end)
  end

  # Non-binding compound nodes.
  defp escapes?({:app, f, x}, depth, local), do: escapes?(f, depth, local) or escapes?(x, depth, local)

  defp escapes?({:data, _f, ps, is}, depth, local),
    do: Enum.any?(ps ++ is, &escapes?(&1, depth, local))

  defp escapes?({:ctor, _c, args}, depth, local), do: Enum.any?(args, &escapes?(&1, depth, local))

  # Leaves. A `{:meta, _}` binds nothing and its own scope is checked when it is
  # solved (`occurs?`/`strengthen` run again there).
  defp escapes?({:meta, _}, _depth, _local), do: false
  defp escapes?({:type, _}, _depth, _local), do: false
  defp escapes?({:global, _}, _depth, _local), do: false
  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:int_type}`
  # node; fresh elaboration never produces one (spec 2026-07-18 §3a).
  defp escapes?({:int_type}, _depth, _local), do: false
  defp escapes?({:int_lit, _}, _depth, _local), do: false
  defp escapes?({:nat_lit, _}, _depth, _local), do: false
  defp escapes?({:bounded_lit, _}, _depth, _local), do: false
  defp escapes?({:float_type}, _depth, _local), do: false
  defp escapes?({:float_lit, _}, _depth, _local), do: false
  defp escapes?({:binary_type}, _depth, _local), do: false

  defp escapes?(_unknown, _depth, _local), do: true

  # Does metavariable `id` occur in `t` (following solutions)? Structurally
  # complete (generic tuple/list walk) so an occurrence buried in ANY shape is
  # caught — an under-approximation would admit a cyclic solution.
  defp occurs?(id, t, ctx) do
    case force(t, ctx) do
      {:meta, ^id} -> true
      {:meta, _other} -> false
      tup when is_tuple(tup) -> tup |> Tuple.to_list() |> Enum.any?(&occurs?(id, &1, ctx))
      lst when is_list(lst) -> Enum.any?(lst, &occurs?(id, &1, ctx))
      _ -> false
    end
  end

  @doc """
  True iff `t` still contains a metavariable syntactically. Use at a kernel
  boundary (after `zonk`) to reject cleanly rather than hand a `{:meta, _}`-bearing
  term to the trusted evaluator, which has no `{:meta, _}` clause and would crash.
  """
  @spec has_meta?(uterm()) :: boolean()
  def has_meta?(t), do: not meta_free?(t)

  @doc """
  Finalise a term by substituting every metavariable solution away. Structurally
  complete (generic tuple/list walk) so a solution buried in ANY shape is
  substituted — a missed shape would leave a `{:meta, _}` in a term handed to the
  kernel.
  """
  @spec zonk(uterm(), MetaCtx.t()) :: uterm()
  def zonk({:meta, id} = meta, ctx) do
    case MetaCtx.solution(ctx, id) do
      nil -> meta
      solution -> zonk(solution, ctx)
    end
  end

  # Core's known node grammar gets shape-directed clauses so zonking visits only
  # actual subterms. The generic tuple/list clauses below remain the completeness
  # firewall for elaborator-only and future nodes (Eq/Refl were historically the
  # reason this operation must never use an opaque catch-all).
  def zonk({:pi, grade, domain, codomain}, ctx),
    do: {:pi, grade, zonk(domain, ctx), zonk(codomain, ctx)}

  def zonk({:lam, grade, domain, body}, ctx),
    do: {:lam, grade, zonk(domain, ctx), zonk(body, ctx)}

  def zonk({:let, grade, type, value, body}, ctx),
    do: {:let, grade, zonk(type, ctx), zonk(value, ctx), zonk(body, ctx)}

  def zonk({:app, function, argument}, ctx),
    do: {:app, zonk(function, ctx), zonk(argument, ctx)}

  def zonk({:data, name, parameters, indices}, ctx),
    do: {:data, name, Enum.map(parameters, &zonk(&1, ctx)), Enum.map(indices, &zonk(&1, ctx))}

  def zonk({:ctor, name, arguments}, ctx),
    do: {:ctor, name, Enum.map(arguments, &zonk(&1, ctx))}

  def zonk({:case, scrutinee, motive, branches}, ctx) do
    {:case, zonk(scrutinee, ctx), zonk(motive, ctx),
     Enum.map(branches, fn {constructor, arity, body} ->
       {constructor, arity, zonk(body, ctx)}
     end)}
  end

  def zonk({:effect_type, type}, ctx), do: {:effect_type, zonk(type, ctx)}
  def zonk({:effect_pure, value}, ctx), do: {:effect_pure, zonk(value, ctx)}

  def zonk({:effect_bind, effect, continuation}, ctx),
    do: {:effect_bind, zonk(effect, ctx), zonk(continuation, ctx)}

  def zonk({tag} = leaf, _ctx)
      when tag in [:int_type, :float_type, :binary_type, :atom_type, :absurd],
      do: leaf

  def zonk({tag, _payload} = leaf, _ctx)
      when tag in [
             :type,
             :var,
             :global,
             :int_lit,
             :nat_lit,
             :bounded_lit,
             :float_lit,
             :atom_lit,
             :hole
           ],
      do: leaf

  def zonk(tup, ctx) when is_tuple(tup),
    do: tup |> Tuple.to_list() |> Enum.map(&zonk(&1, ctx)) |> List.to_tuple()

  def zonk(list, ctx) when is_list(list), do: Enum.map(list, &zonk(&1, ctx))
  def zonk(other, _ctx), do: other

  @meta_placeholder_prefix "$meta$"

  @doc false
  # Meta-aware weak-head normalisation (ledger #11, whnf-before-compare). Reduce
  # `term` to whnf while treating each unsolved metavariable as an opaque neutral:
  # it BLOCKS a match/case whose scrutinee is the metavariable (`plus(?m, Z)` stays
  # stuck) but PASSES THROUGH any non-scrutinee position (`plus(Z, ?m)` reduces to
  # `?m`). Mechanism: zonk, substitute each remaining `{:meta, id}` with a reserved
  # opaque global `{:global, :"$meta$id"}` (no signature entry → `unfold_head`
  # returns `:stuck`, exactly like an unsolved metavariable), reduce with the
  # TRUSTED `Normalise` reduction reused via its constituents (`Eval.eval` →
  # `Normalise.whnf_value` → `Quote.reify`, the trio `Normalise.whnf/3` itself
  # composes — bypassing `whnf/3`'s `Core.Context.t()` requirement), then map the
  # placeholders back. E-layer only: the kernel re-checks the assembled term, so a
  # wrong reduction is caught downstream. On `:fuel_exhausted` (or `sig == nil`),
  # returns the (zonked) input unchanged — strictly additive, never crashes.
  @spec whnf_meta_aware(uterm(), MetaCtx.t(), Cure.Core.Env.t() | nil, non_neg_integer(), keyword()) ::
          uterm()
  def whnf_meta_aware(term, ctx, sig, depth \\ 0, opts \\ [])

  def whnf_meta_aware(term, ctx, nil, _depth, _opts), do: zonk(term, ctx)

  def whnf_meta_aware(term, ctx, sig, depth, opts) do
    z = zonk(term, ctx)
    subst = metas_to_placeholders(z)
    fuel = Keyword.get(opts, :fuel, :infinity)

    # Only reduce a CLOSED term. `unify_d`'s `depth` counts binders crossed *within*
    # the unification, but the terms may still carry FREE de Bruijn variables from
    # the ambient elaboration context (function parameters). Evaluating those under
    # the empty env would mis-level them into out-of-range `{:var, _}` (negative
    # indices). A closed term is context-independent, so `env = []` / read-back at
    # `depth` is sound; the computed-index unifications this feature targets
    # (`plus(Z, ?m) =? S(Z)`) are closed once metavariables become placeholders.
    if Cure.Core.Term.closed?(subst) do
      reduce_closed(z, subst, sig, depth, fuel)
    else
      z
    end
  end

  defp reduce_closed(z, subst, sig, depth, fuel) do
    reduced =
      Cure.Core.Normalise.with_fuel(fuel, fn ->
        env = for level <- (depth - 1)..0//-1, do: {:vneutral, {:nvar, level}}

        subst
        |> Cure.Core.Eval.eval(env)
        |> Cure.Core.Normalise.whnf_value(sig, delta: :certified, stuck_cases: :preserve)
        # Pass `sig` so an indexed-family value (`{:vdata, :Equivalent, params ++ indices}`)
        # reifies back to the correctly-split `{:data, :Equivalent, params, indices}` rather
        # than the flat `{:data, :Equivalent, all, []}`. Without it, a codomain metavariable
        # solved through this whnf (`?P := λn. Equivalent(Nat,n,n)`, ledger #10) stores a
        # flat body, and the later `P(Zero)` check trips `check_spine`'s `:arg_arity`.
        |> Cure.Core.Quote.reify(depth, sig)
      end)

    case reduced do
      :fuel_exhausted -> z
      other -> placeholders_to_metas(other)
    end
  end

  # Replace each unsolved `{:meta, id}` with its reserved opaque-global placeholder.
  # Generic tuple/list walk (mirrors `zonk/2`) so a metavariable buried in ANY Core
  # shape is substituted.
  defp metas_to_placeholders({:meta, id}), do: {:global, :"#{@meta_placeholder_prefix}#{id}"}

  defp metas_to_placeholders(tup) when is_tuple(tup),
    do: tup |> Tuple.to_list() |> Enum.map(&metas_to_placeholders/1) |> List.to_tuple()

  defp metas_to_placeholders(list) when is_list(list),
    do: Enum.map(list, &metas_to_placeholders/1)

  defp metas_to_placeholders(leaf), do: leaf

  # Inverse of `metas_to_placeholders/1`: map each placeholder global back to its
  # metavariable. A `{:global, :"$meta$…"}` cannot arise from real source (the
  # prefix is not a legal identifier), so this is unambiguous.
  defp placeholders_to_metas({:global, name} = t) do
    case placeholder_id(name) do
      {:ok, id} -> {:meta, id}
      :error -> t
    end
  end

  defp placeholders_to_metas(tup) when is_tuple(tup),
    do: tup |> Tuple.to_list() |> Enum.map(&placeholders_to_metas/1) |> List.to_tuple()

  defp placeholders_to_metas(list) when is_list(list),
    do: Enum.map(list, &placeholders_to_metas/1)

  defp placeholders_to_metas(leaf), do: leaf

  defp placeholder_id(name) when is_atom(name) do
    case Atom.to_string(name) do
      @meta_placeholder_prefix <> rest ->
        case Integer.parse(rest) do
          {id, ""} -> {:ok, id}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  defp placeholder_id(_), do: :error
end
