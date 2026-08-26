defmodule Cure.Elab.ProofSearch do
  @moduledoc """
  Auto proof-search over `@lemma`-tagged theorems and local hypotheses
  (design: docs/superpowers/specs/2026-07-18-auto-lemma-proof-search-design.md).

  Untrusted: only *builds* Core proof terms; every candidate is re-checked by
  the kernel (`Cure.Core.Kernel.check/3`), so search can never make an
  ill-typed program type-check.
  """
  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.{MetaCtx, Unify, Subst}

  @type goal :: term()
  @type result :: {:ok, term()} | :none | {:error, {:ambiguous_proof_search, term(), [term()]}}

  # Search terminates on two conditions: a recursion-depth ceiling and a
  # per-branch "already trying this goal" cycle stack.
  @depth_limit 5

  @spec resolve(goal(), Context.t(), Cure.Core.Env.t()) :: result()
  def resolve(goal, ctx, env), do: resolve(goal, ctx, env, %{depth: 0, trying: []})

  # Depth-bound guard: abandon a branch that has descended past the ceiling.
  def resolve(_goal, _ctx, _env, %{depth: d}) when d > @depth_limit, do: :none

  # Cycle guard: if this goal is already being attempted higher on the branch,
  # abandon it (a self-referential lemma set would otherwise loop forever).
  def resolve(goal, ctx, env, %{trying: ts} = state) do
    # Weak-head-normalise the goal first. A goal threaded in from checked-mode
    # elaboration is often an unreduced β-redex — the dependent codomain motive
    # applied to the argument, e.g. `(λn:Nat. IsPositive(n)) (multiply …)` —
    # whose head is a `{:lam, …}`, not the family. `head_of/1` (and conclusion
    # unification) need the reduced `{:data, IsPositive, …, [multiply …]}` form,
    # or no lemma filed under `IsPositive` is ever tried. whnf (not nf) is used
    # deliberately: it β-reduces the outer redex to expose the family head while
    # leaving the index spine (`multiply (refined_value …) …`) unfolded-free, so
    # the implicit arguments unification recovers from the goal stay in their
    # surface form — δ-unfolding them (as full nf would) makes the assembled term
    # differ syntactically from the hand-written proof it must equal.
    goal = Cure.Core.Normalise.whnf(ctx, goal)

    if Enum.any?(ts, &same_goal?(&1, goal, ctx, env)) do
      :none
    else
      # Now working on `goal`: push it onto the cycle stack so any sub-goal that
      # reduces back to it (a self-referential lemma set) is cut here, not below.
      state = %{state | trying: [goal | ts]}

      # Ordered solver seam (design §4.2). Each solver is a disjoint strategy;
      # `run_solvers` consults them in order and the first NON-`:none` verdict
      # wins — an `{:ok, term}` discharge OR an `{:error, …}` ambiguity, which
      # must surface rather than be masked by a later solver that happens to
      # find something. Only a `:none` (this strategy does not apply) falls
      # through to the next. `solver_lemma` (local hypotheses + refinement
      # projections + `@lemma`-tagged theorems) runs first; `solver_positivity`
      # (the syntax-directed arithmetic-sign procedure over the stdlib's
      # untagged sign lemmas) is the fallback.
      run_solvers(
        [
          fn -> solver_lemma(goal, ctx, env, state) end,
          fn -> solver_positivity(goal, ctx, env, state) end
        ],
        goal
      )
    end
  end

  # Consult solvers in order; first non-`:none` verdict wins. See `resolve/4`.
  defp run_solvers([], _goal), do: :none

  defp run_solvers([solver | rest], goal) do
    case solver.() do
      :none -> run_solvers(rest, goal)
      verdict -> verdict
    end
  end

  # The v1 solver: pool local-context hypotheses, refinement/Sigma projections,
  # and `@lemma`-tagged theorems filed under the goal's head, then apply the
  # unique-or-defer discipline (`decide/2`).
  defp solver_lemma(goal, ctx, env, state) do
    {lemma_ok, lemma_errors} = lemma_candidates(goal, ctx, env, state)

    candidates =
      local_candidates(goal, ctx, env) ++
        projection_candidates(goal, ctx, env) ++
        conjunction_candidates(goal, ctx, env) ++
        lemma_ok

    # An ambiguous SUB-goal (e.g. a lemma's own hypothesis matches two local
    # witnesses) means that particular lemma-application path itself yields
    # more than one distinct proof term — a genuine ambiguity, not "this
    # lemma doesn't apply". If some OTHER candidate independently and
    # unambiguously proves the goal, prefer it (the ambiguous branch was
    # simply unneeded). Only surface the inner ambiguity when it is the
    # only path this goal has, so it is never silently downgraded to :none.
    case decide(candidates, goal) do
      :none ->
        case lemma_errors do
          [] -> :none
          [first | _] -> first
        end

      other ->
        other
    end
  end

  # The syntax-directed arithmetic-sign procedure (design §4.2, a Lean-`positivity`
  # style decision procedure). The stdlib's `Std.Proof.Math` ships the sign lemmas
  # for the successor and addition fragments WITHOUT `@lemma`, so the tagged-lemma
  # solver never reaches them. This solver applies them by name through the same
  # `try_lemma` machinery, using VIRTUAL lemma entries built from the stdlib defs.
  #
  # Order matters for the two overlapping addition lemmas: both conclude
  # `IsPositive(plus(a, b))`, so when both summands are provably positive both
  # apply. Pooling them (as `decide/2` would) is a false `:ambiguous_proof_search`.
  # Here we try the curated lemmas in a fixed order and take the FIRST that
  # discharges — a deterministic choice, not an ambiguity. `multiply` is
  # intentionally absent: its lemma IS `@lemma`-tagged in the stdlib, so the
  # primary solver already discharges `IsPositive(multiply(a, b))` and this
  # fallback never sees it.
  @positivity_lemmas [
    "successor_is_positive",
    "adding_a_positive_number_is_positive",
    "adding_to_a_positive_number_is_positive"
  ]

  defp solver_positivity(goal, ctx, env, state) do
    case head_of(goal) do
      nil ->
        :none

      _head ->
        @positivity_lemmas
        |> Enum.map(&virtual_lemma_entry(env, &1))
        |> Enum.reject(&is_nil/1)
        |> Enum.reduce_while(:none, fn entry, _acc ->
          case try_lemma(entry, goal, ctx, env, state) do
            # A genuine ambiguity in a recursive sub-goal must surface, not be
            # papered over by trying the next sign lemma.
            {:error, _} = err ->
              {:halt, err}

            # This lemma discharged the goal — the first to do so wins.
            {term, _prov} when term != nil ->
              {:halt, {:ok, term}}

            # This lemma does not apply (head mismatch, or an unprovable
            # hypothesis): try the next one in the curated order.
            _ ->
              {:cont, :none}
          end
        end)
    end
  end

  # A lemma entry `%{name, type}` (the shape `try_lemma/5` consumes) synthesised
  # from an ordinary — untagged — stdlib def looked up by name. `name` is the
  # resolved global key so the assembled `{:global, name}` application refers to
  # the same def the kernel will check against. Returns nil when the def is not
  # in scope (e.g. `Std.Proof.Math` not `use`d), so the solver simply skips it.
  defp virtual_lemma_entry(env, name) do
    case Cure.Core.Env.get_def(env, name) do
      %{type: pi} -> %{name: Cure.Core.Env.resolve_key(env, env.defs, name), type: pi}
      _ -> nil
    end
  end

  # Each candidate is {term, provenance}. Keep only the kernel-checked survivors,
  # then collapse candidates that produce the SAME Core term to one (design §6:
  # "require the survivors to collapse to a single survivor"). Two structurally
  # identical proof terms are one proof, not an ambiguity — this is what a
  # diamond import produces, where the same `@lemma` reaches the goal by more
  # than one `use` path (e.g. `use Std.Proof.Math` directly and transitively via
  # `use Std.Refine`), so the same lemma entry is filed twice under the goal head
  # and yields two byte-identical applications. Only *distinct* proof terms
  # constitute a genuine ambiguity.
  defp decide(candidates, goal) do
    survivors =
      candidates
      |> Enum.filter(fn {term, _prov} -> term != nil end)
      |> Enum.uniq_by(fn {term, _prov} -> term end)

    case survivors do
      [] -> :none
      [{term, _}] -> {:ok, term}
      many -> {:error, {:ambiguous_proof_search, goal, Enum.map(many, &elem(&1, 1))}}
    end
  end

  # Local-context search: every binder whose type checks against the goal.
  defp local_candidates(goal, ctx, _env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    if len > 0 do
      for k <- 0..(len - 1)//1 do
        term = {:var, k}

        case Kernel.check(ctx, term, goal_val) do
          :ok -> {term, {:local, k}}
          _ -> {nil, {:local, k}}
        end
      end
      |> Enum.filter(fn {term, _} -> term != nil end)
    else
      []
    end
  end

  # Refinement/Sigma second-projection search: for every local binder whose type
  # WHNFs to the Sigma family, the binder's `.2` projection proves the predicate
  # about its first component. Its type `P(sigma_first(binder))` is checked
  # against the goal by the kernel.
  defp projection_candidates(goal, ctx, env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1, len > 0 do
      case sigma_params(Context.lookup(ctx, k), ctx, env) do
        {:ok, a_value, predicate_value} ->
          term = sigma_second_of({:var, k}, a_value, predicate_value, ctx, env)

          case Kernel.check(ctx, term, goal_val) do
            :ok -> {term, {:projection, k}}
            _ -> {nil, {:projection, k}}
          end

        :error ->
          {nil, {:projection, k}}
      end
    end
    |> Enum.filter(fn {term, _} -> term != nil end)
  end

  # If a Value WHNFs to the Sigma family, return its two params
  # `{:ok, a_value, predicate_value}`; else `:error`. Sigma has exactly two
  # params (`a: Type`, `b: (a) -> Type`) and zero indices.
  defp sigma_params(nil, _ctx, _env), do: :error

  defp sigma_params(type_value, ctx, env) do
    case Cure.Core.Inductive.builtin(env, :sigma) do
      nil ->
        :error

      sigma_fam ->
        case Cure.Core.Normalise.whnf_value(type_value, Context.signature(ctx)) do
          {:vdata, ^sigma_fam, [a_value, predicate_value]} -> {:ok, a_value, predicate_value}
          _ -> :error
        end
    end
  end

  # The second projection of a refinement/Sigma binder, applied with its implicit
  # `{a}`/`{predicate}` arguments reified DIRECTLY from the Sigma family's own
  # params (not fresh metavars: those never reach the kernel; sigma_params/3
  # already pinned down `a_value`/`predicate_value` from the binder's own type).
  # The assembled term is meta-free before it reaches Kernel.check.
  #
  # The head is `Std.Refine.refinement_proof` — the idiomatic accessor a human
  # writes for the proof carried by a refinement (design §5:
  # `refinement_proof(left) : IsPositive(refined_value(left))`), so the auto-found
  # term is syntactically the hand-written one, not a δ-convertible variant. When
  # `Std.Refine` is not loaded (a plain `Std.Sigma` binder with no refinement API
  # in scope) we fall back to the kernel builtin `sigma_second`, which is
  # definitionally the same second projection — refinement_proof's own body — so
  # generic-Sigma projection still works without depending on Std.Refine.
  defp sigma_second_of(var_term, a_value, predicate_value, ctx, env) do
    depth = Context.length(ctx)
    sig = Context.signature(ctx)
    a_term = Cure.Core.Quote.reify(a_value, depth, sig)
    predicate_term = Cure.Core.Quote.reify(predicate_value, depth, sig)
    build_app({:global, second_projection_head(env)}, [a_term, predicate_term, var_term])
  end

  # The global to head the second projection with: `Std.Refine.refinement_proof`
  # when the refinement API is in scope, else the kernel builtin `sigma_second`.
  defp second_projection_head(env) do
    case Cure.Core.Env.get_def(env, "refinement_proof") do
      nil -> :sigma_second
      _def -> Cure.Core.Env.resolve_key(env, env.defs, "refinement_proof")
    end
  end

  # Conjunction-elimination search: for every local binder whose type WHNFs to
  # `IsTrue(and(left, right))`, both operands' truths follow — the left via
  # `left_operand_is_true_from_true_conjunction`, the right via its counterpart.
  # Each projection is assembled with the operands reified from the binder's own
  # type (meta-free, like the Sigma second projection) and kernel-checked against
  # the goal, so an `IsTrue(left)` or `IsTrue(right)` obligation is discharged
  # from a conjunctive hypothesis without the author naming the lemma. Only the
  # projection whose conclusion matches the goal survives the kernel check.
  defp conjunction_candidates(goal, ctx, env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1,
        len > 0,
        {left_term, right_term} <- is_true_and_binder(Context.lookup(ctx, k), ctx, env),
        {global, prov} <- [
          {and_left_projection_head(env), {:conjunction_left, k}},
          {and_right_projection_head(env), {:conjunction_right, k}}
        ],
        global != nil do
      term = build_app({:global, global}, [left_term, right_term, {:var, k}])

      case Kernel.check(ctx, term, goal_val) do
        :ok -> {term, prov}
        _ -> {nil, prov}
      end
    end
    |> Enum.filter(fn {term, _} -> term != nil end)
  end

  # If a Value WHNFs to `IsTrue(and(left, right))`, return `[{left, right}]` with
  # both operands reified to Core terms; else `[]` (so the comprehension skips
  # this binder). `IsTrue` has zero params and one index — the reflected claim —
  # which must itself be the two-argument `and`-application spine. The operands
  # are reified at the current context depth, so they can head the projection
  # application in the same scope as the binder `{:var, k}`.
  defp is_true_and_binder(nil, _ctx, _env), do: []

  defp is_true_and_binder(type_value, ctx, env) do
    is_true_key = is_true_family(env)
    and_key = boolean_and_head(env)

    with true <- is_true_key != nil and and_key != nil,
         depth = Context.length(ctx),
         sig = Context.signature(ctx),
         core = Cure.Core.Quote.reify(type_value, depth, sig),
         {:data, ^is_true_key, _params, [claim]} <- Cure.Core.Normalise.whnf(ctx, core),
         {:app, {:app, {:global, ^and_key}, left_term}, right_term} <- claim do
      [{left_term, right_term}]
    else
      _ -> []
    end
  end

  # The resolved `Std.Proof.IntMath#IsTrue` family key, or nil when the reflection
  # family is not in scope (so conjunction elimination stays inert).
  defp is_true_family(env) do
    case Cure.Core.Inductive.get_family(env, :IsTrue) do
      nil -> nil
      _fam -> Cure.Core.Env.resolve_key(env, env.families, :IsTrue)
    end
  end

  # The resolved `Std.Bool#and` def key, or nil when `Std.Bool` is not in scope.
  defp boolean_and_head(env) do
    case Cure.Core.Env.get_def(env, "and") do
      nil -> nil
      _def -> Cure.Core.Env.resolve_key(env, env.defs, "and")
    end
  end

  # The global heading the left-operand projection, or nil when
  # `Std.Proof.BooleanReflection` is not in scope (so the candidate is dropped by
  # the `global != nil` guard). Mirrors `second_projection_head/1`.
  defp and_left_projection_head(env) do
    case Cure.Core.Env.get_def(env, "left_operand_is_true_from_true_conjunction") do
      nil -> nil
      _def -> Cure.Core.Env.resolve_key(env, env.defs, "left_operand_is_true_from_true_conjunction")
    end
  end

  # The global heading the right-operand projection, or nil when the module is not
  # in scope. Mirrors `second_projection_head/1`.
  defp and_right_projection_head(env) do
    case Cure.Core.Env.get_def(env, "right_operand_is_true_from_true_conjunction") do
      nil -> nil
      _def -> Cure.Core.Env.resolve_key(env, env.defs, "right_operand_is_true_from_true_conjunction")
    end
  end

  # Lemma-application search: every registered lemma under the goal's head whose
  # conclusion unifies with the goal, with any explicit-hypothesis sub-goals
  # resolved recursively, assembled into a curried application and kernel-checked.
  # Returns `{candidates, errors}`: `candidates` are the usual `{term,
  # provenance}` pairs from lemma attempts that produced a kernel-checked
  # term; `errors` collects any `{:error, {:ambiguous_proof_search, ...}}`
  # raised by a lemma's own (recursive) hypothesis resolution, kept separate
  # so the caller can prefer an unambiguous candidate when one exists and
  # only surface the inner ambiguity as a last resort.
  defp lemma_candidates(goal, ctx, env, state) do
    case head_of(goal) do
      nil ->
        {[], []}

      head ->
        results =
          env
          |> Cure.Core.Env.lemmas(head)
          |> Enum.map(&try_lemma(&1, goal, ctx, env, state))

        candidates =
          Enum.flat_map(results, fn
            {:error, _} -> []
            {nil, _prov} -> []
            {_term, _prov} = c -> [c]
          end)

        errors =
          Enum.flat_map(results, fn
            {:error, _} = e -> [e]
            _ -> []
          end)

        {candidates, errors}
    end
  end

  defp head_of({:data, name, _p, _i}), do: name
  defp head_of(_), do: nil

  # Instantiate the lemma's Pi telescope with metavars, unify the conclusion
  # with the goal, resolve unsolved (explicit-hypothesis) binders as sub-goals,
  # assemble the application, and kernel-check it.
  defp try_lemma(%{name: name, type: pi}, goal, ctx, env, state) do
    mctx = MetaCtx.new()
    {arg_metas, conclusion, mctx} = instantiate_telescope(pi, mctx)

    with {:ok, mctx} <- Unify.unify(conclusion, goal, mctx, env),
         {:ok, args} <- fill_args(arg_metas, ctx, env, mctx, state) do
      term = build_app({:global, name}, args)
      goal_val = Eval.eval(goal, Context.env(ctx))

      case Kernel.check(ctx, term, goal_val) do
        :ok -> {term, {:lemma, name}}
        _ -> {nil, {:lemma, name}}
      end
    else
      # Only an ambiguity PROPAGATED UP from a recursive sub-goal (fill_args)
      # is a genuine error to surface. Unify.unify/4's own failure shapes
      # (:cannot_unify, :arity_mismatch, :escaping_variable, :occurs_check) mean
      # this lemma's conclusion simply does not match the goal — the routine,
      # expected outcome for most registered lemmas under a shared head — and
      # must stay a silent decline, not be conflated with an ambiguity error.
      {:error, {:ambiguous_proof_search, _, _}} = err -> err
      _ -> {nil, {:lemma, name}}
    end
  end

  # Peel every {:pi,g,dom,cod}; for each binder mint a fresh metavar and
  # instantiate it into cod. Returns {arg-metas-with-domains, conclusion, mctx}.
  defp instantiate_telescope(pi, mctx), do: instantiate_telescope(pi, mctx, [])

  defp instantiate_telescope({:pi, _g, dom, cod}, mctx, acc) do
    {mctx, id} = MetaCtx.fresh(mctx, nil)
    meta = {:meta, id}
    cod2 = Subst.instantiate(cod, [meta])
    instantiate_telescope(cod2, mctx, [{meta, dom} | acc])
  end

  defp instantiate_telescope(conclusion, mctx, acc),
    do: {Enum.reverse(acc), conclusion, mctx}

  # For each telescope slot: if its metavar is solved by conclusion-unification,
  # use the solution; otherwise treat the (zonked) domain as a sub-goal and recurse.
  defp fill_args(arg_metas, ctx, env, mctx, state) do
    Enum.reduce_while(arg_metas, {:ok, []}, fn {meta, dom}, {:ok, acc} ->
      z = Unify.zonk(meta, mctx)

      if solved?(z) do
        {:cont, {:ok, acc ++ [z]}}
      else
        subgoal = Unify.zonk(dom, mctx)
        subgoal_core = ensure_core(subgoal, ctx)

        case resolve(subgoal_core, ctx, env, deeper(state)) do
          {:ok, term} -> {:cont, {:ok, acc ++ [term]}}
          {:error, _} = err -> {:halt, err}
          _ -> {:halt, :fail}
        end
      end
    end)
    |> case do
      {:ok, args} -> {:ok, args}
      :fail -> :fail
      {:error, _} = err -> err
    end
  end

  defp solved?({:meta, _}), do: false
  defp solved?(_), do: true

  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)

  # Descend one level: increment depth only. The cycle stack is extended by
  # `resolve/4` itself when it begins working on a goal, so the parent goal is
  # already on `state.trying` here; pushing the sub-goal too would make it match
  # itself on the next `resolve` and abort every recursion.
  defp deeper(%{depth: d} = state), do: %{state | depth: d + 1}

  # A sub-goal produced by zonk/reify is already a Core term.
  defp ensure_core(term, _ctx), do: term

  # Up-to-conversion equality of two goal Core terms. `Conv.conv?/5` takes Core
  # terms and evaluates them itself, so pass the terms directly (not pre-evaled).
  defp same_goal?(a, b, ctx, env) do
    Cure.Core.Conv.conv?(a, b, Context.env(ctx), Context.length(ctx), env)
  end
end
