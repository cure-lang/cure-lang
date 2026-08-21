defmodule Cure.Core.Normalise do
  @moduledoc """
  Trusted normalization service for Core terms.

  Evaluation and read-back remain split across `Cure.Core.Eval` and
  `Cure.Core.Quote`; this module is the trusted owner of the policy between
  them: certified δ-unfolding, weak-head reduction, full normal forms, and the
  deterministic δ fuel counter used by conversion.
  """

  alias Cure.Core.{Context, Env, Eval, Quote}

  @fuel_key {__MODULE__, :fuel}

  @type delta_mode :: :certified | :reducible | :none
  @type fuel :: pos_integer() | :infinity
  @type opts :: [
          delta: delta_mode(),
          delta_allow: MapSet.t(atom()) | nil,
          mode: :whnf | :nf,
          fuel: fuel(),
          stuck_cases: :preserve | :expose
        ]

  @doc "Reduce `term` to weak-head normal form in `ctx` and read it back."
  @spec whnf(Context.t(), Cure.Core.Term.t(), opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def whnf(ctx, term, opts \\ []) do
    run_with_fuel(Keyword.put(opts, :mode, :whnf), fn opts ->
      ctx
      |> eval_in(term)
      |> whnf_value(Context.signature(ctx), opts)
      |> Quote.reify(Context.length(ctx), Context.signature(ctx))
    end)
  end

  @doc "Reduce `term` to normal form in `ctx` and read it back."
  @spec nf(Context.t(), Cure.Core.Term.t(), opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def nf(ctx, term, opts \\ []) do
    run_with_fuel(Keyword.put(opts, :mode, :nf), fn opts ->
      ctx
      |> eval_in(term)
      |> nf_value(Context.signature(ctx), Context.length(ctx), opts)
      |> Quote.reify(Context.length(ctx), Context.signature(ctx))
    end)
  end

  @doc """
  Read a semantic value back to a Core term. The optional 3rd arg is the
  inductive signature: passing it recovers an indexed family's param/index split
  in the read-back (`nil`, the default, keeps the flat form conversion compares).
  """
  @spec quote(Cure.Core.Value.t(), non_neg_integer(), Env.t() | nil) :: Cure.Core.Term.t()
  def quote(value, depth, sig \\ nil), do: Quote.reify(value, depth, sig)

  @doc false
  @spec whnf_value(Cure.Core.Value.t(), Env.t() | nil, opts()) :: Cure.Core.Value.t()
  def whnf_value(value, sig, opts \\ [])

  def whnf_value(value, nil, _opts), do: value

  def whnf_value({:vneutral, neutral} = value, sig, opts) do
    opts = normalize_opts(opts)

    case unfold_head(neutral, sig, opts) do
      {:ok, reduced} -> whnf_value(reduced, sig, opts)
      :stuck -> value
    end
  end

  def whnf_value(value, _sig, _opts), do: value

  @doc false
  @spec with_fuel(fuel(), (-> term())) :: term() | :fuel_exhausted
  def with_fuel(:infinity, fun), do: fun.()

  # The budget lives in the process dictionary, so it is a dynamically-scoped variable and
  # must be saved and restored like one. It used to be unconditionally `Process.delete`d on
  # exit: a nested `with_fuel` — `conv_within?/6` inside a fueled `nf/3`, or a reentrant
  # `whnf/3` — wiped the enclosing, still-live counter on its way out, and every subsequent
  # δ-unfold in the outer computation found no key and ran unbounded. The bound a caller
  # asked for silently stopped being a bound.
  def with_fuel(fuel, fun) when is_integer(fuel) and fuel > 0 do
    outer = Process.get(@fuel_key, :none)
    Process.put(@fuel_key, fuel)

    try do
      fun.()
    catch
      :throw, {@fuel_key, :exhausted} -> :fuel_exhausted
    after
      case outer do
        :none -> Process.delete(@fuel_key)
        remaining -> Process.put(@fuel_key, remaining)
      end
    end
  end

  @doc false
  @spec fuel_key() :: term()
  def fuel_key, do: @fuel_key

  defp eval_in(ctx, term), do: Eval.eval(term, Context.env(ctx))

  defp run_with_fuel(opts, fun) do
    opts = normalize_opts(opts)
    with_fuel(opts[:fuel], fn -> fun.(opts) end)
  end

  defp normalize_opts(opts) do
    opts =
      opts
      |> Keyword.put_new(:delta, :certified)
      |> Keyword.put_new(:delta_allow, nil)
      |> Keyword.put_new(:mode, :nf)
      |> Keyword.put_new(:fuel, :infinity)
      |> Keyword.put_new(:stuck_cases, :preserve)

    delta = Keyword.fetch!(opts, :delta)
    delta_allow = Keyword.fetch!(opts, :delta_allow)
    mode = Keyword.fetch!(opts, :mode)
    fuel = Keyword.fetch!(opts, :fuel)
    stuck_cases = Keyword.fetch!(opts, :stuck_cases)

    unless delta in [:certified, :reducible, :none] do
      raise ArgumentError, "expected :delta to be :certified, :reducible, or :none, got: #{inspect(delta)}"
    end

    unless is_nil(delta_allow) or match?(%MapSet{}, delta_allow) do
      raise ArgumentError, "expected :delta_allow to be a MapSet or nil"
    end

    unless mode in [:whnf, :nf] do
      raise ArgumentError, "expected :mode to be :whnf or :nf, got: #{inspect(mode)}"
    end

    unless stuck_cases in [:preserve, :expose] do
      raise ArgumentError,
            "expected :stuck_cases to be :preserve or :expose, got: #{inspect(stuck_cases)}"
    end

    unless fuel == :infinity or (is_integer(fuel) and fuel > 0) do
      raise ArgumentError, "expected :fuel to be a positive integer or :infinity, got: #{inspect(fuel)}"
    end

    opts
  rescue
    MatchError ->
      raise ArgumentError,
            "expected normalization options delta: :certified | :reducible | :none, mode: :whnf | :nf, " <>
              "fuel: pos_integer() | :infinity, stuck_cases: :preserve | :expose"
  end

  defp nf_value(value, sig, depth, opts) do
    value
    |> whnf_value(sig, opts)
    |> nf_struct(sig, depth, opts)
  end

  # The identity value-environment for `depth` binders: the neutral vars
  # [{:nvar,depth-1}, …, {:nvar,0}]. `nf_struct`'s binder clauses reify the body
  # to a `depth+1` de Bruijn term via `quote_nf`; storing it in a closure with
  # this env (rather than `[]`) makes the OUTER `Quote.reify` re-eval a provable
  # identity, so free (context) variables read back unchanged instead of being
  # reflected by re-evaluation in a truncated env. (depth 0 → []).
  defp id_env(depth), do: Context.neutral_env(depth)

  defp nf_struct({:vpi, g, dom, {:closure, env, cod}}, sig, depth, opts) do
    fresh = {:vneutral, {:nvar, depth}}

    {:vpi, g, nf_value(dom, sig, depth, opts),
     {:closure, id_env(depth), quote_nf(Eval.eval(cod, [fresh | env]), sig, depth + 1, opts)}}
  end

  defp nf_struct({:vlam, g, dom, {:closure, env, body}}, sig, depth, opts) do
    fresh = {:vneutral, {:nvar, depth}}

    {:vlam, g, nf_value(dom, sig, depth, opts),
     {:closure, id_env(depth), quote_nf(Eval.eval(body, [fresh | env]), sig, depth + 1, opts)}}
  end

  defp nf_struct({:vdata, name, args}, sig, depth, opts),
    do: {:vdata, name, Enum.map(args, &nf_value(&1, sig, depth, opts))}

  defp nf_struct({:vctor, name, args}, sig, depth, opts),
    do: {:vctor, name, Enum.map(args, &nf_value(&1, sig, depth, opts))}

  defp nf_struct({:vneutral, neutral}, sig, depth, opts),
    do: {:vneutral, nf_neutral(neutral, sig, depth, opts)}

  # Inert effect values: read back structurally, normalising SUBTERMS only, so
  # the shape (`bind`/`pure`/`Effect` and its op spine) is preserved exactly —
  # the nf-idempotence and inertness-invariance the design (§3.2/§9) requires.
  defp nf_struct({:veffect_type, v}, sig, depth, opts),
    do: {:veffect_type, nf_value(v, sig, depth, opts)}

  defp nf_struct({:veffect_pure, v}, sig, depth, opts),
    do: {:veffect_pure, nf_value(v, sig, depth, opts)}

  defp nf_struct({:veffect_bind, ve, vk}, sig, depth, opts),
    do: {:veffect_bind, nf_value(ve, sig, depth, opts), nf_value(vk, sig, depth, opts)}

  defp nf_struct(value, _sig, _depth, _opts), do: value

  defp nf_neutral({:napp, neutral, arg}, sig, depth, opts),
    do: {:napp, nf_neutral(neutral, sig, depth, opts), nf_value(arg, sig, depth, opts)}

  defp nf_neutral({:ncase, neutral, motive, branches}, sig, depth, opts) do
    {:ncase, nf_neutral(neutral, sig, depth, opts), nf_motive(motive, sig, depth, opts),
     Enum.map(branches, &nf_branch(&1, sig, depth, opts))}
  end

  defp nf_neutral(neutral, _sig, _depth, _opts), do: neutral

  # Normalize a stuck-case motive/branch closure. Left un-normalized these keep a
  # certified global FOLDED (β/ι are recovered by `Quote.reify`, but δ only fires
  # in `nf_value`), so `nf` would not be a δ-normal form. Mirror `Quote`'s
  # readback: the motive is a COMPLETE function term instantiated with NO extra
  # binder; a branch body lives under its ctor's `arity` binders. Re-close the
  # normalized term over `id_env(depth)`, exactly as `nf_struct` does for λ/Π.
  defp nf_motive({:closure, env, term}, sig, depth, opts),
    do: {:closure, id_env(depth), quote_nf(Eval.eval(term, env), sig, depth, opts)}

  defp nf_branch({c, arity, {:closure, env, body}}, sig, depth, opts),
    do:
      {c, arity,
       {:closure, id_env(depth), quote_nf(Eval.open_branch(env, body, arity, depth), sig, depth + arity, opts)}}

  defp quote_nf(value, sig, depth, opts), do: value |> nf_value(sig, depth, opts) |> Quote.reify(depth, sig)

  defp unfold_head(neutral, sig, opts) do
    if opts[:delta] == :none do
      :stuck
    else
      unfold_certified_head(neutral, sig, opts)
    end
  end

  # δ-reduce a neutral's spine head when that head is either a certified-total
  # global OR a *stuck eliminator* (`ncase`/`nfst`/`nsnd`) whose target itself
  # δ-reduces to a constructor/pair. In the eliminator case we whnf the target
  # (threading the caller's `opts`, so `delta: :none` and fuel/mode are honored)
  # and, when a value emerges, apply the SAME ι-rule `eval` trusts, then re-apply
  # the spine `args`. Each ι-reduction spends fuel so termination stays bounded.
  defp unfold_certified_head(neutral, sig, opts) do
    {head, args} = spine(neutral, [])

    case head do
      {:nglobal, name} ->
        # δ-unfold a certified global by evaluating its body in the EMPTY env.
        # Guard: the body MUST be closed — an open body's free de Bruijn variables
        # would surface as neutral `{:nvar, k}` and alias whatever the ambient
        # context binds at level k (a capture). `Env.certify/2` already refuses
        # open bodies, so this only fires against a forged marker; staying stuck is
        # the safe answer (never unsound, at worst a missed unfold). (A5)
        #
        # Lazy unfolding (Idris/Lean/Agda): if unfolding a pattern-matching
        # definition only re-exposes an eliminator that is itself STUCK on a
        # neutral (no ι-progress possible), keep the application FOLDED. Eagerly
        # expanding `f x` into its internal `case x {…}` when `x` is neutral
        # yields a non-canonical normal form (the same stuck recursive call then
        # has two shapes — folded in one spine, expanded in another), which both
        # breaks syntactic occurrence-matching in the elaborator and can make
        # conversion δ-loop on open terms. Freezing is always sound: it only
        # makes normal forms MORE distinct, never collapses two of them, and
        # `conv?` still δ-unfolds on demand when it must compare. (A6)
        # K2 (spec 2026-07-09 §1.2): dispatch FIRST on the builtin-op marker so a
        # body-less op def never reaches the generic `Eval.eval(body, [])` path
        # (which would crash on the nil body). The certified-body path below is
        # unchanged for ordinary defs.
        definition = Env.get_def(sig, name)
        delta_allowed? = is_nil(opts[:delta_allow]) or MapSet.member?(opts[:delta_allow], name)

        if not delta_allowed? or
             (opts[:delta] == :reducible and not match?(%{reducible: true}, definition)) do
          :stuck
        else
          case definition do
            %{builtin_op: bop} when not is_nil(bop) ->
              builtin_op_fold(bop, args, sig, opts)

            _ ->
              with true <- Env.certified?(sig, name),
                   %{body: body} <- definition,
                   true <- Cure.Core.Term.closed?(body) do
                case eval_certified_application(body, args) do
                  # A certified identity (or any definition whose open
                  # application evaluates back to the exact same neutral)
                  # made the old loop re-enter `whnf_value/3` forever:
                  # `f x` unfolded to `x`, `reduce_unfolded/3` reported
                  # progress, and the neutral was forced again indefinitely.
                  # Open terms are already in weak-head normal form here; an
                  # unchanged neutral is therefore *stuck*, not progress.
                  # This is especially important for indexed branch
                  # refinement, which normalizes computed family indices.
                  {:ok, {:vneutral, ^neutral}} ->
                    :stuck

                  {:ok, value} ->
                    if opts[:stuck_cases] == :expose,
                      do: {:ok, value},
                      else: reduce_unfolded(value, sig, opts)

                  :stuck ->
                    :stuck
                end
              else
                _ -> :stuck
              end
          end
        end

      # ι on `case`: mirrors the ctor branch of `eval({:case,…})` — reduce the
      # matching branch body in `reverse(cargs) ++ env`.
      {:ncase, scrut, _motive, branches} ->
        # `nat_to_ctor_if`/`bounded_to_ctor_if` peel a compact-Nat / compact-Bounded
        # scrutinee to `Z`/`S` / `First`/`Next` so it reuses the ctor ι-rule below;
        # the two value shapes are disjoint, so composing is safe and every other
        # value passes through unchanged.
        case Eval.int_to_ctor_if(
               Eval.bounded_to_ctor_if(Eval.nat_to_ctor_if(whnf_value({:vneutral, scrut}, sig, opts)))
             ) do
          {:vctor, cname, cargs} ->
            case Enum.find(branches, fn {c, _ar, _b} -> Eval.constructor_name_matches?(c, cname) end) do
              {_c, ar, {:closure, env, body}} ->
                {:ok, reapply(args, spend_fuel(Eval.reduce_branch_body(body, env, cargs, ar)))}

              nil ->
                :stuck
            end

          _ ->
            :stuck
        end

      _ ->
        :stuck
    end
  end

  # Conversion normalizes speculative/open Core before the kernel has accepted
  # it. Runtime evaluation of checked Core remains strict, but δ-normalization
  # must stay total: an invalid application is simply unable to unfold.
  defp eval_certified_application(body, args) do
    {:ok, reapply(args, spend_fuel(Eval.eval(body, [])))}
  rescue
    RuntimeError -> :stuck
  end

  # Decide, in ONE whnf of the eliminated target, whether a certified global's
  # δ-unfold made progress. If the unfold only re-exposed a stuck eliminator
  # (`ncase`) — the lazy-unfolding case — this both decides productiveness AND
  # fires ι, so the two never re-force the same scrutinee.
  #
  # Threading the FORCED target through `spend_fuel(Eval.eval(...))` (rather than
  # returning the raw stuck eliminator for the outer `whnf_value`
  # loop to re-force) is what keeps normalization LINEAR: a naive check that
  # whnf's the scrutinee to test productiveness and then lets the loop whnf it a
  # second time to reduce is Θ(2ᵈ) on total definitions whose recursive scrutinee
  # reduces to a constructor (e.g. `f n = case n {Z→Z; S k→case (f k) {…}}`).
  #
  #   * ctor target      → ι fires here, result returned reduced (productive);
  #   * stuck target     → `:stuck`, so `whnf_value` keeps the global FOLDED;
  #   * anything else (ctor, λ, or a neutral not headed by an eliminator) →
  #     `{:ok, value}`, i.e. genuine progress the outer loop continues from.
  defp reduce_unfolded({:vneutral, neutral} = value, sig, opts) do
    {head, args} = spine(neutral, [])

    case head do
      {:ncase, scrut, _motive, branches} ->
        # See the twin arm above: peel a compact-Nat / compact-Bounded scrutinee
        # before the ctor ι.
        case Eval.int_to_ctor_if(
               Eval.bounded_to_ctor_if(Eval.nat_to_ctor_if(whnf_value({:vneutral, scrut}, sig, opts)))
             ) do
          {:vctor, cname, cargs} ->
            case Enum.find(branches, fn {c, _ar, _b} -> c == cname end) do
              {_c, ar, {:closure, env, body}} ->
                # Keep following the ι chain rather than returning after ONE step. If the
                # branch body re-exposes a *stuck* `ncase` (a case whose scrutinee is a
                # non-reducible neutral), this recursion propagates that `:stuck` up so the
                # WHOLE def-application freezes — folded — instead of surfacing the residual
                # `case`. That makes the A6 freeze CONSISTENT: `f(<ctor>, x)` (outer case
                # ι-fires eagerly in `eval`, leaving a stuck inner `case x`) and
                # `f(<stuck-global>, x)` (outer case forced HERE, same stuck inner `case x`)
                # both freeze to `f(…, x)`, so conversion compares them argument-wise instead
                # of one folded and one expanded (finding K1). It only ever freezes MORE — a
                # result headed by a constructor or another global still returns `{:ok, …}` —
                # so NF termination is preserved (and mutual recursion is unaffected: we never
                # UNfreeze a recursive re-exposure). Each ι still spends fuel.
                reduce_unfolded(
                  reapply(args, spend_fuel(Eval.reduce_branch_body(body, env, cargs, ar))),
                  sig,
                  opts
                )

              nil ->
                :stuck
            end

          _ ->
            if opts[:stuck_cases] == :expose, do: {:ok, value}, else: :stuck
        end

      _ ->
        {:ok, value}
    end
  end

  defp reduce_unfolded(value, _sig, _opts), do: {:ok, value}

  # Literal acceleration for builtin-op globals (spec 2026-07-09 §1.2; Lean
  # reduce_nat / Idris Builtin-op analog). Fold ONLY a saturated spine whose
  # arguments all whnf to literals — via the SAME audited table Eval uses
  # (§G.1: div/rem by literal zero returns :stuck and the spine stays neutral).
  # Anything else (open args, wrong arity/overapplication) stays stuck: never
  # unsound, at worst a missed unfold. `args` are already VALUES (spine/2);
  # whnf_value forces any residual certified-global redex among them.
  # Amendment A1 (spec §1-A): struct_eq/struct_ne take [tyval, l, r] and
  # delegate to the SAME audited :eq/:ne fold over the two VALUE args — the type
  # argument is not consulted (and not forced for literalness). Folds iff both
  # value args whnf to int/float/atom literals (late-instantiated polymorphic
  # operands, same as today's prim); NEUTRAL otherwise — ADT equality never
  # computes in the kernel (R8c).
  defp builtin_op_fold(op, [_tyval, l, r], sig, opts) when op in [:struct_eq, :struct_ne] do
    vals = Enum.map([l, r], &whnf_value(&1, sig, opts))

    if Enum.all?(vals, fn value ->
         match?({:vint, _}, value) or match?({:vfloat, _}, value) or
           match?({:vatom, _}, value) or match?({:vbounded, _}, value)
       end) do
      Eval.fold(if(op == :struct_eq, do: :eq, else: :ne), vals)
    else
      :stuck
    end
  end

  defp builtin_op_fold(op, args, sig, opts) when op not in [:struct_eq, :struct_ne] do
    arity = if op in [:neg, :bnot], do: 1, else: 2

    with true <- length(args) == arity,
         vals = Enum.map(args, &whnf_value(&1, sig, opts)),
         true <- Enum.all?(vals, &(match?({:vint, _}, &1) or match?({:vfloat, _}, &1))) do
      Eval.fold(op, vals)
    else
      _ -> :stuck
    end
  end

  # A struct op at the wrong arity (unsaturated/overapplied): stuck, never unsound.
  defp builtin_op_fold(_op, _args, _sig, _opts), do: :stuck

  defp reapply(args, value), do: Eval.apply_spine(value, args)

  defp spend_fuel(reduced) do
    case Process.get(@fuel_key) do
      nil ->
        reduced

      0 ->
        throw({@fuel_key, :exhausted})

      n ->
        Process.put(@fuel_key, n - 1)
        reduced
    end
  end

  defp spine({:napp, n, arg}, acc), do: spine(n, [arg | acc])
  defp spine(head, acc), do: {head, acc}
end
