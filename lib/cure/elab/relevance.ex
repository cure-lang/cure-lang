defmodule Cure.Elab.Relevance do
  @moduledoc """
  The `{0,ω}` relevance check (M8.3) — the elaborator-side pass that makes
  erasure SOUND. It is the exact dual of `Cure.Elab.Erase`: erasure drops every
  `:erased` argument position, and this check guarantees no `:erased` binder is
  ever *used* in a position erasure would drop it from — so the runtime term
  `Erase.erase` produces never references a binding that no longer exists.

  This lives in the untrusted elaborator (E-layer), NOT the kernel — exactly like
  Idris, where `Core/LinearCheck.idr` runs outside the core conversion checker.
  The kernel stays quantity-blind; `declarations.ex` calls this after
  `Kernel.check` succeeds and before the def is registered/erased.

  ## Idris grounding (Core/LinearCheck.idr)

  Idris runs **two independent mechanisms**, and so does this module.

  ### 1. The position check — Idris `rigSafe` (`:166-170`)

  At a `Local` occurrence, `rigSafe l r = when (l < r) (throw (LinearMisuse …))`:
  a binder whose multiplicity sits strictly below the ambient rig is misused. The
  `{0, ω}` instance of that is "an `:erased` binder may not appear in a RELEVANT
  position", which is the check this module has always performed:

    * RELEVANT (a `0` binder here is a violation):
      - returned as the value (`:returned`);
      - passed in a runtime-**present** argument position of a call/constructor
        (`:present_arg`);
      - scrutinised as a `case` discriminant (`:scrutinee`);
      - applied as a function head (`:applied`).
    * EXEMPT (does not count): type/index positions (`{:pi}`/`{:data}` — Pi
      domains, the `case` motive), erased argument positions, and
      collapsible-family proof elimination (the J/subst transport's scrutinee).

  A present argument position is `Grade.present?/1`, **not** `q == :unrestricted`.
  Slice 4a's rename left the latter here, which exempted every `:linear` and
  `:affine` argument position from the walk — the same trap 4a fixed in `Erase`
  and `Emit`, dormant only until 4b made those grades reachable.

  ### 2. The usage check — Idris `checkUsageOK` (`:274-276`)

  At a `Bind`, `checkUsageOK used r = when (isLinear r && used /= 1) (throw …)`.
  Slice 4b generalises that over the full carrier, which is exactly where affinity
  enters: `:affine` admits `0` or `1`.

  Usage is carried **as a grade** — `:erased` = zero uses, `:linear` = one,
  `:unrestricted` = many — so composition is the semiring:

    * sequence (`:let` value then body, application head then args, `:case`
      scrutinee then branches) sums with `Grade.add/2`: `1 + 1 = ω`;
    * entering a subterm scales with `Grade.mul/2`. An argument position scales by
      the callee's declared grade, so passing a `:linear` variable to an `ω`
      parameter costs `ω`. **A λ's body scales by `ω`**, because a closure may be
      entered any number of times — this is how a linear binder captured by a
      returned closure is rejected without a bespoke rule. Idris achieves the same
      with `eraseLinear env` when checking a `Lam` at `top` (`:233-237`).

  The rule itself is `Grade.leq(used, declared)` — subusaging. Over this carrier
  that is *exhaustively equivalent* to `Grade.admits?(declared, n)` for the
  representative count `n`, and it keeps grades opaque: nothing here
  pattern-matches one. `grade_test.exs` pins the equivalence.

  ### Branches combine by agreement, not summation

  A `case` yields, per binder, the **set** of usages its branches produce, and
  every member must satisfy `leq`. A `:linear` binder used in one branch and
  dropped in another is rejected; an `:affine` one is accepted. Idris's
  `combineUsage` (`:528-540`) throws on any `Use0`/`Use1` mismatch regardless of
  the binder's grade — right for Idris, which has no affine, and wrong here.

  ### Division of labour

  The counting check runs for `:linear` and `:affine` binders. `:erased` stays
  with the position check above, which reports the more precise
  `{:erased_used_relevantly, …}` (naming the *site*) and carries the
  collapsible-family exemption. `:unrestricted` imposes no obligation.

  ## de Bruijn convention

  `check/4` receives the RAW body term (before `wrap_binders(:lam, …)`), so the
  `P = length(quantities)` parameters are its outermost free variables: parameter
  `p` (0-based, telescope order) occurs at de Bruijn index `P-1-p`. Walking with
  an initial `depth = P` makes `level = depth-1-i` recover the parameter index
  directly, and inner binders (`:lam` bodies, `case` branch patterns) simply
  increment `depth` — a free occurrence of parameter `p` at extra depth `d` is
  index `P-1-p+d`, still `level = p`. Levels `>= P` are inner binders, never
  parameters, so never flagged.
  """

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Collapsible

  @type site :: :returned | :present_arg | :scrutinee | :applied
  @type kind :: :param | :lambda | :let | :field

  @typedoc """
  Per-binder usage. Keys are de Bruijn LEVELS; each value is the set of usages the
  term's branches admit for that level (a singleton outside a `case`). A level
  absent from the map was used zero times.
  """
  @type usage :: %{optional(non_neg_integer()) => MapSet.t(Grade.t())}

  @type error ::
          {:erased_used_relevantly, %{def: atom(), binder: non_neg_integer(), site: site()}}
          | {:usage_violation,
             %{def: atom(), binder: non_neg_integer(), kind: kind(), declared: Grade.t(), used: Grade.t()}}

  @doc """
  Check `body` (the raw, pre-lambda-wrapped body term) against `quantities`, the
  per-parameter grade vector (`nil` = all runtime-relevant, no check).

  Enforces both mechanisms described in the moduledoc: no `:erased` binder is used
  in a relevant position, and every `:linear` / `:affine` binder — parameter,
  lambda, `let`, or constructor field bound by a pattern — is used a number of
  times its grade admits. Returns `:ok` or the first violation.
  """
  @spec check(Env.t(), atom(), [Grade.t()] | nil, Cure.Core.Term.t()) :: :ok | {:error, error()}
  def check(_env, _name, quantities, _body) when not is_list(quantities), do: :ok

  def check(env, name, quantities, body) do
    erased =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {q, _idx} -> Grade.erased?(q) end)
      |> Enum.map(fn {_q, idx} -> idx end)
      |> MapSet.new()

    # No early-out when `erased` is empty. Erasedness does not only originate at
    # the signature: matching a constructor with an erased FIELD introduces a fresh
    # erased binder (see the `:case` clause's `branch_erased` fold), so an ordinary
    # all-`:unrestricted` function can still return a value that `Erase.erase` deletes.
    # Idris's `lcheck` (Core/LinearCheck.idr) likewise always walks the body — there
    # is one notion of erased, not a checked and an unchecked one.
    st = %{env: env, name: name, erased: erased}

    # The parameters are the body's outermost free variables, so parameter `p` is
    # de Bruijn LEVEL `p` and its usage is read straight off the walk's result.
    with {:ok, usage} <- walk(body, length(quantities), :returned, st) do
      quantities
      |> Enum.with_index()
      |> each(fn {q, p} -> check_binder(st, p, q, usage, :param) end)
    end
  end

  # --- the usage rule --------------------------------------------------------

  # `Grade.leq(used, declared)` is subusaging, and over this carrier it is exactly
  # `Grade.admits?(declared, count(used))`. `:erased` binders are left to the
  # position check, which reports the site; `:unrestricted` imposes no obligation.
  defp check_binder(st, level, declared, usage, kind) do
    if Grade.restricted?(declared) and not Grade.erased?(declared) do
      usage
      |> Map.get(level, no_uses())
      |> Enum.find(fn used -> not Grade.leq(used, declared) end)
      |> case do
        nil ->
          :ok

        used ->
          {:error, {:usage_violation, %{def: st.name, binder: level, kind: kind, declared: declared, used: used}}}
      end
    else
      :ok
    end
  end

  # An `:erased` `:let` or `:lam` binder joins the POSITION check's tracked set, exactly
  # as an erased constructor FIELD does in `walk_branches/3`. Without this, `:erased`
  # is the one grade no mechanism polices on those binders: `check_binder/5` defers
  # erasure to the position check, and the position check only ever knew about
  # parameters and fields — so `let c :erased = e` and then returning `c` was accepted.
  # `Emit` binds every `:let` unconditionally, so the value does exist at runtime; the
  # lie was in the annotation, not in erasure.
  defp track_erased(st, g, level) do
    if Grade.erased?(g), do: %{st | erased: MapSet.put(st.erased, level)}, else: st
  end

  # --- usage algebra ---------------------------------------------------------

  # Zero uses. A level absent from a usage map has exactly this.
  defp no_uses, do: MapSet.new([Grade.zero()])

  defp one_use(level), do: %{level => MapSet.new([Grade.one()])}

  # Sequential composition: both subterms run, so usages SUM (`1 + 1 = ω`).
  defp seq(u1, u2) do
    Enum.reduce(u2, u1, fn {level, s2}, acc ->
      Map.update(acc, level, s2, fn s1 ->
        for a <- s1, b <- s2, into: MapSet.new(), do: Grade.add(a, b)
      end)
    end)
  end

  defp seq_all(usages), do: Enum.reduce(usages, %{}, &seq(&2, &1))

  # Alternative composition (`case` branches): exactly one branch runs, so the
  # usages are not summed — they are collected, and every one must satisfy `leq`.
  defp alt([]), do: %{}

  defp alt(usages) do
    usages
    |> Enum.flat_map(&Map.keys/1)
    |> Enum.uniq()
    |> Map.new(fn level ->
      {level, usages |> Enum.map(&Map.get(&1, level, no_uses())) |> Enum.reduce(&MapSet.union/2)}
    end)
  end

  # Scale a usage context by the grade of the position it sits in.
  defp scale(usage, g), do: Map.new(usage, fn {l, s} -> {l, MapSet.new(s, &Grade.mul(g, &1))} end)

  # --- relevant positions: an erased-parameter occurrence here is a violation --

  defp walk({:var, i}, depth, site, st) do
    level = depth - 1 - i

    cond do
      level >= 0 and MapSet.member?(st.erased, level) ->
        {:error, {:erased_used_relevantly, %{def: st.name, binder: level, site: site}}}

      level >= 0 ->
        {:ok, one_use(level)}

      true ->
        {:ok, %{}}
    end
  end

  # A closure value: its domain is a type position (exempt); its body is relevant.
  # Descending binds one more variable, at level `depth`.
  #
  # The body's usage of OUTER binders is scaled by `ω`: a λ may be entered any
  # number of times, so one syntactic occurrence inside it is not one use. This is
  # what rejects a linear binder captured by a returned closure, and it is the
  # `mul/2` consequence rather than a rule of its own (Idris: `eraseLinear env`
  # when a `Lam` is checked at `top`, LinearCheck.idr:233-237).
  defp walk({:lam, g, _dom, body}, depth, _site, st) do
    with {:ok, u} <- walk(body, depth + 1, :returned, track_erased(st, g, depth)),
         :ok <- check_binder(st, depth, g, u, :lambda) do
      {:ok, u |> Map.delete(depth) |> scale(Grade.unrestricted())}
    end
  end

  # `:let` — the ascription is a type position (exempt). The VALUE is always
  # evaluated at runtime (`X = Val` in the emitted BEAM), so it is a relevant
  # position regardless of whether the body uses the binder; that is the honest
  # dual of `Emit`'s unconditional bind. The body inherits the let's own site and
  # binds one more variable. Value and body both run, so their usages sum.
  #
  # JOIN POINT (slice 4c). When the value is a λ and the body is a `case` that
  # applies the binder AT MOST ONCE PER BRANCH and nowhere else — the shape
  # `wrap_join/2` produces — this `:let` is a shared branch continuation, not an
  # escaping closure. Idris never materialises such a shape: it usage-checks each
  # case alternative INDEPENDENTLY and combines by agreement (`LinearCheck.idr`
  # `getArgUsage`, `traverse getPUsage pats; combine us`). So the generic ω-scale of
  # a λ body (which assumes the closure may be entered any number of times) is wrong
  # here: the continuation runs at most once on any path, so its captured variables
  # are used at most once — the same count the un-joined per-branch form gives via
  # `alt`. `walk_joined_case/7` reproduces that: it walks the shared body's captures
  # ONCE, unscaled, and injects them as one more alternative into the branch `alt`.
  defp walk({:let, g, _ty, val, body}, depth, site, st) do
    # The un-join inlines the let binder, so it never records the binder's OWN usage
    # — it must therefore only fire when the binder carries NO obligation, i.e. an
    # unrestricted grade. `wrap_join/2` always emits `ω`, so every compiler join
    # qualifies. A user-written `let g :linear = λ …` that happens to match the join
    # shape has a restricted grade `g`, so it takes the generic path below, where
    # `check_binder(st, depth, g, …)` enforces g's own obligation (found by the
    # un-join red-team: skipping it accepted a linear closure dropped in some branch).
    join = if Grade.restricted?(g), do: :not_join, else: join_view(val, body, depth)

    case join do
      {:join, lg, jbody, scrut, branches} ->
        walk_joined_case(lg, jbody, scrut, branches, depth, site, st)

      :not_join ->
        with {:ok, uv} <- walk(val, depth, :present_arg, st),
             {:ok, ub} <- walk(body, depth + 1, site, track_erased(st, g, depth)),
             :ok <- check_binder(st, depth, g, ub, :let) do
          # CBV: the value runs once, so its resources are counted once via `uv`
          # (this is why `let x = consume(c) in …` counts `c` a single time — even
          # if `x` is dropped, and even summed with a second use of `c` in the body).
          # But the binder NAMES that value: if the body uses `x` ω-many times, the
          # value's result — hence any linear resource ALIASED into it — is referenced
          # ω times. `seq(uv, ub\x)` alone dropped the binder's uses and so laundered
          # `let x = cap in (…x…x…)` to a single use. Add the aliasing duplication
          # when `x` is used ω-many times; a linear/affine resource inside `uv` then
          # reaches ω and is rejected, while a value with no restricted resource is
          # unaffected (ω resources carry no obligation). Idris reaches the same
          # verdict by substitution; this keeps Cure's single CBV evaluation.
          dup =
            if Enum.any?(Map.get(ub, depth, no_uses()), &(&1 == Grade.unrestricted())),
              do: scale(uv, Grade.unrestricted()),
              else: %{}

          {:ok, seq(seq(uv, dup), Map.delete(ub, depth))}
        end
    end
  end

  # Application spine: the head is `:applied`; an argument is walked iff a runtime
  # value exists for it (`Grade.present?/1` — the dual of `Erase.erase`'s
  # `{:app, …}` filtering), and its usage is scaled by the callee's declared grade.
  # Passing a linear variable to an `ω` parameter therefore costs `ω`.
  #
  # EXCEPTION — the McBride convoy. `(case s of {c, ar, λx₁…λxₙ. inner} …) a₁ … aₙ`
  # is a case that RETURNS a function, immediately applied to `a₁ … aₙ`. The case
  # picks ONE branch and applies its λ-nest exactly once, so it is NOT an escaping
  # closure: each branch's captures run once (no ω-scale), and each argument `aⱼ` is
  # aliased by the branch binder `xⱼ`, hence used exactly as many times as the branch
  # uses `xⱼ`. This is the shape dependent-`match` / `with` sibling refinement emits
  # (`(case r of λcap'. …reply(cap',…)…) cap`); the generic ω-scale wrongly rejected
  # a linear capability threaded through it. Sound: `aⱼ` scaled by `xⱼ`'s usage, other
  # captures counted once, and the original argument's own grade (e.g. the def's
  # `:linear cap`) is still checked at its binding site — so a branch that DROPS or
  # DUPLICATES it is rejected there (`aⱼ` reaches 0 / ω).
  defp walk({:app, _f, _x} = app, depth, _site, st) do
    {head, args} = spine(app, [])

    case head do
      {:case, scrut, _motive, branches}
      when branches != [] ->
        if Enum.all?(branches, fn {_c, _ar, b} -> lambda_depth(b) >= length(args) end) do
          walk_convoy(scrut, branches, args, depth, st)
        else
          walk_app_spine(head, args, depth, st)
        end

      _ ->
        walk_app_spine(head, args, depth, st)
    end
  end

  # Constructor: same present/erased split, via the family's ctor quantities.
  defp walk({:ctor, cname, args}, depth, _site, st) do
    quantities =
      (Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), length(args)))
      |> pad(length(args))

    walk_args(args, quantities, depth, st)
  end

  # `case`: the discriminant is scrutinised (relevant); the motive is a type
  # position (exempt); each branch body runs under `arity` fresh pattern binders.
  #
  # EXCEPTION — indexed-singleton elimination: a well-typed Core case with one
  # branch is exhaustive at its instantiated indices, even if the family has
  # other constructors globally. If all fields of that forced constructor are
  # erased (e.g. `Equivalent`'s `reflexive`, or one constructor of an indexed
  # `Encodes` proof), it inspects nothing at runtime. Such a scrutinee
  # is a PROOF position, exempt like the retired `{:rewrite}` node's proof
  # (Idris2 permits case on a 0-multiplicity value precisely when the match has
  # a single uninformative alternative; Brady/McBride/McKinna's collapsible
  # families). Sound only because `Erase.erase` drops the whole case for the
  # SAME class (its `collapsible_ctor?/3` must stay in lockstep with
  # `collapsible_case?/2` here), so the exempted scrutinee never survives into
  # the runtime term.
  #
  # Each branch additionally folds its constructor's own erased-field positions
  # into the tracked set — a named erased pattern binder (spec 2026-07-08 §2.3)
  # is policed exactly like an erased top-level parameter.
  #
  # Exactly one branch runs, so branch usages are collected by `alt/1` rather than
  # summed; the scrutinee runs before whichever branch is taken, so it sums.
  defp walk({:case, scrut, _motive, branches}, depth, _site, st) do
    scrut_usage =
      if collapsible_case?(st.env, branches),
        do: {:ok, %{}},
        else: walk(scrut, depth, :scrutinee, st)

    with {:ok, us} <- scrut_usage,
         {:ok, ubs} <- walk_branches(branches, depth, st) do
      {:ok, seq(us, alt(ubs))}
    end
  end

  # --- exempt positions: type formers and proof terms carry no runtime value ---
  defp walk({:pi, _g, _d, _c}, _depth, _site, _st), do: {:ok, %{}}
  defp walk({:data, _n, _ps, _is}, _depth, _site, _st), do: {:ok, %{}}

  # Leaves (`:global`, `:type`, `:hole`, literals) and any other form: no
  # occurrence to account for. Mirrors `Erase`'s leaf clause.
  # `bind(e, λx. body)` runs `e` once, producing `x`, then runs the continuation
  # ONCE — so it is a one-shot graded `let` over the effect's result, NOT the
  # generic ω-scaling `:lam` closure (which assumes a λ may be entered any number
  # of times). Mirror the `:let` `:not_join` branch: `seq` `e`'s uses with the
  # continuation's captures counted ONCE, and `check_binder` enforces the
  # continuation grade `g` on the result binder `x` (linear exactly-once, affine
  # at-most-once). Without this clause an effectful body hit the `_leaf` catch-all
  # and NO usage inside it — erased or graded — was ever counted.
  defp walk({:effect_bind, e, {:lam, g, _dom, body}}, depth, site, st) do
    with {:ok, ue} <- walk(e, depth, :present_arg, st),
         {:ok, ub} <- walk(body, depth + 1, site, track_erased(st, g, depth)),
         :ok <- check_binder(st, depth, g, ub, :lambda) do
      {:ok, seq(ue, Map.delete(ub, depth))}
    end
  end

  # A `bind` with a non-λ (first-class) continuation: seq both children. Not
  # produced by the elaborator today (the let-lowering always emits a literal λ),
  # but keeps the walk total and sound.
  defp walk({:effect_bind, e, k}, depth, site, st) do
    with {:ok, ue} <- walk(e, depth, :present_arg, st),
         {:ok, uk} <- walk(k, depth, site, st) do
      {:ok, seq(ue, uk)}
    end
  end

  # `pure(a)` returns `a`; `Effect(T)` in a term position walks its payload.
  defp walk({:effect_pure, a}, depth, site, st), do: walk(a, depth, site, st)
  defp walk({:effect_type, t}, depth, site, st), do: walk(t, depth, site, st)

  defp walk(_leaf, _depth, _site, _st), do: {:ok, %{}}

  defp walk_app_spine(head, args, depth, st) do
    quantities = callee_quantities(head, length(args), st.env)

    with {:ok, uh} <- walk(head, depth, :applied, st),
         {:ok, ua} <- walk_args(args, quantities, depth, st) do
      {:ok, seq(uh, ua)}
    end
  end

  defp lambda_depth({:lam, _g, _d, b}), do: 1 + lambda_depth(b)
  defp lambda_depth(_), do: 0

  # The convoy: scrutinee runs once (relevant, or exempt if collapsible), then one
  # branch. Each branch's λ-nest binds `x₁…xₙ` to `a₁…aₙ` and runs once.
  defp walk_convoy(scrut, branches, args, depth, st) do
    scrut_usage =
      if collapsible_case?(st.env, branches),
        do: {:ok, %{}},
        else: walk(scrut, depth, :scrutinee, st)

    with {:ok, us} <- scrut_usage,
         {:ok, ubs} <- walk_convoy_branches(branches, args, depth, st) do
      {:ok, seq(us, alt(ubs))}
    end
  end

  defp walk_convoy_branches(branches, args, depth, st) do
    n = length(args)

    branches
    |> Enum.reduce_while({:ok, []}, fn {cname, arity, body}, {:ok, acc} ->
      ctor_qs =
        Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), arity)

      branch_erased =
        ctor_qs
        |> Enum.with_index()
        |> Enum.filter(fn {q, _p} -> Grade.erased?(q) end)
        |> Enum.map(fn {_q, p} -> depth + p end)

      st2 = %{st | erased: Enum.into(branch_erased, st.erased)}

      # Peel the n λ binders (they sit ABOVE the `arity` pattern binders). `xⱼ` is at
      # level `depth + arity + j`; `inner` is walked below all of them.
      {lam_grades, inner} = peel_lambdas(body, n)
      inner_depth = depth + arity + n

      case walk(inner, inner_depth, :returned, st2) do
        {:ok, u_inner} ->
          x_levels = for(j <- 0..(n - 1)//1, do: depth + arity + j)

          # Each xⱼ aliases aⱼ, so aⱼ is used as many times as `inner` uses xⱼ.
          # A relevant use of an erased binder inside a present convoy argument is a
          # LEGITIMATE rejection (`walk` returns `{:error, :erased_used_relevantly}`);
          # PROPAGATE it instead of crashing on a hard `{:ok, ua} =` match — otherwise
          # an ill-typed body (an erased implicit passed to a present-position call
          # under a `rewrite`/`match`) raises a MatchError rather than reporting the
          # error.
          arg_usages_result =
            args
            |> Enum.with_index()
            |> Enum.reduce_while({:ok, []}, fn {arg, j}, {:ok, acc_u} ->
              x_usage = Map.get(u_inner, Enum.at(x_levels, j), no_uses())
              lambda_grade = Enum.at(lam_grades, j, Grade.unrestricted())

              # Convoy arguments are authored in the OUTER frame. Constructor
              # fields exist only inside the selected branch; applying `st2`
              # here aliases their levels with binders introduced inside an
              # argument (for example a lambda), falsely treating those binders
              # as erased. The branch-local state remains correct for `inner`
              # above; outer arguments must be walked with the outer state.
              if Grade.erased?(lambda_grade) and Enum.all?(x_usage, &Grade.erased?/1) do
                # The selected branch never uses this convoy binder. The
                # application is administrative dependent transport, not a
                # runtime call argument; walking `arg` as present before scaling
                # would reject an erased proof even though its use count is zero.
                {:cont, {:ok, acc_u ++ [%{}]}}
              else
                case walk(arg, depth, :present_arg, st) do
                  {:ok, ua} -> {:cont, {:ok, acc_u ++ [scale_by_uses(ua, x_usage)]}}
                  {:error, _} = err -> {:halt, err}
                end
              end
            end)

          with {:ok, arg_usages} <- arg_usages_result,
               :ok <- check_convoy_binders(st2, x_levels, lam_grades, u_inner),
               :ok <- check_fields(st2, ctor_qs, depth, u_inner) do
            drop = x_levels ++ for(p <- 0..(arity - 1)//1, do: depth + p)
            {:cont, {:ok, acc ++ [seq(seq_all(arg_usages), Map.drop(u_inner, drop))]}}
          else
            {:error, _} = err -> {:halt, err}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp peel_lambdas(body, 0), do: {[], body}
  defp peel_lambdas({:lam, g, _d, b}, n), do: peel_lambdas(b, n - 1) |> then(fn {gs, i} -> {[g | gs], i} end)
  defp peel_lambdas(body, _n), do: {[], body}

  defp check_convoy_binders(st, x_levels, lam_grades, u_inner) do
    x_levels
    |> Enum.zip(lam_grades)
    |> each(fn {lvl, g} -> check_binder(st, lvl, g, u_inner, :lambda) end)
  end

  # Scale a usage context by a SET of use-grades: each entry used once per member,
  # the scaled copies UNIONED per level. Do NOT `alt` against an empty base — `alt`
  # reads an absent level as `{0}` (no_uses), which would inject a spurious drop into
  # every level and make a linearly-used argument look dropped.
  defp scale_by_uses(usage, use_set) do
    Enum.reduce(use_set, %{}, fn g, acc ->
      Map.merge(acc, scale(usage, g), fn _l, a, b -> MapSet.union(a, b) end)
    end)
  end

  # Recognise the join idiom AND prove it is sound to un-join: the `:let` value is a
  # λ, the body is a `case`, and the let binder (de Bruijn level `depth`) occurs in
  # that case ONLY as an application head `{:app, {:var, →depth}, _}`, AT MOST ONCE in
  # any single branch, and NOWHERE in the scrutinee or motive. Under those conditions
  # the continuation is one-shot per execution path, so counting its captures once
  # (not ω) never under-counts. Any other shape → `:not_join`, keeping the sound,
  # conservative ω-scale of the generic `:let`/`:lam` path.
  defp join_view({:lam, lg, _dom, jbody}, {:case, scrut, motive, branches}, depth) do
    # The continuation's parameter grade `lg` must be unrestricted. The un-join scales
    # a branch argument by `lg` (`scale(us0, lg)`); a RESTRICTED `lg` — in particular
    # `:erased` — would annihilate that argument's usage (`mul(:erased, _) = :erased`)
    # while `Erase` still keeps the call argument (`{:var}`-headed apps are never
    # dropped), an under-rejection. Today every `:lam` is `ω` (no surface syntax grades
    # a lambda parameter), so this is belt-and-suspenders — but making it STRUCTURAL
    # keeps a future lambda-grade slice from silently re-opening the hole (both round-3
    # red-team agents flagged this exact landmine). A restricted `lg` → the sound
    # generic `:let` path (which ω-scales the whole lambda value).
    if not Grade.restricted?(lg) and join_binder_safe?(scrut, motive, branches, depth) do
      {:join, lg, jbody, scrut, branches}
    else
      :not_join
    end
  end

  defp join_view(_val, _body, _depth), do: :not_join

  # The join binder is at level `depth`. The `case` sits one binder deeper
  # (`case_depth`); inside a branch it is under `arity` more pattern binders. Safe to
  # un-join iff it does not occur in the scrutinee or motive, and EVERY branch is
  # either free of it entirely (a matched arm) OR is EXACTLY a bare tail application
  # `{:app, {:var, →depth}, s}` with the binder absent from `s` (a defaulted branch
  # that runs the shared continuation exactly once). This is precisely the shape
  # `wrap_join/2` emits, and precisely the shape `walk_join_branches/5` inlines — a
  # branch that applied the binder in ANY other position (`sink(j(x))`, `j(a)+j(b)`)
  # would be walked as a matched arm, dropping the binder and LOSING the shared
  # continuation's captures (an under-count). Anything else → `:not_join` → the sound
  # ω-scale of the generic `:lam`/`:let` path.
  defp join_binder_safe?(scrut, motive, branches, depth) do
    case_depth = depth + 1

    count_level(scrut, case_depth, depth) == 0 and
      count_level(motive, case_depth, depth) == 0 and
      Enum.all?(branches, fn {_c, arity, body} ->
        bd = case_depth + arity

        case body do
          {:app, {:var, idx}, s} when bd - 1 - idx == depth ->
            count_level(s, bd, depth) == 0

          _ ->
            count_level(body, bd, depth) == 0
        end
      end)
  end

  # Count free occurrences of de Bruijn LEVEL `target` in `term` (walked at `depth`).
  defp count_level({:var, i}, depth, target), do: if(depth - 1 - i == target, do: 1, else: 0)
  defp count_level({:lam, _g, d, b}, depth, t), do: count_level(d, depth, t) + count_level(b, depth + 1, t)
  defp count_level({:pi, _g, d, c}, depth, t), do: count_level(d, depth, t) + count_level(c, depth + 1, t)

  defp count_level({:let, _g, ty, v, b}, depth, t),
    do: count_level(ty, depth, t) + count_level(v, depth, t) + count_level(b, depth + 1, t)

  defp count_level({:app, f, x}, depth, t), do: count_level(f, depth, t) + count_level(x, depth, t)
  defp count_level({:ctor, _n, args}, depth, t), do: Enum.sum(Enum.map(args, &count_level(&1, depth, t)))

  defp count_level({:data, _n, ps, is}, depth, t),
    do: Enum.sum(Enum.map(ps ++ is, &count_level(&1, depth, t)))

  defp count_level({:case, s, m, brs}, depth, t) do
    count_level(s, depth, t) + count_level(m, depth, t) +
      Enum.sum(Enum.map(brs, fn {_c, ar, b} -> count_level(b, depth + ar, t) end))
  end

  defp count_level({:effect_type, inner}, depth, t), do: count_level(inner, depth, t)
  defp count_level({:effect_pure, value}, depth, t), do: count_level(value, depth, t)

  defp count_level({:effect_bind, effect, continuation}, depth, t),
    do: count_level(effect, depth, t) + count_level(continuation, depth, t)

  defp count_level(_leaf, _depth, _t), do: 0

  # Un-join: check the shared continuation ONCE (unscaled), then combine it as one
  # alternative with the matched-arm usages. `alt` (agreement) then counts a captured
  # variable at most once across all branches — the Idris per-alternative result.
  defp walk_joined_case(lg, jbody, scrut, branches, depth, _site, st) do
    with {:ok, uj} <- walk(jbody, depth + 1, :returned, track_erased(st, lg, depth)),
         :ok <- check_binder(st, depth, lg, uj, :lambda) do
      jbody_captures = Map.delete(uj, depth)
      case_depth = depth + 1

      scrut_usage =
        if collapsible_case?(st.env, branches),
          do: {:ok, %{}},
          else: walk(scrut, case_depth, :scrutinee, st)

      with {:ok, us} <- scrut_usage,
           {:ok, ubs} <-
             walk_join_branches(branches, case_depth, depth, jbody_captures, lg, st) do
        {:ok, seq(us, alt(ubs)) |> Map.delete(depth)}
      end
    end
  end

  # Like `walk_branches/3`, but a branch that IS a join application `{:app, {:var,
  # arity}, s}` contributes the shared continuation's captures (already computed,
  # unscaled) seq'd with the usage of its scrutinee argument — never counting the
  # join binder itself (it is inlined). Matched arms walk normally.
  defp walk_join_branches(branches, depth, join_level, jbody_captures, lg, st) do
    branches
    |> Enum.reduce_while({:ok, []}, fn {cname, arity, body}, {:ok, acc} ->
      ctor_qs =
        Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), arity)

      branch_erased =
        ctor_qs
        |> Enum.with_index()
        |> Enum.filter(fn {q, _p} -> Grade.erased?(q) end)
        |> Enum.map(fn {_q, p} -> depth + p end)

      st2 = %{st | erased: Enum.into(branch_erased, st.erased)}
      drop_levels = for(p <- 0..(arity - 1)//1, do: depth + p)

      result =
        case body do
          {:app, {:var, idx}, s} when depth + arity - 1 - idx == join_level ->
            # Defaulted branch: it runs the shared continuation. Its usage is that
            # continuation's captures plus the usage of the scrutinee it is applied
            # to; the join binder is inlined, never counted. `check_fields` still
            # polices this branch's OWN pattern-bound constructor fields, uniformly
            # with the matched-arm clause below — currently a no-op (ctor fields are
            # only `:erased`/`:unrestricted`), but the invariant must not depend on
            # that (red-team Finding 3).
            with {:ok, us0} <- walk(s, depth + arity, :present_arg, st2) do
              # `s` is an ARGUMENT to the continuation, so it is scaled by the
              # continuation's DECLARED parameter grade `lg` — exactly as a normal
              # application scales an argument by the callee's grade (Idris `checkRig =
              # rigf |*| rig`). Today every lambda is `ω`, so `s` is ω-scaled. It must
              # NOT be scaled by how many times the parameter is USED: that models
              # call-by-NAME (an unused parameter skips evaluating the argument), but
              # the BEAM is call-by-VALUE — `s` is always evaluated, so a resource it
              # consumes can never be annihilated by the continuation ignoring its
              # parameter (three round-2 red-team agents all found that hole).
              bu = seq(scale(us0, lg), jbody_captures)

              with :ok <- check_fields(st2, ctor_qs, depth, bu) do
                {:ok, Map.drop(bu, drop_levels)}
              end
            end

          _ ->
            with {:ok, u} <- walk(body, depth + arity, :returned, st2),
                 :ok <- check_fields(st2, ctor_qs, depth, u) do
              {:ok, Map.drop(u, drop_levels)}
            end
        end

      case result do
        {:ok, bu} -> {:cont, {:ok, acc ++ [bu]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Each branch binds its constructor's fields at levels `depth + p`. An erased
  # field joins the position check's tracked set (spec 2026-07-08 §2.3, a named
  # erased pattern binder is policed like an erased parameter); a restricted one is
  # usage-checked like any other binder, then dropped from the usage that escapes.
  defp walk_branches(branches, depth, st) do
    branches
    |> Enum.reduce_while({:ok, []}, fn {cname, arity, body}, {:ok, acc} ->
      ctor_qs =
        Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), arity)

      branch_erased =
        ctor_qs
        |> Enum.with_index()
        |> Enum.filter(fn {q, _p} -> Grade.erased?(q) end)
        |> Enum.map(fn {_q, p} -> depth + p end)

      st2 = %{st | erased: Enum.into(branch_erased, st.erased)}

      with {:ok, u} <- walk(body, depth + arity, :returned, st2),
           :ok <- check_fields(st2, ctor_qs, depth, u) do
        {:cont, {:ok, acc ++ [Map.drop(u, for(p <- 0..(arity - 1)//1, do: depth + p))]}}
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp check_fields(st, ctor_qs, depth, usage) do
    ctor_qs
    |> Enum.with_index()
    |> each(fn {q, p} -> check_binder(st, depth + p, q, usage, :field) end)
  end

  # Walk each present argument and scale its usage by the position's grade; erased
  # positions are not walked at all (the position check's exemption).
  defp walk_args(args, quantities, depth, st) do
    args
    |> Enum.zip(quantities)
    |> Enum.reduce_while({:ok, []}, fn {arg, q}, {:ok, acc} ->
      if Grade.present?(q) do
        case walk(arg, depth, :present_arg, st) do
          {:ok, u} -> {:cont, {:ok, acc ++ [scale(u, q)]}}
          {:error, _} = err -> {:halt, err}
        end
      else
        {:cont, {:ok, acc}}
      end
    end)
    |> case do
      {:ok, usages} -> {:ok, seq_all(usages)}
      {:error, _} = err -> err
    end
  end

  # Exactly one branch whose fields are all erased. Kernel coverage
  # has already proved this constructor is the only inhabitant possible at the
  # case's instantiated indices; requiring it to be the family's only constructor
  # globally would incorrectly reject indexed singleton elimination. A nullary
  # branch collapses only for an indexed family, preserving ordinary Unit-like
  # value cases.
  defp collapsible_case?(env, branches), do: Collapsible.classify(env, branches) != :runtime

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  defp callee_quantities({:global, name}, arity, env) do
    case Env.get_def(env, name) do
      %{quantities: qs} when is_list(qs) -> pad(qs, arity)
      _ -> List.duplicate(Grade.unrestricted(), arity)
    end
  end

  defp callee_quantities({:ctor, cname, _args}, arity, env) do
    (Inductive.ctor_quantities(env, cname) || List.duplicate(Grade.unrestricted(), arity)) |> pad(arity)
  end

  defp callee_quantities(_other, arity, _env), do: List.duplicate(Grade.unrestricted(), arity)

  # Conservative padding: an argument position with no declared quantity is
  # treated as `:unrestricted` (relevant), never silently exempted.
  defp pad(qs, n) when length(qs) == n, do: qs

  # Over-application: the extra arguments apply to the callee's RESULT and are always present.
  defp pad(qs, n) when length(qs) < n, do: qs ++ List.duplicate(Grade.unrestricted(), n - length(qs))

  # Fewer arguments than declared quantities: by `Erase.erase/2`'s own convention, the term is
  # ALREADY ERASED — its erased arguments have been dropped, so the survivors occupy the
  # ORIGINAL trailing positions, not the leading ones. `Enum.take(qs, n)` realigned them onto
  # the leading labels, and a genuinely present survivor landing on an `:erased` label was
  # silently exempted from the relevance check. Erase guards this exact case ("re-zipping the
  # full quantity vector against the shrunk arg list would realign survivors onto leading
  # positions and DROP them"); Relevance, its documented dual, did not. Every surviving
  # argument of an already-erased term is relevant.
  defp pad(_qs, n), do: List.duplicate(Grade.unrestricted(), n)

  defp each(list, fun) do
    Enum.reduce_while(list, :ok, fn item, :ok ->
      case fun.(item) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
