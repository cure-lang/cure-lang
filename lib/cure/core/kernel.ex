defmodule Cure.Core.Kernel do
  @moduledoc """
  The trusted bidirectional type checker (design spec §4.3, §5).

  `infer/2` synthesises a type **value** for a term; `check/3` verifies a term
  against an expected type value, falling back to `infer` plus a cumulative
  conversion test on the result. Types are compared as values via
  `Cure.Core.Conv` (NbE definitional equality); universe cumulativity is applied
  at the sort level (`Type i <: Type i+1`).

  This module is part of the trusted kernel: it is small, pure, and deterministic,
  and it never trusts an elaborator-supplied type — it re-derives everything.

  Coverage grows by milestone: Type/var/Π here (M2.2), λ/application (M2.3),
  constructors (M3.4), `case` (M4), Σ (M5), `Eq`/`refl`/`rewrite` (M6), global
  definitions + certificates (M7).
  """

  alias Cure.Core.{Certificate, Context, Conv, Env, Eval, Inductive, Normalise, Quote, Term, Universe}

  @type result :: {:ok, Cure.Core.Value.t()} | {:error, term()}

  @certificate_timing_sink_key {__MODULE__, :certificate_timing_sink}

  # The fixed predicative ceiling (`Universe.ceiling()`), mirrored into a compile
  # constant so it is usable in guards. Single source of truth stays `Universe`.
  @universe_ceiling Universe.ceiling()

  @doc false
  @spec with_certificate_timing_sink((term() -> any()), (-> result)) :: result when result: term()
  def with_certificate_timing_sink(sink, operation)
      when is_function(sink, 1) and is_function(operation, 0) do
    previous = Process.put(@certificate_timing_sink_key, sink)

    try do
      operation.()
    after
      if is_nil(previous) do
        Process.delete(@certificate_timing_sink_key)
      else
        Process.put(@certificate_timing_sink_key, previous)
      end
    end
  end

  @doc """
  Normalize `term` in `ctx` via the shared trusted Core normalizer
  (`Cure.Core.Normalise`).

  Full normal form under the certified δ gate, preserving stuck `case`
  (`stuck_cases: :preserve`): it unfolds certified global heads and reduces β/ι
  redexes but does not recurse into the branch bodies of a neutral case — which
  keeps recursive certified definitions from expanding forever while still
  exposing the definitional equalities the surface proof elaborator needs.
  """
  @spec normalize(Context.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t() | :fuel_exhausted
  def normalize(ctx, term), do: Normalise.nf(ctx, term)

  @doc "Normalize `term` in `ctx` via the shared trusted Core normalizer, with options."
  @spec normalize(Context.t(), Cure.Core.Term.t(), Normalise.opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def normalize(ctx, term, opts), do: Normalise.nf(ctx, term, opts)
  @doc "Synthesise the type value of `term` in `ctx`."
  @spec infer(Context.t(), Cure.Core.Term.t()) :: result()
  def infer(_ctx, {:type, level}) do
    case Universe.succ(level) do
      {:ok, l1} -> {:ok, {:vtype, l1}}
      {:error, reason} -> {:error, reason}
    end
  end

  def infer(ctx, {:var, k}) do
    case Context.lookup(ctx, k) do
      nil -> {:error, {:unbound_var, k}}
      type_value -> {:ok, type_value}
    end
  end

  # Primitive Int/Bool/Float: base types live in `Type0`, literals inhabit them,
  # and each primitive op is typed against the kernel (arithmetic/comparison are
  # numeric-polymorphic over Int or Float; connectives are on Bool).
  #
  # NOTE(int-facade): `{:int_type}` is retired from surface production (spec
  # 2026-07-18 §3a — `Int` is the inductive family); this clause stays so
  # `infer` remains total on a legacy/deserialized term still carrying it.
  def infer(_ctx, {:int_type}), do: {:ok, {:vtype, 0}}

  # A compact `Int` literal inhabits the canonical `Int` inductive family — its type
  # is the family value `{:vdata, :Int, []}`, exactly as a `{:nat_lit}` inhabits `Nat`.
  # The surface flip (spec 2026-07-18) retired the primitive `{:vint_type}`; the
  # literal ↔ `FromNat`/`NegativeSuccessor` spine bridge is the audited `int_to_ctor`
  # fold, so the compact node and the constructor form share one type at this rule.
  def infer(ctx, {:int_lit, _n}), do: {:ok, int_type_value(Context.signature(ctx))}

  # A compact Nat literal inhabits the canonical `Nat` inductive family — its type
  # is the family value `{:vdata, :Nat, []}`, exactly what `infer({:ctor, :Z, []})`
  # and `eval({:data, :Nat, [], []})` produce, so a literal and the `S`-tower are
  # interchangeable at the type level too (needs `ctx` to reach the signature).
  def infer(ctx, {:nat_lit, n}) when is_integer(n) and n >= 0,
    do: {:ok, nat_type_value(Context.signature(ctx))}

  # A compact `Bounded` literal `k` inhabits `Bounded(n)` for every bound `n > k`;
  # pure inference cannot source the intended bound, so it yields the MINIMAL
  # witness type `Bounded(k+1)` (sound: `k < k+1`). Admitting `k` at a wider
  # DECLARED bound (e.g. the `Char = Bounded(0x110000)` case) is the checking rule's
  # job — inference is the rarely-taken fallback. `Bounded` must be the registered
  # `@builtin(:bounded)` family for the literal to have a type at all.
  def infer(ctx, {:bounded_lit, k}) when is_integer(k) and k >= 0 do
    case Inductive.builtin(Context.signature(ctx), :bounded) do
      nil -> {:error, :bounded_family_unregistered}
      fid -> {:ok, {:vdata, fid, [{:vnat, k + 1}]}}
    end
  end

  def infer(_ctx, {:float_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:float_lit, _f}), do: {:ok, {:vfloat_type}}
  def infer(_ctx, {:binary_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:atom_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:atom_lit, a}) when is_atom(a), do: {:ok, {:vatom_type}}

  # {:absurd} is an elaborator-only marker sitting in a discharged (unreachable)
  # case branch, which check_case_branches never checks. It has no positive typing
  # rule; a reachable occurrence fails cleanly here rather than crashing the kernel
  # with an unmatched-clause exception (spec §5/§8.1).
  def infer(_ctx, {:absurd}), do: {:error, :absurd_in_reachable_position}

  # A hole is checkable at any type (`check/3` below) but has nothing to infer — its type is
  # known only from the expected type, as in Agda and Idris. Without this clause `infer/2`
  # raised an unmatched-clause exception on a node the kernel otherwise accepts, and every
  # caller that expects `{:error, _}` — `MetaCheck.progresses?/2` and `type_preserved?/2`,
  # whose `case`/`else` cannot catch a raise — crashed on a legitimate mid-development term.
  def infer(_ctx, {:hole, name}), do: {:error, {:hole_in_inference_position, name}}

  def infer(ctx, {:pi, _g, dom, cod}) do
    with {:ok, l1} <- infer_sort(ctx, dom),
         dom_value = Eval.eval(dom, Context.env(ctx)),
         ctx2 = Context.extend(ctx, dom_value),
         {:ok, l2} <- infer_sort(ctx2, cod) do
      {:ok, {:vtype, Universe.max(l1, l2)}}
    end
  end

  # let-binding (ζ). Typing mirrors Lean's `infer_let`
  # (`src/kernel/type_checker.cpp`): the ascription must be a sort, the value
  # must check against it, and the let's type is the body's type.
  #
  # The body is checked under `Context.extend_def/3`, so the bound variable is
  # definitionally its value. Two consequences worth stating, because they are
  # what make this a small change:
  #
  #   * No inferred type can mention the bound variable — it is never a neutral —
  #     so unlike Lean's fvar formulation there is nothing to re-abstract
  #     (`mk_pi(fvars, r)`). Values carry their own environments.
  #   * `Eval` erases the node (ζ), so no `let` reaches `Conv`, `Quote` or any
  #     normal form. Sharing lives in the term; transparency lives in the env.
  def infer(ctx, {:let, _g, ty, val, body}) do
    with {:ok, _level} <- infer_sort(ctx, ty),
         ty_value = Eval.eval(ty, Context.env(ctx)),
         :ok <- check(ctx, val, ty_value) do
      val_value = Eval.eval(val, Context.env(ctx))
      infer(Context.extend_def(ctx, ty_value, val_value), body)
    end
  end

  def infer(ctx, {:lam, g, dom, body}) do
    with {:ok, _level} <- infer_sort(ctx, dom) do
      dom_value = Eval.eval(dom, Context.env(ctx))
      ctx2 = Context.extend(ctx, dom_value)

      with {:ok, cod_value} <- infer(ctx2, body) do
        # Reify the body's type into a codomain family over the binder.
        cod_term = Quote.reify(cod_value, Context.length(ctx2))
        {:ok, {:vpi, g, dom_value, {:closure, Context.env(ctx), cod_term}}}
      end
    end
  end

  def infer(ctx, {:global, name}) do
    case Env.get_def(Context.signature(ctx), name) do
      nil ->
        {:error, {:unknown_global, name, %{core_term: {:global, name}, context_size: Context.length(ctx)}}}

      %{type: type_term} ->
        {:ok, Eval.eval(type_term, [])}
    end
  end

  def infer(ctx, {:app, f, a}) do
    with {:ok, f_type} <- infer(ctx, f),
         # whnf the head's type first: a function whose type is a certified global
         # (or applied family) that δ-reduces to a Π must not be rejected as
         # :not_a_function on its un-reduced syntactic form.
         {:ok, dom, cod_closure} <-
           ensure_pi(Normalise.whnf_value(f_type, Context.signature(ctx))),
         :ok <- check(ctx, a, dom) do
      a_value = Eval.eval(a, Context.env(ctx))
      {:ok, Eval.apply_closure(cod_closure, a_value)}
    end
  end

  # -- inert effects (design 2026-07-09 §3.1) ---------------------------------
  #
  # `Effect : Type ℓ → Type ℓ` — level-preserving formation. `t` must be a type;
  # `Effect(t)` lives in the same universe. No reduction is ever attached to any
  # of these nodes: the kernel TYPES them, `Conv`/`Normalise` compare them by
  # structural congruence, and nothing else.
  def infer(ctx, {:effect_type, t}) do
    with {:ok, level} <- infer_sort(ctx, t) do
      {:ok, {:vtype, level}}
    end
  end

  # `pure(a) : Effect(A)` where `a : A`. Inference synthesises `A` from `a`.
  def infer(ctx, {:effect_pure, a}) do
    with {:ok, a_type} <- infer(ctx, a) do
      {:ok, {:veffect_type, a_type}}
    end
  end

  # `bind(e, k) : Effect(B)` for `e : Effect(A)` and `k : A -> Effect(B)`
  # (NON-dependent in v1, matching Lean's `Bind.bind`). Infer `e`, whnf its type
  # to `Effect(A)`; infer `k`, whnf to a `Π A -> Effect(B)`, require its domain
  # convertible with `A`, then read `B` off the codomain (instantiated at a fresh
  # neutral — non-dependent, so `B` does not mention it). The `bind` node itself
  # binds nothing and is never reduced.
  def infer(ctx, {:effect_bind, e, k}) do
    sig = Context.signature(ctx)
    depth = Context.length(ctx)

    with {:ok, e_type} <- infer(ctx, e),
         {:ok, a_val} <- ensure_effect(Normalise.whnf_value(e_type, sig), :effect_bind_not_effect),
         {:ok, k_type} <- infer(ctx, k),
         {:ok, kdom, kcod_closure} <- ensure_pi(Normalise.whnf_value(k_type, sig)),
         :ok <- ensure_conv(kdom, a_val, depth, sig, :effect_bind_domain_mismatch),
         cod_value = Eval.apply_closure(kcod_closure, {:vneutral, {:nvar, depth}}),
         {:ok, b_val} <-
           ensure_effect(Normalise.whnf_value(cod_value, sig), :effect_bind_cont_not_effect) do
      {:ok, {:veffect_type, b_val}}
    end
  end

  def infer(ctx, {:data, name, params, indices}) do
    case Inductive.get_family(Context.signature(ctx), name) do
      nil ->
        {:error, {:unknown_family, name}}

      %{params: ptele, indices: itele, level: level} ->
        with {:ok, pvals} <- check_spine(ctx, params, ptele, []),
             {:ok, _ivals} <- check_spine(ctx, indices, itele, pvals) do
          {:ok, {:vtype, level}}
        end
    end
  end

  def infer(ctx, {:ctor, name, args}) do
    sig = Context.signature(ctx)

    case Inductive.get_ctor(sig, name) do
      nil ->
        {:error, {:unknown_ctor, name}}

      %{args: tele} = ctor_sig ->
        family_name = Inductive.ctor_family(sig, name)
        pc = Inductive.param_count(sig, family_name)

        cond do
          pc == 0 ->
            with {:ok, arg_env, _fields} <- check_ctor_app(ctx, [], args, tele) do
              # The accumulated arg values (most-recent first) are exactly the env
              # in which the result terms are written; compute them by NbE (so a
              # computed index like `and(d1,d2)` reduces once δ is available, M7).
              {:ok, result_vdata(arg_env, family_name, ctor_sig)}
            end

          # K6 / §E.1: the data parameters ride the spine at grade 0 (Lean's kernel
          # form). When the P params are supplied ahead of the F fields, the kernel
          # READS and re-checks them from the family's parameter telescope — no
          # metavariable inference in the TCB — so a param-bearing constructor is
          # checkable in INFERENCE position (closes #545/#599; unblocks the Eq
          # `bridge_step`'s inductive refl). Checking `params ++ fields` against
          # `ptele ++ tele` yields the SAME arg_env as the checking-mode path
          # (fields-most-recent ++ params), so `result_*` de Bruijn indices resolve
          # identically.
          length(args) == pc + length(tele) ->
            ptele = Inductive.param_telescope(sig, family_name) || []

            with {:ok, arg_env, _fields} <- check_ctor_app(ctx, [], args, ptele ++ tele) do
              {:ok, result_vdata(arg_env, family_name, ctor_sig)}
            end

          # Params absent from a bare fields-only spine: nothing carries them, so
          # the ctor must be type-CHECKED against an expected vdata that supplies
          # them — see the check/3 clause below.
          true ->
            {:error, {:ctor_requires_checking_mode, family_name}}
        end
    end
  end

  def infer(ctx, {:case, scrut, motive, branches}) do
    sig = Context.signature(ctx)

    case infer(ctx, scrut) do
      {:ok, scrut_type} ->
        case Normalise.whnf_value(scrut_type, sig) do
          {:vdata, dname, scrut_args} ->
            family = Inductive.get_family(sig, dname)
            # An OPAQUE (postulate) family is non-eliminable: refuse the `case`
            # BEFORE coverage. A zero-constructor family passes coverage vacuously
            # (empty branch list = ex-falso, §H), so without this guard an opaque
            # type would be freely ex-falso-eliminable — the marker, not the ctor
            # count, is what forbids elimination (Agda `postulate`).
            if Inductive.opaque_family?(family) do
              {:error, :opaque_not_eliminable}
            else
              infer_case_data(ctx, sig, dname, family, scrut, scrut_args, motive, branches)
            end

          _other ->
            {:error, :case_scrutinee_not_data}
        end

      {:error, _} = err ->
        err
    end
  end

  defp infer_case_data(ctx, sig, dname, family, scrut, scrut_args, motive, branches) do
    # {:vdata} carries params ++ indices; the motive and the branch-index
    # unifier range over indices only, so split the params off up front.
    pc = Inductive.param_count(sig, dname)
    {scrut_params, scrut_idx} = Enum.split(scrut_args, pc)
    motive_value = Eval.eval(motive, Context.env(ctx))
    scrut_value = Eval.eval(scrut, Context.env(ctx))

    with :ok <- check_motive_wf(ctx, motive_value, family, scrut_params),
         :ok <- check_coverage(ctx, sig, dname, branches, scrut_idx, scrut_params, scrut_value),
         :ok <-
           check_case_branches(
             ctx,
             sig,
             dname,
             motive_value,
             branches,
             scrut_idx,
             scrut_params,
             scrut_value
           ) do
      # Result type = motive at the scrutinee's actual indices and value (§4.4).
      {:ok, apply_motive(motive_value, scrut_idx ++ [scrut_value])}
    end
  end

  @doc "Check while retaining the first failing case branch for diagnostics."
  @spec check_with_branch_details(Context.t(), Cure.Core.Term.t(), Cure.Core.Value.t()) ::
          :ok | {:error, term()}
  def check_with_branch_details(ctx, term, expected) do
    key = {__MODULE__, :branch_details}
    previous = Process.get(key)
    Process.put(key, {:active, []})

    try do
      result = check(ctx, term, expected)

      case {result, Process.get(key)} do
        {{:error, :branch_type}, {:active, details}} when is_list(details) ->
          {:error, {:branch_type, %{branches: Enum.reverse(details)}}}

        _ ->
          result
      end
    after
      if is_nil(previous), do: Process.delete(key), else: Process.put(key, previous)
    end
  end

  @doc "Check `term` against the expected type value in `ctx`."
  @spec check(Context.t(), Cure.Core.Term.t(), Cure.Core.Value.t()) :: :ok | {:error, term()}

  # Bidirectional rule: a lambda is checked against a Π, propagating the expected
  # domain into the body (more robust than infer when the body is not standalone).
  # A λ checks against a Π of the SAME grade. Grades are part of type identity
  # (see `Conv`), so a mismatch is a type error, not a usage error — the usage
  # check never runs in the kernel. Compared by equality, never by `Grade.leq/2`.
  def check(ctx, {:lam, g, dom, body}, {:vpi, exp_g, exp_dom, cod_closure}) do
    dom_value = Eval.eval(dom, Context.env(ctx))

    cond do
      g != exp_g ->
        {:error, {:grade_mismatch, %{lam: g, pi: exp_g}}}

      not Conv.conv_values?(dom_value, exp_dom, Context.length(ctx), Context.signature(ctx)) ->
        {:error, :domain_mismatch}

      true ->
        fresh = {:vneutral, {:nvar, Context.length(ctx)}}
        cod_value = Eval.apply_closure(cod_closure, fresh)
        check(Context.extend(ctx, exp_dom), body, cod_value)
    end
  end

  # A hole is a deferred term: accepted at any goal type. Its obligation is
  # reported to the user and blocks codegen until filled (§6 / M8.5).
  # Checking a `let` pushes the expected type through to the body. Without this
  # clause `check_via_infer/3` would INFER the body, which forbids check-only
  # terms (`{:hole, _}`, `{:absurd}`, `{:bounded_lit, _}`) in a let body — the
  # very regression a `(λ x. body) val` β-redex encoding suffers, since the λ
  # must be inferred. `expected` is a level-indexed value and stays valid under
  # the extended context.
  def check(ctx, {:let, _g, ty, val, body}, expected) do
    with {:ok, _level} <- infer_sort(ctx, ty),
         ty_value = Eval.eval(ty, Context.env(ctx)),
         :ok <- check(ctx, val, ty_value) do
      val_value = Eval.eval(val, Context.env(ctx))
      check(Context.extend_def(ctx, ty_value, val_value), body, expected)
    end
  end

  def check(_ctx, {:hole, _name}, _expected), do: :ok

  # Checking-mode constructor application: the expected vdata supplies the
  # family's parameters (which pure inference cannot source), so this is the path
  # a param-bearing constructor takes (from check_def's top-level check and from
  # check_case_branches' per-branch check). `:vdata` is a 3-tuple carrying a
  # single combined `params ++ indices` list; split off the params by param_count
  # to seed check_ctor_app, then re-derive the actual result and compare it to
  # `expected` (arguments checking against their own types is NOT enough — the
  # computed indices must still match the expected type's).
  def check(ctx, {:ctor, cname, args} = term, expected) do
    # Weak-head-normalise the GOAL before dispatching on its head: a constructor
    # can be checked against any type that δ-unfolds to the family's `{:vdata,…}`
    # — e.g. a `typealias String = List(Char)` goal, which reaches here as the
    # bare alias global (a neutral), not a literal `{:vdata,…}`. This mirrors the
    # `bounded_lit` clause below (and Agda/Lean, which whnf the goal in checking
    # mode). Sound: `elaborate_ctor` still field-checks and converts the computed
    # result against the whnf'd goal, which is definitionally the original goal, so
    # no ill-typed constructor is admitted. A goal that does NOT expose a `{:vdata}`
    # head falls through to the infer-then-convert path, exactly as before.
    case Normalise.whnf_value(expected, Context.signature(ctx)) do
      {:vdata, _family, _combined} = vd ->
        with {:ok, _value} <- elaborate_ctor(ctx, cname, args, vd), do: :ok

      _ ->
        check_via_infer(ctx, term, expected)
    end
  end

  # Checking a compact `Bounded` literal against a concrete declared bound. δ-whnf
  # the expected type to expose the `Bounded` family and its bound index; the
  # literal `k` inhabits `Bounded(n)` iff `0 <= k < n`. The kernel re-derives `n`
  # itself — it never trusts the elaborator's bound check (this is the TCB gate).
  # This is where `97 : Char` (= `Bounded(0x110000)`) is admitted, which the
  # infer-then-convert fallback cannot do (inference only knows `Bounded(k+1)`).
  # Placed before the generic catch-all so it is reachable (Elixir clause order).
  def check(ctx, {:bounded_lit, k}, expected) when is_integer(k) and k >= 0 do
    sig = Context.signature(ctx)
    bounded_fid = Inductive.builtin(sig, :bounded)
    char_fid = Inductive.builtin(sig, :char)
    depth = Context.length(ctx)

    case Normalise.whnf_value(expected, sig) do
      # `Char` is a constructor-less nominal carrier, so this rule is the ONLY
      # introduction form for it — the kernel re-derives the Unicode scalar
      # ceiling itself rather than trusting the elaborator, exactly as it does
      # for a declared `Bounded` bound below. `Char`'s own
      # `ExpressibleByCharacterLiteral` instance cannot serve instead: its
      # descriptor field is already a `Char`, so it presupposes what it would
      # construct.
      {:vdata, ^char_fid, []} when not is_nil(char_fid) ->
        if k < 0x110000,
          do: :ok,
          else: {:error, {:bounded_lit_out_of_range, k, 0x110000}}

      {:vdata, ^bounded_fid, [bound_val]} when not is_nil(bounded_fid) ->
        case concrete_nat(bound_val, sig) do
          {:ok, n} when k < n -> :ok
          {:ok, n} -> {:error, {:bounded_lit_out_of_range, k, n}}
          :error -> {:error, {:bounded_bound_not_concrete, Quote.reify(bound_val, depth, sig)}}
        end

      other ->
        {:error, {:conversion_failure, {:bounded_lit, k}, Quote.reify(other, depth, sig)}}
    end
  end

  # Checking-mode `pure`: when the goal whnf's to `Effect(G)`, push `G` into `a`
  # (so a check-only `a` is admitted, mirroring the `let`/`ctor` clauses). A goal
  # that is not an `Effect(_)` falls to the infer-then-convert path.
  def check(ctx, {:effect_pure, a}, expected) do
    case Normalise.whnf_value(expected, Context.signature(ctx)) do
      {:veffect_type, g} -> check(ctx, a, g)
      _ -> check_via_infer(ctx, {:effect_pure, a}, expected)
    end
  end

  # Checking-mode `bind` against goal `Effect(B)`: INFER the bind and convert its
  # inferred `Effect(B')` against the goal. Inference reads the continuation's
  # type via `ensure_pi`, which takes the Π's domain/codomain and IGNORES its
  # grade — so a continuation of ANY multiplicity (`λ (r :linear A). …`, the
  # graded-effect-binder case) is accepted, and the grade is the relevance
  # checker's obligation, not a fixed value the kernel invents here. (The prior
  # cut built the Π with a hardcoded ω grade and rejected a graded continuation
  # on `Conv`'s grade-equality.) A goal that is not `Effect(_)` falls to the
  # generic infer-then-convert.
  def check(ctx, {:effect_bind, _e, _k} = term, expected) do
    sig = Context.signature(ctx)

    case ensure_effect(Normalise.whnf_value(expected, sig), :effect_bind_goal_not_effect) do
      {:ok, _b_goal} ->
        with {:ok, inferred} <- infer(ctx, term),
             :ok <-
               ensure_conv(
                 inferred,
                 Normalise.whnf_value(expected, sig),
                 Context.length(ctx),
                 sig,
                 :effect_bind_result_mismatch
               ) do
          :ok
        end

      {:error, _} ->
        check_via_infer(ctx, term, expected)
    end
  end

  def check(ctx, term, expected), do: check_via_infer(ctx, term, expected)

  # Shared checking-mode constructor elaboration. Checks the fields-only spine
  # against the ctor telescope, converts the computed result type against the
  # expected `vdata`, and RETURNS the constructor's own value — assembled from the
  # recursively-checked field values (`{:vctor, cname, field_vals}`). Returning the
  # value lets a caller thread it up the spine instead of re-evaluating the surface
  # sub-term at every level: the O(n²)→O(n) fix for deep constructor towers (the
  # value-returning bidirectional checker, cf. Idris's `Glued`). The returned value
  # is definitionally `Eval.eval({:ctor, cname, args}, env)`, so `check/3`'s `:ok`
  # contract and all downstream index/conversion logic are unchanged.
  defp elaborate_ctor(ctx, cname, args, {:vdata, family, combined_args} = expected) do
    sig = Context.signature(ctx)
    pc = Inductive.param_count(sig, family)
    {params, _indices} = Enum.split(combined_args, pc)

    case Inductive.get_ctor(sig, cname) do
      nil ->
        {:error, {:unknown_ctor, cname}}

      %{args: tele} = ctor_sig ->
        cond do
          Inductive.ctor_family(sig, cname) != family ->
            {:error, {:foreign_ctor, cname}}

          # Fields-only spelling — the existing specialized path, byte-identical.
          # MUST be first: for a paramless family (pc == 0) the spine condition
          # below collapses to this same predicate (spec §1 "order is load-bearing").
          length(args) == length(tele) ->
            with {:ok, arg_env, field_vals} <- check_ctor_app(ctx, params, args, tele) do
              actual = result_vdata(arg_env, family, ctor_sig)

              if Conv.conv_values?(actual, expected, Context.length(ctx), sig) do
                {:ok, {:vctor, cname, field_vals}}
              else
                {:error, {:conversion_failure, actual, expected}}
              end
            end

          # Params-on-spine spelling (K6/§E.1, the inference form): the fields-only
          # strategy cannot measure this arity. Coherence (spec 2026-07-09, Lean's
          # check = infer + def-eq): route to the generic fallback — infer re-checks
          # the spine params against the family telescope (the K6 arm), then the
          # result converts against `expected`. Accepts nothing that is not already
          # inferable-and-convertible. This rare spelling is not the deep-tower hot
          # path, so recovering the value with a single eval is fine.
          pc > 0 and length(args) == pc + length(tele) ->
            with :ok <- check_via_infer(ctx, {:ctor, cname, args}, expected) do
              {:ok, Eval.eval({:ctor, cname, args}, Context.env(ctx))}
            end

          true ->
            {:error, :ctor_arity}
        end
    end
  end

  # Peel a value to a concrete non-negative integer bound, spanning both Nat
  # representations: the compact `{:vnat, n}` and the `Z`/`S` tower (a bound may be
  # written either way). A non-concrete (neutral/symbolic) bound returns `:error`
  # — a literal cannot be checked against an unknown ceiling.
  # Read a closed Nat value through the canonical builtin-family identity. An
  # imported interface owns its constructors (`Std.Nat#Z`/`Std.Nat#S`), so
  # matching the historical bare atoms silently rejected the very canonical
  # representation used outside Std.Nat. Normalize at every predecessor: a
  # certified recursive arithmetic function commonly exposes one constructor at
  # a time (`plus (S m) n` -> `S (plus m n)`).
  defp concrete_nat(value, sig) do
    value = Normalise.whnf_value(value, sig)

    case value do
      {:vnat, n} when is_integer(n) and n >= 0 ->
        {:ok, n}

      {:vctor, cname, []} ->
        if nat_ctor_position(sig, cname) == 0, do: {:ok, 0}, else: :error

      {:vctor, cname, [pred]} ->
        if nat_ctor_position(sig, cname) == 1 do
          case concrete_nat(pred, sig) do
            {:ok, n} -> {:ok, n + 1}
            :error -> :error
          end
        else
          :error
        end

      _other ->
        :error
    end
  end

  defp nat_ctor_position(sig, cname) do
    case Inductive.builtin(sig, :nat) do
      nil -> nil
      family -> sig |> Inductive.ctors_of(family) |> Enum.find_index(&(&1.name == cname))
    end
  end

  # The generic checking rule (moduledoc: "falling back to `infer` plus a
  # cumulative conversion test") — shared by the fallthrough clause and the
  # params-on-spine ctor branch above so the coherence logic exists exactly once.
  defp check_via_infer(ctx, term, expected) do
    with {:ok, inferred} <- infer(ctx, term) do
      if subtype?(inferred, expected, ctx) do
        :ok
      else
        # Conversion failure diagnostic (§10): report both normal forms so the
        # mismatch is legible (and serializable via C2 for independent checkers).
        # Legible means the context's signature has to be threaded through: without
        # it, `reify` collapses an indexed family's params/indices split into a flat
        # `params` list with `indices => []`, which `Conv` tolerates but a human — or
        # an independent checker rebuilding the term — cannot.
        depth = Context.length(ctx)
        sig = Context.signature(ctx)

        {:error, {:conversion_failure, Quote.reify(inferred, depth, sig), Quote.reify(expected, depth, sig)}}
      end
    end
  end

  @doc """
  Type-check a registered global definition: its declared type is a valid type,
  and its body checks against that type. The kernel re-derives everything — it
  never trusts an elaborator-supplied type. (δ-unfolding stays disabled until the
  def is also totality-certified, M7.2.)
  """
  @spec check_def(Env.t(), atom()) :: :ok | {:error, term()}
  def check_def(env, name) do
    case Env.get_def(env, name) do
      nil ->
        {:error, {:unknown_global, name, %{core_term: {:global, name}, context_size: nil}}}

      # Builtin-op def (K2, R4): body-less by design. Check its DECLARED TYPE
      # only — the nil body must never reach `check`/`infer` (no nil clause →
      # crash). Total by fiat (Lean/Idris treat primitive ops so). Reachable via
      # TotalityClosure.certify_type_level once builtin-op spines occur in TYPE
      # positions (dependent-index arithmetic). Ordering: BEFORE the generic
      # %{type:, body:} clause, which these defs would also match.
      # A builtin-op def has no body, but it still has a declared TYPE, and that type is
      # inside the Final-Core grammar boundary just like a body is. This branch used to check
      # only that the type is a valid sort, so every `:reject` clause the validator enforces
      # was silently unenforced along this admission path — the exact gap the validator exists
      # to close, and one `validator_test.exs` already pins for the generic branch.
      %{builtin_op: op, type: type_term} when not is_nil(op) ->
        with {:ok, _level} <-
               timed_certificate_stage(name, :type_sort, fn ->
                 infer_sort(Context.empty(env), type_term)
               end),
             :ok <-
               timed_certificate_stage(name, :final_core_validation, fn ->
                 run_final_core_validator([type_term])
               end) do
          :ok
        end

      %{type: type_term, body: body_term} ->
        ctx = Context.empty(env)

        with {:ok, _level} <-
               timed_certificate_stage(name, :type_sort, fn -> infer_sort(ctx, type_term) end),
             :ok <-
               timed_certificate_stage(name, :body_check, fn ->
                 check(ctx, body_term, Eval.eval(type_term, []))
               end),
             :ok <-
               timed_certificate_stage(name, :final_core_validation, fn ->
                 run_final_core_validator([type_term, body_term])
               end) do
          :ok
        end
    end
  end

  defp timed_certificate_stage(name, stage, operation) when is_function(operation, 0) do
    case Process.get(@certificate_timing_sink_key) do
      sink when is_function(sink, 1) ->
        started = System.monotonic_time(:microsecond)
        result = operation.()
        elapsed = System.monotonic_time(:microsecond) - started
        sink.({:kernel_certificate_timing, stage, elapsed, %{definition: name}})
        result

      _ ->
        operation.()
    end
  end

  @doc "Kernel-check only a global declaration's published type."
  @spec check_def_type(Env.t(), atom()) :: :ok | {:error, term()}
  def check_def_type(env, name) do
    case Env.get_def(env, name) do
      nil ->
        {:error, {:unknown_global, name, %{core_term: {:global, name}, context_size: nil}}}

      %{type: type_term} ->
        with {:ok, _level} <- infer_sort(Context.empty(env), type_term),
             :ok <- run_final_core_validator([type_term]) do
          :ok
        end
    end
  end

  # Final-Core grammar-boundary instrumentation (K11a). Scans BOTH the declared
  # type and the body — a legacy node in a signature is as much a checklist hit
  # as one in the body. Emits warnings via the pipeline and rejects only clauses
  # configured to :reject (none, by Wave-0 default); on a mixed verdict,
  # rejections from either term are combined.
  # Every Core term admitted by `check_def` — a declared type, a body, or both — crosses the
  # Final-Core grammar boundary. Warnings are emitted; rejections from all terms are
  # collected so one call reports every violation rather than the first.
  defp run_final_core_validator(terms) do
    cfg = Cure.Core.Validator.check_def_config()
    results = Enum.map(terms, &Cure.Core.Validator.validate(&1, cfg))

    case Enum.flat_map(results, fn
           {:error, rejections} -> rejections
           {:ok, _warnings} -> []
         end) do
      [] ->
        for {:ok, warnings} <- results, d <- warnings do
          Cure.Pipeline.Events.emit(
            :kernel,
            :final_core_violation,
            %{clause: d.clause, message: d.message},
            %{}
          )
        end

        :ok

      rejections ->
        {:error, {:final_core_violation, rejections}}
    end
  end

  @doc """
  Re-run the totality decision procedure on a registered, type-checked global
  and, if it passes, certify it for δ-reduction (design spec §7). Coverage is
  re-checked by `check_def` (the kernel's `case` typing); termination by
  `Cure.Core.Certificate`. The kernel never trusts an elaborator's verdict — it
  re-derives certification itself, returning the signature with the global
  marked certified (the only way the certified set is populated).
  """
  @spec validate_certificate(Env.t(), atom()) :: {:ok, Env.t()} | {:error, term()}
  def validate_certificate(env, name) do
    # Canonicalize the lookup name to its def key BEFORE deriving the certificate.
    # A def's body refers to itself (and its siblings) by owner-qualified key, but a
    # caller may submit the bare name. `Certificate.terminating?` detects recursion by
    # matching the submitted name against the `{:global, _}` nodes in the body: a bare
    # name never matches a qualified self-reference, so an un-canonicalized name makes a
    # self-looping function look non-recursive and be certified total (unsound). Resolve
    # once here so recursion detection compares like against like.
    name = Env.resolve_key(env, env.defs, name)

    case Env.get_def(env, name) do
      # Builtin-op def (K2, R4): total by fiat, no body to submit to the
      # termination checker. Type-check the declared type, then certify.
      %{builtin_op: op} when not is_nil(op) ->
        with :ok <- check_def(env, name) do
          timed_certificate_stage(name, :termination, fn -> {:ok, Env.certify(env, name)} end)
        end

      _ ->
        with :ok <- check_def(env, name) do
          %{body: body} = Env.get_def(env, name)
          env = ensure_direct_call_summary(env, name, body)

          timed_certificate_stage(name, :termination, fn ->
            if Certificate.terminating?(name, body, env) do
              # Certify the WHOLE proven-total SCC, not just `name`. A mutual group
              # is certified member-by-member in declaration order; the first-declared
              # member defers (its sibling's body is still a pending hole) and the
              # last-declared member's check proves the group total but — before this —
              # certified only itself, leaving the earlier member opaque to δ until the
              # end-of-module sweep, which is too late for a dependent def checked in
              # between. `terminating?` being true here means `pending_callee?` was
              # false (every SCC member has a real, already-`check_def`'d body) and, for
              # a genuine group, `mutual_group_total?` proved every member terminating
              # together — so certifying them all is sound (Idris/Agda/Lean certify a
              # `mutual` block as a unit). For a non-mutual def the group is `{name}`,
              # so this is behaviour-preserving.
              certified =
                Certificate.total_group(name, body, env)
                |> Enum.reduce(env, fn m, acc -> Env.certify(acc, m) end)

              {:ok, certified}
            else
              {:error, :not_total}
            end
          end)
        end
    end
  end

  defp ensure_direct_call_summary(env, name, body) do
    summary = Certificate.direct_summary(name, body, env)

    case Env.direct_call_summary(env, name) do
      %{body_hash: hash, version: version}
      when hash == summary.body_hash and version == summary.version ->
        env

      _ ->
        Env.put_direct_call_summary(env, name, summary)
    end
  end

  @doc "Prepare trusted direct-call summaries for a finite certification universe."
  @spec prepare_direct_call_summaries(Env.t(), [atom()]) :: {:ok, Env.t()} | {:error, term()}
  def prepare_direct_call_summaries(%Env{} = env, names) when is_list(names) do
    names
    |> Enum.map(&Env.resolve_key(env, env.defs, &1))
    |> Enum.uniq()
    |> Enum.sort()
    |> Enum.reduce_while({:ok, env}, fn name, {:ok, acc} ->
      case Env.get_def(acc, name) do
        nil ->
          {:halt, {:error, {:totality_unknown_callee, %{definition: name}}}}

        %{body: body} when is_tuple(body) and elem(body, 0) not in [:extern, :hole] ->
          case check_def(acc, name) do
            :ok -> {:cont, {:ok, ensure_direct_call_summary(acc, name, body)}}
            {:error, reason} -> {:halt, {:error, reason}}
          end

        %{body: {:hole, _}} ->
          {:halt, {:error, {:totality_summary_stale, %{definition: name, reason: :pending_body}}}}

        _terminal ->
          {:cont, {:ok, acc}}
      end
    end)
  end

  @doc "Verify an SCC partition once and atomically certify selected components."
  @spec validate_scc_certificates(Env.t(), map(), [atom()]) ::
          {:ok, Env.t()} | {:error, {:not_total, [atom()]}} | {:error, term()}
  def validate_scc_certificates(%Env{} = env, partition, selected_names) do
    with {:ok, _components} <- Cure.Core.SCCCertificate.verify_partition(env, partition) do
      selected_ids =
        selected_names
        |> Enum.map(&Env.resolve_key(env, env.defs, &1))
        |> Enum.map(&Map.fetch!(partition.component_of, &1))
        |> Enum.uniq()
        |> Enum.sort_by(&Map.fetch!(partition.rank, &1))

      Enum.reduce_while(selected_ids, {:ok, env}, fn component_id, {:ok, acc} ->
        members = partition.components[component_id].members
        digest = scc_certificate_digest(partition, component_id, members)

        cond do
          Map.has_key?(acc.totality_components, digest) ->
            {:cont, {:ok, acc}}

          Certificate.terminating_group?(members, acc) ->
            {:cont, {:ok, Env.certify_component(acc, members, digest)}}

          true ->
            {:halt, {:error, {:not_total, members}}}
        end
      end)
    end
  end

  defp scc_certificate_digest(partition, component_id, members) do
    material =
      {partition.version, component_id,
       Enum.map(members, fn member ->
         {member, Map.fetch!(partition.summary_hashes, member)}
       end)}

    :crypto.hash(:sha256, :erlang.term_to_binary(material, [:deterministic]))
  end

  @doc """
  Check an indexed family declaration well-formed: parameter telescope, then
  index telescope (in the context of the parameters), each entry a valid type.
  """
  @spec check_family(Cure.Core.Env.t(), Inductive.family()) :: :ok | {:error, term()}
  def check_family(env, %{params: params, indices: indices} = family) do
    base = Context.empty(env)

    with :ok <- check_family_level(Map.get(family, :level, 0)),
         {:ok, ctx_params} <- check_telescope(base, params),
         {:ok, _ctx} <- check_telescope(ctx_params, indices) do
      :ok
    end
  end

  # The family's declared universe must lie within the fixed predicative ceiling
  # (`Type0 : Type1 : Type2`); a family at `Type k > ceiling` contradicts the
  # hierarchy the rest of the kernel enforces (`Universe.succ`, `subtype?`).
  defp check_family_level(level)
       when is_integer(level) and level >= 0 and level <= @universe_ceiling,
       do: :ok

  defp check_family_level(_level), do: {:error, :universe_ceiling}

  @doc """
  Check a constructor well-formed against its family (§4.4): argument telescope
  well-typed; the family's declared level dominates every field type's level
  (the two-universe rule); the result indices match the family index telescope
  in count (`:index_arity`) and in type (evaluating computed indices via NbE).
  """
  @spec check_ctor(Cure.Core.Env.t(), Inductive.family(), Inductive.ctor()) ::
          :ok | {:error, term()}
  def check_ctor(env, %{name: fname, params: params, indices: index_tele, level: fam_level}, ctor) do
    %{args: args, result_indices: result_indices} = ctor
    result_params = Map.get(ctor, :result_params, [])

    with {:ok, ctx_params} <- check_telescope(Context.empty(env), params),
         {:ok, ctx_full, field_levels} <- check_ctor_args(ctx_params, args),
         :ok <- check_field_levels(field_levels, fam_level),
         :ok <-
           check_uniform_params(fname, ctor.name, result_params, length(params), length(args)),
         :ok <-
           check_result_indices(ctx_full, Context.env(ctx_params), result_indices, index_tele) do
      :ok
    end
  end

  # Each result parameter must be exactly the family's corresponding parameter
  # variable, as a de Bruijn var in ctx_full = params(outer) ++ args(inner): the
  # p-th declared parameter is {:var, num_args + (num_params - 1 - p)}. A ctor
  # that writes anything else in a parameter position (a non-uniform parameter)
  # is rejected — that position would have to be refined by matching, which is
  # index behaviour, not parameter behaviour.
  defp check_uniform_params(fname, cname, result_params, num_params, num_args) do
    cond do
      length(result_params) != num_params ->
        {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: :arity}}}

      true ->
        result_params
        |> Enum.with_index()
        |> Enum.reduce_while(:ok, fn {term, p}, :ok ->
          expected = {:var, num_args + (num_params - 1 - p)}

          if term == expected,
            do: {:cont, :ok},
            else: {:halt, {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: p}}}}
        end)
    end
  end

  # -- helpers ----------------------------------------------------------------

  # Infer `term` and require its type to be a universe; return that level.
  defp infer_sort(ctx, term) do
    with {:ok, type_value} <- infer(ctx, term) do
      case type_value do
        {:vtype, level} -> {:ok, level}
        _ -> {:error, :not_a_type}
      end
    end
  end

  # Require a type value to be a Π; return its domain value + codomain closure.
  defp ensure_pi({:vpi, _g, dom, cod_closure}), do: {:ok, dom, cod_closure}
  defp ensure_pi(_), do: {:error, :not_a_function}

  # Require a (whnf'd) type value to be `Effect(A)`; return `A`. `tag` names the
  # position so a `bind` failure reports which side was not an effect.
  defp ensure_effect({:veffect_type, a}, _tag), do: {:ok, a}
  defp ensure_effect(_value, tag), do: {:error, tag}

  # Require two type values convertible; `:ok` or a tagged error. Grades/types
  # are compared by `Conv` (definitional equality), never a preorder.
  defp ensure_conv(v1, v2, depth, sig, tag) do
    if Conv.conv_values?(v1, v2, depth, sig), do: :ok, else: {:error, tag}
  end

  # Check `args` against a dependent telescope, threading each evaluated arg so
  # later telescope types can depend on earlier args. Returns the arg values
  # (most-recent first) so a caller can continue (e.g. params then indices).
  defp check_spine(ctx, args, tele, init_vals) do
    if length(args) == length(tele) do
      do_spine(ctx, Enum.zip(args, tele), init_vals)
    else
      {:error, :arg_arity}
    end
  end

  defp do_spine(_ctx, [], vals), do: {:ok, vals}

  defp do_spine(ctx, [{arg, {_name, type_term}} | rest], vals) do
    expected = Eval.eval(type_term, vals)

    case check_field(ctx, arg, expected) do
      {:ok, arg_val} -> do_spine(ctx, rest, [arg_val | vals])
      {:error, _} = err -> err
    end
  end

  # Check a spine field and return its VALUE. For a constructor field the value is
  # assembled bottom-up from the recursively-checked sub-fields (no re-eval of the
  # surface tower — the O(n²)→O(n) fix; see `elaborate_ctor`). Every other field
  # (or a ctor whose goal is not a data type) uses the ordinary `check` plus a
  # single `eval`; such fields are leaves of the spine recursion, so that eval is
  # not re-entered per level. The returned value equals `Eval.eval(arg, env)`.
  defp check_field(ctx, {:ctor, cname, args}, {:vdata, _f, _c} = expected) do
    elaborate_ctor(ctx, cname, args, expected)
  end

  defp check_field(ctx, arg, expected) do
    with :ok <- check(ctx, arg, expected) do
      {:ok, Eval.eval(arg, Context.env(ctx))}
    end
  end

  # Telescope well-formedness: each entry is a valid type; returns the context
  # extended by the whole telescope.
  defp check_telescope(ctx, []), do: {:ok, ctx}

  defp check_telescope(ctx, [{_name, type_term} | rest]) do
    with {:ok, _level} <- infer_sort(ctx, type_term) do
      type_value = Eval.eval(type_term, Context.env(ctx))
      check_telescope(Context.extend(ctx, type_value), rest)
    end
  end

  # Like check_telescope but also collects each field type's universe level.
  defp check_ctor_args(ctx, args) do
    Enum.reduce_while(args, {:ok, ctx, []}, fn {_name, type_term}, {:ok, c, levels} ->
      case infer_sort(c, type_term) do
        {:ok, level} ->
          c2 = Context.extend(c, Eval.eval(type_term, Context.env(c)))
          {:cont, {:ok, c2, [level | levels]}}

        err ->
          {:halt, err}
      end
    end)
  end

  defp check_field_levels(levels, fam_level) do
    if Enum.all?(levels, &(&1 <= fam_level)), do: :ok, else: {:error, :universe_level}
  end

  # Check a constructor application's args against its telescope (dependent),
  # returning the accumulated arg values (most-recent first) for result-index
  # computation. A failure on a data-typed argument is an index disagreement.
  # Returns `{:ok, arg_env, field_vals}`: `arg_env` is the accumulated values
  # (params-most-recent-first, for result-index computation) exactly as before;
  # `field_vals` is the fields in surface order, so a caller can assemble the
  # constructor value without re-evaluating the surface spine.
  defp check_ctor_app(ctx, param_vals, args, tele) do
    if length(args) == length(tele) do
      # Seed the local evaluation environment with the family's actual parameter
      # values (most-recent-first, mirroring check_ctor's ctx_full = params ++
      # args numbering) so a ctor arg whose declared type references a parameter
      # (e.g. `prepend`'s `x : a`) resolves to the real parameter, not a bogus
      # out-of-range neutral.
      check_ctor_app_rec(ctx, Enum.zip(args, tele), Enum.reverse(param_vals), [])
    else
      {:error, :ctor_arity}
    end
  end

  defp check_ctor_app_rec(_ctx, [], vals, fields), do: {:ok, vals, Enum.reverse(fields)}

  defp check_ctor_app_rec(ctx, [{arg, {_name, type_term}} | rest], vals, fields) do
    expected = Eval.eval(type_term, vals)

    # Thread the field's value UP from its own check instead of re-evaluating the
    # surface sub-term here (`Eval.eval(arg, env)`), which made a depth-n tower
    # O(n²). `check_field` returns exactly that value, so `vals` is unchanged.
    case check_field(ctx, arg, expected) do
      {:ok, arg_val} -> check_ctor_app_rec(ctx, rest, [arg_val | vals], [arg_val | fields])
      {:error, _} = err -> remap_index_error(err, expected)
    end
  end

  # A mismatch on a constructor argument whose expected type is a family value is
  # an index disagreement (the kernel-level backstop; the elaborator surfaces the
  # user-facing :index_unification earlier — see plan M3.4/M8.4).
  #
  # The category alone is not a diagnosis. This branch fires for every way a field
  # can fail against a family — a constructor of some other family, an undefined
  # global, a conversion failure — and reporting them all as a bare
  # `:index_mismatch` erases the one fact an author needs. For core the elaborator
  # never checked (a macro expansion goes to the kernel directly), this branch IS
  # the whole diagnosis, so the family and the underlying rejection travel with it.
  defp remap_index_error({:error, cause}, {:vdata, name, _args}),
    do: {:error, {:index_mismatch, {:in_field_of, name, cause}}}

  defp remap_index_error(err, _expected), do: err

  # Assemble a constructor's RESULT type value by evaluating its result params and
  # indices in the accumulated field/param environment (`arg_env`, most-recent
  # first). The single owner of the `{:vdata, family, result_params ++
  # result_indices}` shape shared by the inference-mode ctor rule and
  # checking-mode `elaborate_ctor`; a computed index reduces once δ is available.
  defp result_vdata(arg_env, family, ctor_sig) do
    result_params = Map.get(ctor_sig, :result_params, [])
    result_indices = Map.get(ctor_sig, :result_indices, [])
    param_values = Enum.map(result_params, &Eval.eval(&1, arg_env))
    index_values = Enum.map(result_indices, &Eval.eval(&1, arg_env))
    {:vdata, family, param_values ++ index_values}
  end

  # -- dependent case (§4.4) --------------------------------------------------

  # Apply a (curried) motive value to a list of argument values. Callers below
  # use this only AFTER `check_motive_wf` has validated the motive is a function
  # of the right shape (`apply_motive_checked` is the validating gate).
  defp apply_motive(motive_value, args), do: Eval.apply_spine(motive_value, args)

  # Like `apply_motive`, but on the UNvalidated motive supplied by the (untrusted)
  # elaborator: if some prefix reduces to a non-function while arguments remain,
  # the motive is ill-formed — return `{:error, :bad_motive}` rather than crashing
  # `Eval.apply` on a non-function value.
  defp apply_motive_checked(motive_value, args) do
    Enum.reduce_while(args, {:ok, motive_value}, fn arg, {:ok, acc} ->
      case acc do
        {:vlam, _, _, _} -> {:cont, {:ok, Eval.apply(acc, arg)}}
        {:vneutral, _} -> {:cont, {:ok, Eval.apply(acc, arg)}}
        _ -> {:halt, {:error, :bad_motive}}
      end
    end)
  end

  # Extend `ctx` by a (dependent) telescope; return the new context and the fresh
  # neutral values bound for each telescope variable, in declaration order.
  #
  # `param_vals` seeds the *isolated* local evaluation environment for `tele`'s
  # own type terms (mirroring check_ctor's ctx_full = params ++ args numbering) —
  # NOT the ambient `ctx`, which has an unrelated numbering. Each entry may still
  # reference earlier entries of the same `tele` (threaded via the same local
  # list). `ctx` is extended in parallel purely to keep the ambient context's
  # depth/levels consistent for whatever uses the returned context afterward
  # (e.g. checking a branch body, which IS written relative to the ambient ctx).
  defp extend_with_telescope(ctx, tele, param_vals) do
    {ctx_final, _local_vals, fresh_vals} =
      Enum.reduce(tele, {ctx, Enum.reverse(param_vals), []}, fn {_name, type_term}, {c, local_vals, fresh} ->
        level = Context.length(c)
        type_value = Eval.eval(type_term, local_vals)
        fresh_val = {:vneutral, {:nvar, level}}
        {Context.extend(c, type_value), [fresh_val | local_vals], fresh ++ [fresh_val]}
      end)

    {ctx_final, fresh_vals}
  end

  # The motive must be a type family over the family's indices and the scrutinee:
  # applied to fresh indices ȷ̄ and x : D p̄ ȷ̄, its body must itself be a type.
  # The scrutinee's actual parameters (`scrut_params`) are fixed context: they
  # seed the index telescope's own evaluation (an index type may mention a
  # parameter) and fill the parameter slots of the scrutinee's data value. Values
  # in this NbE representation reference free variables by absolute de Bruijn
  # LEVEL, so `scrut_params` need no shift as more binders are added.
  defp check_motive_wf(ctx, motive_value, %{name: dname, indices: index_tele}, scrut_params) do
    {ctx_indices, index_vals} = extend_with_telescope(ctx, index_tele, scrut_params)
    scrut_level = Context.length(ctx_indices)
    data_value = {:vdata, dname, scrut_params ++ index_vals}
    ctx_motive = Context.extend(ctx_indices, data_value)
    x_value = {:vneutral, {:nvar, scrut_level}}

    with {:ok, body_value} <- apply_motive_checked(motive_value, index_vals ++ [x_value]),
         {:ok, _level} <- infer_type_value_sort(ctx_motive, body_value) do
      :ok
    else
      _ -> {:error, :bad_motive}
    end
  end

  defp infer_type_value_sort(_ctx, {:vtype, level}), do: Universe.succ(level)

  # A neutral is a valid type of sort `sublevel` iff its own declared type in
  # `ctx` is itself `{:vtype, sublevel}` — i.e. the variable it stands for was
  # bound at a universe (e.g. a parameter `a : Type` used polymorphically as the
  # case result type). de Bruijn index of a level-`level` neutral is
  # `Context.length(ctx) - 1 - level`.
  defp infer_type_value_sort(ctx, {:vneutral, {:nvar, level}}) do
    idx = Context.length(ctx) - 1 - level

    case Context.lookup(ctx, idx) do
      {:vtype, sublevel} -> {:ok, sublevel}
      _ -> {:error, :not_a_type_value}
    end
  end

  # A neutral APPLICATION is a valid type iff the kernel's own term-level
  # judgement says so: reify the spine back to a term (signature-aware, so a
  # {:vdata,…} argument keeps its param/index split — quote.ex split_data_args)
  # and infer it. infer/2's {:app, f, a} rule resolves the head's type (ctx var
  # or signature global), CHECKS each argument against the instantiated Pi
  # domain, and returns the codomain — full validation, nothing trusted from
  # the (untrusted) elaborator that assembled the motive. Accept only a
  # {:vtype, l} result: `b(first(p))` with `b : (a) -> Type` sorts at l; a
  # non-type codomain stays :not_a_type_value.
  defp infer_type_value_sort(ctx, {:vneutral, {:napp, _, _} = neutral}) do
    term = Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))

    case infer(ctx, term) do
      {:ok, {:vtype, level}} -> {:ok, level}
      _ -> {:error, :not_a_type_value}
    end
  end

  # A bare neutral GLOBAL used in type position — e.g. a `typealias String =
  # List(Char)` appearing as a `match`/dispatch result type — is a valid type of
  # sort `level` iff the kernel's own term-level judgement says so. Same trust
  # discipline as the `{:napp}` clause above: reify the neutral back to a
  # `{:global, g}` term and `infer` it, resolving `g`'s declared type from the
  # signature; accept only a `{:vtype, l}` result. A typealias is a nullary def
  # `g : Type := RHS`, so its declared type is a universe and this admits it as a
  # motive body — without this clause a constant motive `λ_. String` (and every
  # abstract interface method returning an aliased type) is a spurious
  # `:bad_motive`, since `infer_type_value_sort` had no clause for `{:nglobal, _}`.
  defp infer_type_value_sort(ctx, {:vneutral, {:nglobal, _} = neutral}) do
    term = Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))

    case infer(ctx, term) do
      {:ok, {:vtype, level}} -> {:ok, level}
      _ -> {:error, :not_a_type_value}
    end
  end

  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:vint_type}`
  # value; fresh elaboration never produces one (spec 2026-07-18 §3a).
  defp infer_type_value_sort(_ctx, {:vint_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vfloat_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vbinary_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vatom_type}), do: {:ok, 0}

  defp infer_type_value_sort(ctx, {:vdata, name, _args}) do
    case Inductive.get_family(Context.signature(ctx), name) do
      nil -> {:error, {:unknown_family, name}}
      %{level: level} -> {:ok, level}
    end
  end

  # Π/Σ/Eq value clauses recurse on the sub-VALUES directly, mirroring `infer/2`'s
  # type-formation rules for the corresponding terms, instead of reifying and
  # re-inferring. `Quote.reify` collapses `{:vdata, name, args}` → `{:data, name,
  # args, []}` (it has no inductive signature to recover the param/index split), so
  # reifying a Π/Σ/Eq whose domain (or Eq carrier) is an INDEXED family loses the
  # split and re-inference fails with `:arg_arity` — a false `:bad_motive`. The
  # value-recursion is a faithful mirror: it bottoms out in the same
  # `infer_type_value_sort` clauses (including the direct `{:vdata,…}` clause that
  # already classifies bare indexed-family motive RESULTS), so acceptance is
  # exactly what a non-lossy reify+infer would decide, and a non-type domain still
  # falls through to `:not_a_type_value` (rejected, no false positives).
  defp infer_type_value_sort(ctx, {:vpi, _g, dom, cod_closure}) do
    with {:ok, l1} <- infer_type_value_sort(ctx, dom) do
      fresh = {:vneutral, {:nvar, Context.length(ctx)}}
      cod_value = Eval.apply_closure(cod_closure, fresh)

      with {:ok, l2} <- infer_type_value_sort(Context.extend(ctx, dom), cod_value) do
        {:ok, Universe.max(l1, l2)}
      end
    end
  end

  # `Effect(t)` in type position — a `case`/`match` whose result type is a callback's
  # effect contract. Mirrors `infer/2`'s formation rule (`Effect : Type ℓ → Type ℓ`,
  # level-preserving): the head contributes nothing, so the sort is the payload's own.
  # Recursing on the sub-VALUE rather than reifying is deliberate, for the same reason
  # the `{:vpi}` clause does it: `Quote.reify` collapses `{:vdata, name, args}` →
  # `{:data, name, args, []}`, losing the param/index split, so reify+re-infer would
  # turn an indexed payload like `Effect(SNat s)` into a false `:arg_arity` →
  # `:bad_motive`. Bottoming out in the existing clauses keeps acceptance exactly what
  # a non-lossy reify+infer would decide: a payload that is not a type still falls to
  # `:not_a_type_value`, so an `Effect` head cannot launder a non-type.
  defp infer_type_value_sort(ctx, {:veffect_type, payload}) do
    infer_type_value_sort(ctx, payload)
  end

  defp infer_type_value_sort(_ctx, _value), do: {:error, :not_a_type_value}

  # Coverage (§7 / §E.2): every declared constructor must either HAVE a branch or
  # be provably IMPOSSIBLE at the scrutinee's actual indices (index-unification
  # failure). Omitting a constructor that could still match is a coverage error;
  # omitting one the kernel certifies impossible is the Agda/Idris index-
  # contradiction discipline — and is exactly what lets a provably-uninhabited
  # scrutinee be eliminated by an empty branch list (ex-falso, K4/§H), with no
  # `{:absurd}` term. Relies on `:impossible` being the certain non-unification
  # verdict (K5a-hardened): a merely `:undecided` omission is NOT accepted.
  defp check_coverage(ctx, sig, dname, branches, scrut_indices, scrut_params, scrut_value) do
    covered = branches |> Enum.map(fn {c, _ar, _b} -> c end) |> MapSet.new()

    uncovered =
      sig
      |> Inductive.ctors_of(dname)
      |> Enum.reject(fn c -> MapSet.member?(covered, c.name) end)

    known_ctor =
      case scrut_value do
        {:vctor, cname, _args} -> cname
        _ -> nil
      end

    if Enum.all?(uncovered, fn c ->
         (known_ctor != nil and c.name != known_ctor) or
           unify_indices(ctx, c.result_indices, scrut_indices, length(c.args), scrut_params) ==
             :impossible
       end),
       do: :ok,
       else: {:error, :coverage}
  end

  # Each branch body is checked under its constructor's telescope, against the
  # motive instantiated at that constructor's computed indices s̄ⱼ and value cⱼ āⱼ.
  # A branch must name a constructor of the scrutinee's OWN family `dname`; a
  # constructor of any other family is ill-formed (it can never match), so it is
  # rejected before its body is checked (`:foreign_ctor`).
  defp check_case_branches(
         ctx,
         sig,
         dname,
         motive_value,
         branches,
         scrut_indices,
         scrut_params,
         scrut_value
       ) do
    result =
      Enum.reduce_while(branches, :ok, fn {cname, arity, body}, status ->
        case Inductive.get_ctor(sig, cname) do
          nil ->
            {:halt, {:error, {:unknown_ctor, cname}}}

          ctor ->
            cond do
              Inductive.ctor_family(sig, cname) != dname ->
                {:halt, {:error, {:foreign_ctor, cname}}}

              length(ctor.args) != arity ->
                {:halt, {:error, :branch_arity}}

              true ->
                %{args: tele, result_indices: result_indices} = ctor
                {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele, scrut_params)

                verdict =
                  ctx
                  |> unify_indices(result_indices, scrut_indices, arity, scrut_params)
                  |> validate_branch_substitution(ctx_branch)

                case verdict do
                  :impossible ->
                    # unreachable branch: body NOT checked
                    {:cont, status}

                  verdict ->
                    subst =
                      case verdict do
                        {:solved, s} -> s
                        :trivial -> %{}
                      end

                    subst = merge_known_branch_args(subst, scrut_value, cname, arity, Context.length(ctx))

                    ctx_branch = specialize_branch_context(ctx_branch, subst)
                    # Result indices are written over the ctor frame `params(outer) ++
                    # args(inner)` (see check_uniform_params), so the eval env is
                    # reverse(arg_vals) ++ reverse(scrut_params). Omitting the params
                    # made a result index that references a family PARAMETER (e.g.
                    # `MkBar : Bar n n`) resolve to a stray out-of-range neutral.
                    s_values =
                      Enum.map(
                        result_indices,
                        &Eval.eval(&1, Enum.reverse(arg_vals) ++ Enum.reverse(scrut_params))
                      )

                    ctor_value = {:vctor, cname, arg_vals}

                    expected =
                      motive_value
                      |> apply_motive(s_values ++ [ctor_value])
                      |> specialize_branch_value(ctx_branch, subst)

                    case check(ctx_branch, body, expected) do
                      :ok ->
                        record_branch_detail(cname, body, ctx_branch, expected, :ok)
                        {:cont, status}

                      {:error, _} = error ->
                        if branch_detail_active?() do
                          record_branch_detail(cname, body, ctx_branch, expected, {:error, error})
                          {:cont, :branch_type_seen}
                        else
                          {:halt, {:error, :branch_type}}
                        end
                    end
                end
            end
        end
      end)

    case result do
      :branch_type_seen -> {:error, :branch_type}
      other -> other
    end
  end

  defp branch_detail_active? do
    match?({:active, _}, Process.get({__MODULE__, :branch_details}))
  end

  defp record_branch_detail(cname, body, ctx, expected, status) do
    case Process.get({__MODULE__, :branch_details}) do
      {:active, details} ->
        actual =
          case status do
            :ok ->
              expected

            {:error, _error} ->
              case infer(ctx, body) do
                {:ok, value} -> value
                _ -> nil
              end
          end

        Process.put(
          {__MODULE__, :branch_details},
          {:active, [%{constructor: cname, actual: actual, expected: expected, status: status} | details]}
        )

      _ ->
        :ok
    end
  end

  defp merge_known_branch_args(subst, {:vctor, cname, args}, cname, arity, depth)
       when length(args) == arity do
    args
    |> Enum.with_index()
    |> Enum.reduce(subst, fn {value, p}, acc ->
      term = value |> Quote.reify(depth) |> Term.shift(arity, 0)
      ctor_key = arity - 1 - p

      case term do
        {:var, outer_key} -> Map.put(acc, outer_key, {:var, ctor_key})
        closed -> Map.put(acc, ctor_key, closed)
      end
    end)
  end

  defp merge_known_branch_args(subst, _value, _cname, _arity, _depth), do: subst

  @doc """
  Public branch-refinement query (spec §3). Given the caller's `ctx`, the
  scrutinee's family `dname` and a branch constructor `cname`, plus the
  scrutinee's actual index **values** `scrut_indices`, return the same verdict
  `unify_indices/4` produces: `{:solved, subst} | :trivial | :impossible`, where
  `subst` is in the branch de Bruijn frame `ctor-args ++ outer`. The elaborator
  delegates to this instead of carrying its own weaker index unification. Adds no
  unification logic — it reuses the private `unify_indices/4`. Guards two misuse
  shapes rather than trusting the caller: an unknown constructor (`nil` from
  `get_ctor`) and a constructor that exists but belongs to a different family
  than `dname` (`Inductive.ctor_family/2` mismatch) both verdict `:impossible`
  rather than proceeding against the wrong schema. Both are impossible in
  practice given the elaborator's own pre-validation, but this is new trusted-
  kernel code and `dname` is part of the signature precisely to be checked, not
  merely documented.
  """
  @spec branch_unify(Context.t(), atom(), atom(), [Cure.Core.Value.t()]) ::
          {:solved, map()} | :trivial | :impossible
  def branch_unify(ctx, dname, cname, scrut_indices),
    do: branch_unify(ctx, dname, cname, scrut_indices, [])

  @doc """
  Like `branch_unify/4`, but takes the scrutinee's actual family parameter VALUES
  so a constructor whose result indices reference a family parameter (a GADT such
  as `MkFoo : Foo a [a]`) unifies against the real params instead of a bare param
  var that collides with a shifted scrutinee index. `branch_unify/4` is the
  paramless specialisation (`scrut_params = []`); every caller over an indexed
  family with parameters MUST use this arity.
  """
  @spec branch_unify(Context.t(), atom(), atom(), [Cure.Core.Value.t()], [Cure.Core.Value.t()]) ::
          {:solved, map()} | :trivial | :impossible
  def branch_unify(ctx, dname, cname, scrut_indices, scrut_params) do
    sig = Context.signature(ctx)

    with %{args: tele, result_indices: result_indices} <- Inductive.get_ctor(sig, cname),
         ^dname <- Inductive.ctor_family(sig, cname) do
      verdict = unify_indices(ctx, result_indices, scrut_indices, length(tele), scrut_params)
      {branch_ctx, _fresh} = extend_with_telescope(ctx, tele, scrut_params)
      validate_branch_substitution(verdict, branch_ctx)
    else
      _ -> :impossible
    end
  end

  # First-order index unification is deliberately conservative and operates on
  # reified terms. Nested dependent matches can present a neutral level through
  # more than one contextual spelling; a numeric de Bruijn key is not sufficient
  # evidence that the corresponding context slot has the index's type. Before a
  # substitution is allowed to rewrite the branch context, re-check every entry
  # in the actual branch frame. Dropping an ill-typed entry is conservative (the
  # branch stays less refined); applying one would corrupt an unrelated binder.
  defp validate_branch_substitution({:solved, subst}, branch_ctx) do
    valid =
      Enum.reduce(subst, %{}, fn {key, replacement}, acc ->
        expected = Context.lookup(branch_ctx, key)
        inferred = infer(branch_ctx, replacement)

        case {expected, inferred} do
          {nil, _} ->
            acc

          {expected, {:ok, actual}} ->
            if definitely_distinct_type_heads?(actual, expected),
              do: acc,
              else: Map.put(acc, key, replacement)

          # An application can fail ordinary inference at an argument before the
          # checker reaches its result type.  That is exactly the dangerous case
          # here: an untyped first-order index equation may have confused a proof
          # binder with an index binder, so the replacement is already malformed.
          # Peel only declared Π codomains, without treating this as successful
          # inference.  A distinct rigid result head is enough to REJECT the
          # substitution; every uncertain/same-head case remains conservatively
          # retained and is checked normally by the eventual branch body.
          {expected, {:error, _}} ->
            case infer_application_result_shape(branch_ctx, replacement) do
              {:ok, actual} ->
                if definitely_distinct_type_heads?(actual, expected),
                  do: acc,
                  else: Map.put(acc, key, replacement)

              _ ->
                Map.put(acc, key, replacement)
            end
        end
      end)

    if map_size(valid) == 0, do: :trivial, else: {:solved, valid}
  end

  defp validate_branch_substitution(verdict, _branch_ctx), do: verdict

  defp definitely_distinct_type_heads?({:vdata, left, _}, {:vdata, right, _}),
    do: left != right

  defp definitely_distinct_type_heads?({:vtype, _}, {:vdata, _, _}), do: true
  defp definitely_distinct_type_heads?({:vdata, _, _}, {:vtype, _}), do: true
  defp definitely_distinct_type_heads?({:vpi, _, _, _}, {:vdata, _, _}), do: true
  defp definitely_distinct_type_heads?({:vdata, _, _}, {:vpi, _, _, _}), do: true
  defp definitely_distinct_type_heads?({:vpi, _, _, _}, {:vtype, _}), do: true
  defp definitely_distinct_type_heads?({:vtype, _}, {:vpi, _, _, _}), do: true
  defp definitely_distinct_type_heads?(_actual, _expected), do: false

  @doc false
  @spec infer_application_result_shape(Context.t(), Cure.Core.Term.t()) ::
          {:ok, Cure.Core.Value.t()} | :unknown
  def infer_application_result_shape(ctx, term) do
    {head, args} = application_spine(term, [])

    with {:ok, head_type} <- infer(ctx, head) do
      Enum.reduce_while(args, {:ok, head_type}, fn arg, {:ok, current} ->
        case ensure_pi(Normalise.whnf_value(current, Context.signature(ctx))) do
          {:ok, _domain, codomain} ->
            # Deliberately do not check the argument here. This helper is only a
            # negative filter after ordinary inference has failed; evaluating an
            # argument lets a dependent codomain compute, but never certifies it.
            value = Eval.eval(arg, Context.env(ctx))
            {:cont, {:ok, Eval.apply_closure(codomain, value)}}

          _ ->
            {:halt, :unknown}
        end
      end)
    else
      _ -> :unknown
    end
  rescue
    RuntimeError -> :unknown
  end

  defp application_spine({:app, fun, arg}, args), do: application_spine(fun, [arg | args])
  defp application_spine(head, args), do: {head, args}

  # Bidirectional first-order unification of a constructor's result-index vector
  # (`result_indices`, terms over the ctor telescope — vars < arity) against the
  # scrutinee's index vector (`scrut_indices`, outer-context values) in ctx_branch's
  # de Bruijn space (spec §4.3/§4.4). Verdict: {:solved, subst} | :trivial | :impossible.
  # :impossible fires on a definite rigid index-head clash or a same-key merge
  # conflict; uncertainty is always :undecided (never :impossible).
  defp unify_indices(ctx, result_indices, scrut_indices, arity, scrut_params) do
    # Index-vector arity is fixed by the family, so a length mismatch is a
    # definite non-unification — NOT something to silently truncate. `Enum.zip`
    # drops the tail of the longer list, which would ignore a surplus/missing
    # index and spuriously verdict :trivial/:solved (#573). Guard it first.
    if length(result_indices) != length(scrut_indices) do
      :impossible
    else
      outer_depth = Context.length(ctx)
      sig = Context.signature(ctx)

      # Instantiate the ctor's PARAMETER slots with the scrutinee's actual params
      # before unifying. Result indices are written in the ctor frame
      # `args(inner) ++ params(outer)`, so the p-th declared param is de Bruijn
      # `arity + pc - 1 - p` (`check_uniform_params`). Left as bare vars, a param
      # buried in a result-index spine (`MkFoo : Foo a [a]`) lands in `[arity, …)`
      # — the SAME range a scrutinee index var shifts into — and the occurs/Cycle
      # rule mistakes the two distinct variables for a cyclic self-occurrence,
      # spuriously verdicting `:impossible`. That let an empty `case` on an
      # inhabited indexed family pass coverage (ex-falso). Substituting the real
      # params removes every bare param var, restoring the "r-side unknowns <
      # arity, everything else outer" disjointness the unifier relies on.
      result_indices
      |> instantiate_branch_result_indices(arity, scrut_params, outer_depth)
      |> Enum.zip(scrut_indices)
      |> Enum.map(fn {r, s_val} ->
        # Coverage/branch-typing is up to DEFINITIONAL EQUALITY: unify the ctor's
        # index `r` against the NORMAL FORM of the scrutinee's index, not its
        # stuck form. A dependent sibling refined per branch (via `with`) can
        # present its index as a stuck neutral — `plus(S(k), m)` rather than
        # `S(plus(k, m))` — and unifying `Z` (an impossible branch's index)
        # against that stuck `plus(...)` fails to refute it, keeping a branch the
        # eliminator legitimately omits and rejecting a total function as
        # non-exhaustive. Normalizing strengthens the refutation (a reducible
        # index gains its constructor head) and never weakens it (an already-nf
        # or genuinely-stuck index is unchanged). `nf` in the outer frame, then
        # shift into the ctor frame. Fail-safe on fuel exhaustion.
        s_term = Quote.reify(s_val, outer_depth)

        s_norm =
          case Normalise.nf(ctx, s_term) do
            :fuel_exhausted -> s_term
            nf -> nf
          end

        align_index_ctor_spines(r, Term.shift(s_norm, arity, 0), sig)
      end)
      |> reduce_index_pairs(%{}, arity, sig)
    end
  end

  @doc false
  @spec instantiate_branch_result_indices(
          [Cure.Core.Term.t()],
          non_neg_integer(),
          [Cure.Core.Value.t()],
          non_neg_integer()
        ) :: [Cure.Core.Term.t()]
  def instantiate_branch_result_indices(result_indices, arity, scrut_params, outer_depth) do
    pc = length(scrut_params)

    pmap =
      scrut_params
      |> Enum.with_index()
      |> Map.new(fn {pval, p} ->
        {arity + pc - 1 - p, pval |> Quote.reify(outer_depth) |> Term.shift(arity, 0)}
      end)

    Enum.map(result_indices, &subst_params(&1, pmap, 0))
  end

  # A checked constructor can occur with every inferred leading slot present or
  # with those slots omitted because its expected indexed family determines
  # them. Align the two spellings PAIRWISE: implicit fields remain available for
  # GADT refinement when both sides carry them, while a licensed unequal prefix
  # cannot block propagation through a repeated index equation.
  defp align_index_ctor_spines({:ctor, cname, left}, {:ctor, cname, right}, sig) do
    {left, right} = Inductive.align_ctor_spines(sig, cname, left, right)

    if length(left) == length(right) do
      {left, right} = align_index_spine_lists(left, right, sig)
      {{:ctor, cname, left}, {:ctor, cname, right}}
    else
      {{:ctor, cname, left}, {:ctor, cname, right}}
    end
  end

  defp align_index_ctor_spines({:data, name, lp, li}, {:data, name, rp, ri}, sig)
       when length(lp) == length(rp) and length(li) == length(ri) do
    {lp, rp} = align_index_spine_lists(lp, rp, sig)
    {li, ri} = align_index_spine_lists(li, ri, sig)
    {{:data, name, lp, li}, {:data, name, rp, ri}}
  end

  defp align_index_ctor_spines({:app, lf, la}, {:app, rf, ra}, sig) do
    {lf, rf} = align_index_ctor_spines(lf, rf, sig)
    {la, ra} = align_index_ctor_spines(la, ra, sig)
    {{:app, lf, la}, {:app, rf, ra}}
  end

  defp align_index_ctor_spines(left, right, _sig), do: {left, right}

  defp align_index_spine_lists(left, right, sig) do
    Enum.zip(left, right)
    |> Enum.map(fn {a, b} -> align_index_ctor_spines(a, b, sig) end)
    |> Enum.unzip()
  end

  # Simultaneous, capture-avoiding substitution of the constructor's parameter
  # de Bruijn slots (keys in `pmap`, in the un-shifted result-index frame) with
  # the scrutinee's actual param terms. Unlike `replace_branch_vars`, which CHASES
  # var→var chains (a union-find substitution), replacements here are taken
  # verbatim — a param may be a bare outer var that must NOT be re-resolved as if
  # it were another param slot. Under a binder introducing `d` vars, both the keys
  # (via `k - depth`) and the replacements (shifted by `depth`) move accordingly.
  defp subst_params({:var, k}, pmap, depth) do
    case Map.get(pmap, k - depth) do
      nil -> {:var, k}
      repl -> Term.shift(repl, depth, 0)
    end
  end

  defp subst_params({:pi, g, d, c}, pmap, depth),
    do: {:pi, g, subst_params(d, pmap, depth), subst_params(c, pmap, depth + 1)}

  defp subst_params({:lam, g, d, b}, pmap, depth),
    do: {:lam, g, subst_params(d, pmap, depth), subst_params(b, pmap, depth + 1)}

  defp subst_params({:app, f, a}, pmap, depth),
    do: {:app, subst_params(f, pmap, depth), subst_params(a, pmap, depth)}

  defp subst_params({:data, n, ps, is}, pmap, depth),
    do: {:data, n, Enum.map(ps, &subst_params(&1, pmap, depth)), Enum.map(is, &subst_params(&1, pmap, depth))}

  defp subst_params({:ctor, n, as}, pmap, depth),
    do: {:ctor, n, Enum.map(as, &subst_params(&1, pmap, depth))}

  defp subst_params({:case, s, m, brs}, pmap, depth),
    do:
      {:case, subst_params(s, pmap, depth), subst_params(m, pmap, depth),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, subst_params(b, pmap, depth + ar)} end)}

  defp subst_params(other, _pmap, _depth), do: other

  defp reduce_index_pairs([], subst, _arity, _sig),
    do: if(map_size(subst) == 0, do: :trivial, else: {:solved, subst})

  defp reduce_index_pairs([{r, s} | rest], subst, arity, sig) do
    # Earlier index equations can reveal a constructor hidden behind a shared
    # variable in a later equation (`x`, then `Cons(x, rest)`). Chase the current
    # substitution before pairwise spine alignment so the second equation can
    # decompose that constructor and propagate its forced outer fields.
    {r, s} =
      align_index_ctor_spines(
        replace_branch_vars(r, subst),
        replace_branch_vars(s, subst),
        sig
      )

    case unify_one(r, s, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> reduce_index_pairs(rest, subst2, arity, sig)
      # Dropping an :undecided pair (skip it, keep `subst`) is SOUND, not a bug
      # (K5a #575, proven, do NOT "fix" into propagation): the trusted case-checker
      # skips a branch body ONLY on :impossible. Dropping :undecided never yields a
      # spurious :impossible (that verdict comes solely from a rigid clash in some
      # pair), so no live branch is skipped. And the retained `subst` holds only the
      # DECIDED equations — a subset of the truth — so the branch's `expected` type is
      # specialized LESS (more general), making body-checking STRICTER. The only
      # possible effect is a false REJECTION, never a false acceptance. Propagating
      # :undecided instead would drop these valid refinements and reject MORE.
      :undecided -> reduce_index_pairs(rest, subst, arity, sig)
    end
  end

  # r-side vars are always < arity (ctor telescope); s-side vars always >= arity
  # (outer). Disjoint ranges ⇒ the solve direction is unambiguous.
  defp unify_one({:var, i}, s, arity, subst) when i < arity,
    # ctor arg := scrutinee term (Box case / prior behavior)
    do: bind_index(i, s, arity, subst)

  defp unify_one(r, {:var, j}, arity, subst) when j >= arity,
    # outer index var := ctor result index (4.3)
    do: bind_index(j, r, arity, subst)

  # Symmetric completion of the clause above — an outer index var on the LEFT.
  # The top-level r/s pairs obey the "r-side < arity, s-side >= arity" invariant,
  # but `bind_index`'s resolve-before-bind re-unify (below, ~1498) calls
  # `unify_one(old, rterm, ...)` on two PREVIOUSLY-BOUND terms whose left/right
  # positions are set by scrutinee-index processing order, not the invariant. When
  # that puts an outer var opposite a rigid term (e.g. matching `refl : Eqv(x, x)`
  # at `Eqv(S(a), S(Z()))` re-unifies `S(a) =? S(Z())`, whose spine step is
  # `a(outer) =? Z(ctor)`), the outer var lands on the left, matching NEITHER
  # clause above, and the forced equation `a := Z` was silently dropped as
  # `:undecided` — order-dependently (the mirror `Eqv(S(Z()), S(a))` bound it via
  # clause 2). This clause makes constructor injectivity decide SYMMETRICALLY,
  # mirroring Agda's symmetric Var/Solution dispatch (Rules/LHS/Unify.hs). Placed
  # AFTER clause 2 so a var/var pair with the outer var on the right still binds
  # via clause 2 unchanged; this only fires when clause 2 did not, so it converts
  # previously-dropped pairs into genuine forced bindings and decides no pair
  # differently than it already did. (spec 2026-07-18 §2, K-bug 1.)
  defp unify_one({:var, i}, s, arity, subst) when i >= arity,
    do: bind_index(i, s, arity, subst)

  # Compact Nat literal ↔ Z/S bridge (mirrors conv.ex's cross-representation
  # arms): a `{:nat_lit, n}` index is a closed canonical Nat, definitionally
  # equal to its `S`-tower, so it must unify with `Z`/`S` result indices exactly
  # as the tower form does. Peel one layer and recurse. Without this the generic
  # rigid-head clash rule below wrongly verdicts a literal index `:impossible`
  # against `S`/`Z` — a coverage soundness hole (a `case` on `Vone(0)` could omit
  # `vz`, its only inhabitant, and still pass coverage). The peel terminates: `n`
  # strictly decreases and only fires against a `:ctor`/`:nat_lit` counterpart
  # (var counterparts bind via the clauses above).
  defp unify_one({:nat_lit, a}, {:nat_lit, b}, _arity, subst),
    do: if(a == b, do: {:ok, subst}, else: :impossible)

  defp unify_one({:nat_lit, n}, {:ctor, _, _} = s, arity, subst),
    do: unify_one(nat_lit_ctor(n), s, arity, subst)

  defp unify_one({:ctor, _, _} = r, {:nat_lit, n}, arity, subst),
    do: unify_one(r, nat_lit_ctor(n), arity, subst)

  # Compact Int literal ↔ FromNat/NegativeSuccessor bridge — the exact mirror of
  # the Nat bridge above. An `{:int_lit, n}` index is a closed canonical Int
  # value, definitionally equal to `FromNat({:nat_lit, n})` (n ≥ 0) or
  # `NegativeSuccessor({:nat_lit, -n-1})` (n < 0), so it must unify with those
  # constructor result indices exactly as the explicit spelling does — otherwise
  # `head_key({:int_lit, n})` is `:int_lit`, which never equals `{:ctor, :FromNat}`
  # /`{:ctor, :NegativeSuccessor}`, and the generic rigid-head clash rule verdicts
  # a literal index `:impossible` against its own constructor form (the same
  # coverage-soundness hole the Nat/Bounded bridges close). Single-step peel; the
  # `{:nat_lit, _}` field then bridges through the Nat clauses above.
  defp unify_one({:int_lit, a}, {:int_lit, b}, _arity, subst),
    do: if(a == b, do: {:ok, subst}, else: :impossible)

  defp unify_one({:int_lit, n}, {:ctor, _, _} = s, arity, subst),
    do: unify_one(int_lit_ctor(n), s, arity, subst)

  defp unify_one({:ctor, _, _} = r, {:int_lit, n}, arity, subst),
    do: unify_one(r, int_lit_ctor(n), arity, subst)

  # Compact Bounded literal ↔ First/Next bridge — the exact mirror of the Nat
  # bridge above, and of `conv.ex`'s cross-representation arms (conv_struct?,
  # the `{:vbounded, _}` vs `{:vctor, :First/:Next, _}` clauses). A
  # `{:bounded_lit, k}` index is a closed canonical `Bounded` value,
  # definitionally equal to its k-fold `Next`-tower over `First` (Lean `Fin n`),
  # so it must unify with `First`/`Next` result indices exactly as the tower does.
  #
  # The leading `m` argument of both constructors is the ERASED implicit bound
  # (`builtins.ex`: `First/1`, `Next/2`). `conv` ignores it; so must this, or two
  # definitionally equal indices would fail to unify on a computationally
  # irrelevant argument. Keep these clauses in lock-step with conv.ex's.
  #
  # Without this bridge `head_key({:bounded_lit, k})` is `:bounded_lit`, which can
  # never equal `{:ctor, :First}`/`{:ctor, :Next}`, so the generic rigid-head clash
  # rule below verdicts a literal index `:impossible` against its own tower
  # expansion. That is a COVERAGE SOUNDNESS HOLE identical to the Nat one this
  # bridge's sibling closes: a `case` whose scrutinee index is the tower spelling
  # could omit the scrutinee's own reachable constructor and still pass
  # `check_coverage`, admitting a partial eliminator as total.
  #
  # The peel terminates: `n` strictly decreases, and only fires against a
  # `:ctor`/`:bounded_lit` counterpart (var counterparts bind via the clauses above).
  defp unify_one({:bounded_lit, a}, {:bounded_lit, b}, _arity, subst),
    do: if(a == b, do: {:ok, subst}, else: :impossible)

  defp unify_one({:bounded_lit, 0}, {:ctor, :First, [_m]}, _arity, subst), do: {:ok, subst}
  defp unify_one({:ctor, :First, [_m]}, {:bounded_lit, 0}, _arity, subst), do: {:ok, subst}

  defp unify_one({:bounded_lit, n}, {:ctor, :Next, [_m, pred]}, arity, subst) when n > 0,
    do: unify_one({:bounded_lit, n - 1}, pred, arity, subst)

  defp unify_one({:ctor, :Next, [_m, pred]}, {:bounded_lit, n}, arity, subst) when n > 0,
    do: unify_one(pred, {:bounded_lit, n - 1}, arity, subst)

  # Genuine cross-representation constructor clash: `0` is not a successor, and a
  # positive `k` is not `First`. Stated explicitly so the `:impossible` verdict is
  # derived from the VALUES rather than falling through to the generic head-key
  # clash rule, which would reach the same answer here only by coincidence.
  defp unify_one({:bounded_lit, 0}, {:ctor, :Next, [_m, _pred]}, _arity, _subst), do: :impossible
  defp unify_one({:ctor, :Next, [_m, _pred]}, {:bounded_lit, 0}, _arity, _subst), do: :impossible

  defp unify_one({:bounded_lit, n}, {:ctor, :First, [_m]}, _arity, _subst) when n > 0,
    do: :impossible

  defp unify_one({:ctor, :First, [_m]}, {:bounded_lit, n}, _arity, _subst) when n > 0,
    do: :impossible

  defp unify_one({:ctor, c, as}, {:ctor, c, bs}, arity, subst) when length(as) == length(bs),
    do: unify_spine(as, bs, arity, subst)

  # :data heads: compare the FLATTENED spine (params ++ indices); Quote.reify always
  # emits an empty `indices` list, so never split ps-vs-is (spec §4.3).
  defp unify_one({:data, n, ps, is}, {:data, n, ps2, is2}, arity, subst)
       when length(ps) + length(is) == length(ps2) + length(is2),
       do: unify_spine(ps ++ is, ps2 ++ is2, arity, subst)

  # syntactically equal → consistent
  defp unify_one(r, s, _arity, subst) when r == s, do: {:ok, subst}

  defp unify_one(r, s, _arity, _subst) do
    cond do
      # Agda Cycle rule (Rules/LHS/Unify.hs 43-44, `ifOccursStronglyRigid`): the
      # equation `x =?= v` is absurd when the datatype variable `x` occurs STRONGLY
      # RIGID in `v` (reachable through ctor/data spines only), by acyclicity of the
      # inductive. Both directions, mirroring Agda's symmetric Var/Var dispatch.
      var_cycle?(r, s) -> :impossible
      var_cycle?(s, r) -> :impossible
      # Definite rigid head clash ⇒ impossible (Conflict rule); else conservative.
      rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s) -> :impossible
      true -> :undecided
    end
  end

  # `v` (a datatype/index variable) occurs strongly rigid in `t` ⇒ `v =?= t` is a
  # cyclic, hence absurd, equation. False for a non-var LHS.
  defp var_cycle?({:var, k}, t), do: strongly_rigid_occurs?(k, t)
  defp var_cycle?(_, _), do: false

  defp unify_spine([], [], _arity, subst), do: {:ok, subst}

  defp unify_spine([a | as], [b | bs], arity, subst) do
    case unify_one(a, b, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> unify_spine(as, bs, arity, subst2)
      # :undecided dropped for the same proven-sound reason as reduce_index_pairs.
      :undecided -> unify_spine(as, bs, arity, subst)
    end
  end

  # A spine length mismatch is a definite non-unification, NOT success (K5a #574).
  # Unreachable today — both callers (unify_one's :ctor/:data clauses) guard equal
  # length and the recursion above stays in lockstep — but a catch-all returning
  # `{:ok, subst}` (success) is a soundness landmine for any future direct caller.
  defp unify_spine(_, _, _arity, _subst), do: :impossible

  # Add {key => term} after an occurs-check; on a same-key clash, resolve-before-bind.
  #
  # `term` is first CHASED through the current substitution to its representative
  # (`resolve_index_var`). This keeps `subst` a union-find forest — each key points
  # toward a representative, never into a cycle. In particular, when a second forced
  # equation would close a loop (`c : T(a,a,b,b)` matched against `T(i,j,j,i)` induces
  # both `j := i` and, later, `i := j`), the resolved `term` collapses to the same
  # representative as `key`, so the second edge becomes the no-op `key == rterm`
  # clause below instead of a cyclic `i↦j`/`j↦i` pair. Without this the per-key
  # `occurs_index?` guard (which only inspects a key against its OWN value) cannot see
  # the cross-key cycle, and `replace_branch_vars` would apply it as a variable SWAP
  # rather than collapsing `i ≡ j` (spec §4.1 multi-key-cycle obligation).
  defp bind_index(key, term, arity, subst) do
    rterm = resolve_index_var(term, subst, 0)

    cond do
      # already same class ⇒ no-op (breaks cycles)
      rterm == {:var, key} ->
        {:ok, subst}

      # Agda Cycle rule: absurd (acyclicity)
      strongly_rigid_occurs?(key, rterm) ->
        :impossible

      # weakly-rigid cycle ⇒ conservative degrade
      occurs_index?(key, rterm) ->
        :undecided

      Map.has_key?(subst, key) ->
        old = Map.get(subst, key)

        cond do
          # consistent
          old == rterm ->
            {:ok, subst}

          rigid_index?(old) and rigid_index?(rterm) and head_key(old) != head_key(rterm) ->
            # same-key merge conflict ⇒ impossible
            :impossible

          true ->
            # Resolve-before-bind (Agda Solution step): the key is already pinned to
            # `old`, so this pair really asserts `old =? rterm`. Re-unify them; for two
            # distinct scrutinee vars this routes through unify_one clause 2 and binds
            # the outer var (a forced equation).
            unify_one(old, rterm, arity, subst)
        end

      true ->
        {:ok, Map.put(subst, key, rterm)}
    end
  end

  # Chase a `{:var, k}` through `subst` to its representative (a non-var term or an
  # unbound var). Depth-bounded purely as a defensive backstop — the forest invariant
  # maintained by `bind_index` means a real cycle never forms, so the bound is never hit.
  defp resolve_index_var({:var, k} = v, subst, depth) when depth < 100_000 do
    case Map.get(subst, k) do
      nil -> v
      next -> resolve_index_var(next, subst, depth + 1)
    end
  end

  defp resolve_index_var(t, _subst, _depth), do: t

  defp rigid_index?({:ctor, _, _}), do: true
  defp rigid_index?({:data, _, _, _}), do: true
  defp rigid_index?({:type, _}), do: true
  defp rigid_index?({:pi, _, _, _}), do: true
  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:int_type}`
  # node; fresh elaboration never produces one (spec 2026-07-18 §3a).
  defp rigid_index?({:int_type}), do: true
  defp rigid_index?({:float_type}), do: true
  defp rigid_index?({:binary_type}), do: true
  defp rigid_index?({:atom_type}), do: true
  defp rigid_index?({:atom_lit, _}), do: true
  defp rigid_index?({:int_lit, _}), do: true
  # A compact Nat literal is a closed canonical value (`2` ≡ `S(S(Z))`), so it is
  # a rigid constructor-like head for index unification — same status the `S`/`Z`
  # tower already has via the `{:ctor, _, _}` clause above.
  defp rigid_index?({:nat_lit, _}), do: true
  defp rigid_index?({:bounded_lit, _}), do: true
  defp rigid_index?({:float_lit, _}), do: true
  defp rigid_index?(_), do: false

  # Term-level one-layer peel of a compact Nat literal (the term-space mirror of
  # the value-level `Eval.nat_to_ctor/1`): `0 ↦ Z`, `n ↦ S (n-1)` with the
  # predecessor left compact. Used only by the `unify_one` nat-literal bridge.
  defp nat_lit_ctor(0), do: {:ctor, :Z, []}
  defp nat_lit_ctor(n) when is_integer(n) and n > 0, do: {:ctor, :S, [{:nat_lit, n - 1}]}

  # Expand a compact Int literal to its explicit constructor term (the term-level
  # analogue of Eval.int_to_ctor/1): FromNat(n) for n ≥ 0, NegativeSuccessor(-n-1)
  # for n < 0. Each field is a compact `{:nat_lit, _}` that bridges onward through
  # `nat_lit_ctor/1`.
  defp int_lit_ctor(n) when is_integer(n) and n >= 0, do: {:ctor, :FromNat, [{:nat_lit, n}]}
  defp int_lit_ctor(n) when is_integer(n) and n < 0, do: {:ctor, :NegativeSuccessor, [{:nat_lit, -n - 1}]}

  # Only ever called on `rigid_index?` terms (all tuples), so a tuple head is
  # exhaustive — no non-tuple fallback is reachable.
  defp head_key({:ctor, n, _}), do: {:ctor, n}
  defp head_key({:data, n, _, _}), do: {:data, n}
  defp head_key(t) when is_tuple(t), do: elem(t, 0)

  # Capture-aware occurs-check: does the FREE variable `key` appear in `term`?
  # Normalizing a reducible index can expose a stuck `case`. Its branch bodies
  # introduce constructor fields at de Bruijn indices starting from zero; the old
  # tuple walk mistook one of those BOUND variables for the constructor-telescope
  # variable being solved. That conservatively degraded the equation to
  # `:undecided`, but lost a valid GADT refinement such as
  # `projected_captures := accepting_final_captures(...)`. Track binder depth so
  # only the shifted FREE occurrence (`key + depth`) blocks a binding.
  defp occurs_index?(key, term), do: occurs_index?(key, term, 0)

  defp occurs_index?(key, {:var, k}, depth), do: k == key + depth

  defp occurs_index?(key, {:pi, _grade, domain, codomain}, depth),
    do: occurs_index?(key, domain, depth) or occurs_index?(key, codomain, depth + 1)

  defp occurs_index?(key, {:lam, _grade, domain, body}, depth),
    do: occurs_index?(key, domain, depth) or occurs_index?(key, body, depth + 1)

  defp occurs_index?(key, {:let, _grade, type, value, body}, depth),
    do:
      occurs_index?(key, type, depth) or occurs_index?(key, value, depth) or
        occurs_index?(key, body, depth + 1)

  defp occurs_index?(key, {:app, fun, arg}, depth),
    do: occurs_index?(key, fun, depth) or occurs_index?(key, arg, depth)

  defp occurs_index?(key, {:data, _name, params, indices}, depth),
    do: Enum.any?(params ++ indices, &occurs_index?(key, &1, depth))

  defp occurs_index?(key, {:ctor, _name, args}, depth),
    do: Enum.any?(args, &occurs_index?(key, &1, depth))

  defp occurs_index?(key, {:case, scrutinee, motive, branches}, depth) do
    occurs_index?(key, scrutinee, depth) or occurs_index?(key, motive, depth) or
      Enum.any?(branches, fn {_constructor, arity, body} ->
        occurs_index?(key, body, depth + arity)
      end)
  end

  defp occurs_index?(key, {:effect_type, inner}, depth), do: occurs_index?(key, inner, depth)
  defp occurs_index?(key, {:effect_pure, value}, depth), do: occurs_index?(key, value, depth)

  defp occurs_index?(key, {:effect_bind, effect, continuation}, depth),
    do: occurs_index?(key, effect, depth) or occurs_index?(key, continuation, depth)

  defp occurs_index?(_key, _term, _depth), do: false

  # Agda Cycle rule (Rules/LHS/Unify.hs `ifOccursStronglyRigid` / `flexRigOccurrenceIn`):
  # does {:var, key} occur STRONGLY RIGID in `term` — an occurrence reachable through
  # constructor/data spines ONLY, never a defined-function application or other neutral?
  # If so, `key =?= term` is unsolvable by acyclicity of the inductive, so the branch is
  # :impossible. The soundness of firing here (vs a conservative :undecided) rests
  # entirely on the ctor/data-only descent: `x = S(x)` is absurd, but `x = f(x)` for a
  # DEFINED `f` is NOT — `f` might be the identity — and an `:app`/neutral head stops the
  # search, so the latter never fires. The top of `term` must itself be a rigid ctor/data
  # head: a bare-var top is an ordinary solve (`x =?= x` handled upstream), not a cycle.
  defp strongly_rigid_occurs?(key, {:ctor, _n, args}), do: Enum.any?(args, &rigid_path_occurs?(key, &1))
  defp strongly_rigid_occurs?(key, {:data, _n, ps, is}), do: Enum.any?(ps ++ is, &rigid_path_occurs?(key, &1))
  defp strongly_rigid_occurs?(_key, _), do: false

  # Occurs along a purely rigid (ctor/data) path: a var matches; descent continues
  # solely through ctor/data spines; ANY other node (:app, neutral, meta, …) breaks
  # strong rigidity and halts the search on that sub-branch (⇒ conservative).
  defp rigid_path_occurs?(key, {:var, k}), do: k == key
  defp rigid_path_occurs?(key, {:ctor, _n, args}), do: Enum.any?(args, &rigid_path_occurs?(key, &1))
  defp rigid_path_occurs?(key, {:data, _n, ps, is}), do: Enum.any?(ps ++ is, &rigid_path_occurs?(key, &1))
  defp rigid_path_occurs?(_key, _), do: false

  @doc false
  def specialize_branch_context(ctx, subst) when map_size(subst) == 0, do: ctx

  def specialize_branch_context(ctx, subst) do
    depth = Context.length(ctx)
    env = Context.env(ctx)
    signature = Context.signature(ctx)

    types =
      Enum.map(ctx.types, fn type_value ->
        type_value
        |> Quote.reify(depth, signature)
        |> replace_branch_vars(subst)
        |> Eval.eval(env)
      end)

    refined_env =
      for i <- 0..(depth - 1)//1 do
        {:var, i}
        |> Eval.eval(env)
        |> Quote.reify(depth, signature)
        |> replace_branch_vars(subst)
        |> Eval.eval(env)
      end

    %{ctx | types: types, env: refined_env}
  end

  defp specialize_branch_value(value, _ctx, subst) when map_size(subst) == 0, do: value

  defp specialize_branch_value(value, ctx, subst) do
    value
    |> Quote.reify(Context.length(ctx), Context.signature(ctx))
    |> replace_branch_vars(subst)
    |> Eval.eval(Context.env(ctx))
  end

  defp replace_branch_vars({:var, i}, subst), do: replace_branch_var(i, subst, 0)

  defp replace_branch_vars({:pi, g, d, c}, subst),
    do: {:pi, g, replace_branch_vars(d, subst), replace_branch_vars(c, shift_subst(subst, 1))}

  defp replace_branch_vars({:lam, g, d, b}, subst),
    do: {:lam, g, replace_branch_vars(d, subst), replace_branch_vars(b, shift_subst(subst, 1))}

  defp replace_branch_vars({:app, f, a}, subst),
    do: {:app, replace_branch_vars(f, subst), replace_branch_vars(a, subst)}

  defp replace_branch_vars({:data, n, ps, is}, subst),
    do: {:data, n, Enum.map(ps, &replace_branch_vars(&1, subst)), Enum.map(is, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:ctor, n, args}, subst),
    do: {:ctor, n, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:case, scr, m, brs}, subst),
    do:
      {:case, replace_branch_vars(scr, subst), replace_branch_vars(m, subst),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, replace_branch_vars(b, shift_subst(subst, ar))} end)}

  defp replace_branch_vars(other, _subst), do: other

  defp shift_subst(subst, amount) do
    Map.new(subst, fn {k, v} -> {k + amount, Term.shift(v, amount, 0)} end)
  end

  defp replace_branch_var(i, subst, depth) when depth < 100_000 do
    case Map.get(subst, i) do
      nil -> {:var, i}
      {:var, ^i} -> {:var, i}
      {:var, j} -> replace_branch_var(j, subst, depth + 1)
      term -> replace_branch_vars(term, subst)
    end
  end

  defp replace_branch_var(i, _subst, _depth), do: {:var, i}

  # `param_vals` (most-recent-first = Context.env(ctx_params)) seeds the local
  # evaluation environment so an index-telescope type that references a family
  # PARAMETER (e.g. MyEq's `x : a`, `y : a`) resolves to the real parameter rather
  # than a bogus out-of-range neutral — the same seeding `check_ctor_app` performs
  # for the ctor-application path. Without it, a parameter reference in the second-
  # or-later index position mis-levels (`{:conversion_failure, {:var,1}, {:var,0}}`).
  defp check_result_indices(ctx_full, param_vals, result_indices, index_tele) do
    if length(result_indices) == length(index_tele) do
      case do_spine(ctx_full, Enum.zip(result_indices, index_tele), param_vals) do
        {:ok, _vals} -> :ok
        err -> err
      end
    else
      {:error, :index_arity}
    end
  end

  # Cumulative subtyping: universe-level inclusion on sorts, conversion otherwise.

  # infer_prim retired (K2, spec 2026-07-09): arithmetic/comparison are
  # registry-keyed builtin-op GLOBALS typed as ordinary Pi defs; the certified-δ
  # engine folds saturated literal spines. `bool_type_value/1` stays — the
  # elaborator's literal/`:case` lowering (and the seeded comparison codomains)
  # still route through it.
  @doc """
  The type **value** denoting the canonical `Bool` inductive (`{:vdata, :Bool, []}`).
  Bool has no params/indices, so this is exactly what `infer({:ctor, :True/:False, []})`
  and `eval({:data, :Bool, [], []})` both produce. Public: the elaborator's
  literal/`:case` lowering shares this single closed form (no drift surface).
  """
  @spec bool_type_value(Env.t()) :: Cure.Core.Value.t()
  def bool_type_value(sig) do
    fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
    {:vdata, fid, []}
  end

  @doc """
  The type **value** denoting the canonical `Nat` inductive (`{:vdata, :Nat, []}`).
  Shared by the `{:nat_lit, _}` typing rule and the elaborator's type-directed
  literal lowering, mirroring `bool_type_value/1` (no drift surface).
  """
  @spec nat_type_value(Env.t()) :: Cure.Core.Value.t()
  def nat_type_value(sig) do
    fid = Inductive.builtin(sig, :nat) || raise "builtin :nat not seeded (bootstrap/load-order bug)"
    {:vdata, fid, []}
  end

  @doc """
  The type **value** denoting the canonical `Int` inductive family
  (`Std.Int#Int = FromNat | NegativeSuccessor`). Shared by the `{:int_lit, _}`
  typing rule and any type-directed integer-literal lowering, mirroring
  `nat_type_value/1`. Since the surface flip retired the primitive `{:vint_type}`
  node, a compact integer literal inhabits this family exactly as a `Nat` literal
  inhabits `Nat`.
  """
  @spec int_type_value(Env.t()) :: Cure.Core.Value.t()
  def int_type_value(sig) do
    fid = Inductive.builtin(sig, :int) || raise "builtin :int not seeded (bootstrap/load-order bug)"
    {:vdata, fid, []}
  end

  defp subtype?({:vtype, l1}, {:vtype, l2}, _ctx), do: Universe.le?(l1, l2)

  defp subtype?(inferred, {:vdata, expected, []} = expected_value, ctx) do
    sig = Context.signature(ctx)

    expected == Inductive.builtin(sig, :any) or
      Conv.conv_values?(inferred, expected_value, Context.length(ctx), sig)
  end

  defp subtype?({:vdata, family, inferred_args}, {:vdata, family, expected_args}, ctx)
       when length(inferred_args) == length(expected_args) do
    sig = Context.signature(ctx)

    if family == Inductive.builtin(sig, :list) do
      Enum.zip(inferred_args, expected_args)
      |> Enum.all?(fn {inferred, expected} -> subtype?(inferred, expected, ctx) end)
    else
      Conv.conv_values?(
        {:vdata, family, inferred_args},
        {:vdata, family, expected_args},
        Context.length(ctx),
        sig
      )
    end
  end

  defp subtype?(inferred, expected, ctx),
    do: Conv.conv_values?(inferred, expected, Context.length(ctx), Context.signature(ctx))
end
