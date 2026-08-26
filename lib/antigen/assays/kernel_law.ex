defmodule Antigen.Assays.KernelLaw do
  @moduledoc """
  Relational kernel-law assays (spec §3), via the public `Cure.Core.*` API (no
  TCB edits): de Bruijn σ-algebra (`kernel/shift_subst`), weakening under an
  unused binder (`kernel/weakening`), reduction order-independence
  (`kernel/confluence`), and capture-avoiding β (`kernel/beta_subst`). Each is a
  `:typed_term` challenge dispatched by assay-id.

  `kernel/beta_subst` additionally calls `Cure.Elab.Subst.instantiate/2` — the
  *elaborator's* (untrusted, non-TCB) substitution — as the property's right-hand
  side: it is precisely the machinery whose capture-safety this law cross-checks
  against the trusted kernel's β-reduction (ledger #4/#26). `elab/shift_agrees`
  is the shift-half of that cross-check: the elaborator's `Subst.shift` must equal
  the kernel's `Term.shift` on every meta-free term.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Antigen.Assays.Term, as: TermAssay
  alias Cure.Core.{Conv, Term, Context, Eval, Normalise, Kernel}
  alias Cure.Elab.Subst

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{assay: "kernel/shift_subst", payload: p}), do: shift_subst(p.term)
  def run(%Challenge{assay: "kernel/weakening", payload: p}), do: weakening(p)
  def run(%Challenge{assay: "kernel/confluence", payload: p}), do: confluence(p)
  def run(%Challenge{assay: "kernel/beta_subst", payload: p}), do: beta_subst(p)
  def run(%Challenge{assay: "kernel/zeta_subst", payload: p}), do: zeta_subst(p)
  def run(%Challenge{assay: "kernel/grade_conv", payload: p}), do: grade_conv(p)
  def run(%Challenge{assay: "kernel/effect_inert", payload: p}), do: effect_inert(p)
  def run(%Challenge{assay: "elab/shift_agrees", payload: p}), do: shift_agrees(p.term)

  defp ctx_of(p), do: SigMenu.rebuild_context(SigMenu.env_of(p.sig), p.ctx)

  # ── 3a. de Bruijn σ-algebra (pure; no ctx needed) ──────────────────────────
  defp shift_subst(t) do
    with :ok <- law1(t), :ok <- law2(t), :ok <- law3(t), :ok <- law4(t), do: :ok
  end

  defp law1(t) do
    lhs = Term.shift(t, 0, 0)
    if lhs == t, do: :ok, else: {:violation, {:shift_subst_law, 1, lhs, t}}
  end

  defp law2(t) do
    case Enum.find_value([{1, 1, 0}, {2, 1, 0}, {1, 2, 1}, {2, 2, 1}], fn {a, b, c} ->
           lhs = Term.shift(Term.shift(t, a, c), b, c)
           rhs = Term.shift(t, a + b, c)
           if lhs != rhs, do: {a, b, c, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 2, f}}
    end
  end

  # commutation, for c ≤ j: shift(subst(t,j,r),a,c) == subst(shift(t,a,c), j+a, shift(r,a,c))
  defp law3(t) do
    combos = for j <- [0, 1], c <- [0, 1], a <- [1, 2], r <- [@z, @sz], c <= j, do: {j, c, a, r}

    case Enum.find_value(combos, fn {j, c, a, r} ->
           lhs = Term.shift(Term.subst(t, j, r), a, c)
           rhs = Term.subst(Term.shift(t, a, c), j + a, Term.shift(r, a, c))
           if lhs != rhs, do: {j, c, a, r, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 3, f}}
    end
  end

  # subst-of-fresh-index no-op: subst(shift(t,1,c),c,r) == shift(t,1,c)
  defp law4(t) do
    case Enum.find_value(for(c <- [0, 1], r <- [@z, @sz], do: {c, r}), fn {c, r} ->
           shifted = Term.shift(t, 1, c)
           lhs = Term.subst(shifted, c, r)
           if lhs != shifted, do: {c, r, lhs, shifted}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 4, f}}
    end
  end

  # ── 3b. weakening under an unused binder ───────────────────────────────────
  defp weakening(p) do
    ctx = ctx_of(p)
    t = p.term

    case Kernel.infer(ctx, t) do
      {:error, _} ->
        :ok

      {:ok, v} ->
        a_value = Eval.eval(@nat, Context.env(ctx))
        ctx2 = Context.extend(ctx, a_value)
        t2 = Term.shift(t, 1, 0)

        case Kernel.infer(ctx2, t2) do
          {:error, err} ->
            {:violation, {:weakening_broke_typing, err}}

          {:ok, v2} ->
            q = Normalise.quote(v, Context.length(ctx))
            q2 = Normalise.quote(v2, Context.length(ctx2))
            if q2 == Term.shift(q, 1, 0), do: :ok, else: {:violation, {:weakening_type_mismatch, q, q2}}
        end
    end
  end

  # ── 3e. elaborator/kernel shift agreement ──────────────────────────────────
  # The untrusted elaborator carries its OWN de Bruijn shift (Cure.Elab.Subst.shift)
  # because it must also shift meta-bearing terms the trusted Core.Term.shift refuses
  # (subst.ex moduledoc). On the meta-FREE terms this generator emits the two MUST
  # coincide: if they ever diverge, the elaborator would relocate free variables
  # differently from the kernel — a capture bug at the TCB boundary that the
  # bind-once β-redex fix (which shifts `expected` via Subst.shift) would inherit.
  defp shift_agrees(t) do
    combos = for a <- [1, 2, 3], c <- [0, 1, 2], do: {a, c}

    case Enum.find_value(combos, fn {a, c} ->
           lhs = Subst.shift(t, a, c)
           rhs = Term.shift(t, a, c)
           if lhs != rhs, do: {a, c, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:elab_shift_disagrees, f}}
    end
  end

  # ── 3d. capture-avoiding β: β-reduction agrees with substitution ───────────
  # For a redex (λx:T. body) e the law has TWO obligations, both of which must hold:
  #
  #   (a) reduction — the kernel's β lands on the same normal form as substituting
  #       e for x via the elaborator's capture-avoiding `instantiate`;
  #   (b) typing (the substitution lemma) — the redex and its substituted body are
  #       both well-typed and at the SAME type.
  #
  # `instantiate(body, [e])` replaces x (de Bruijn 0) with e, shifting e under every
  # binder body crosses. A shift/capture bug shows up in (a) as a normal-form
  # disagreement AND in (b) as a mis-scoped `subst_term` that infers to no type or a
  # different one — the typing-level teeth the nf comparison alone cannot see.
  defp beta_subst(%{term: {:app, {:lam, _g, _t, body}, e}} = p) do
    ctx = ctx_of(p)
    redex = p.term
    subst_term = Subst.instantiate(body, [e])

    with :ok <- beta_nf_agrees(ctx, redex, subst_term),
         :ok <- beta_type_agrees(ctx, redex, subst_term) do
      :ok
    end
  end

  # The generator only ever emits redexes; a non-redex term is a wiring bug, not a
  # kernel finding — surface it distinctly.
  defp beta_subst(%{term: other}), do: {:violation, {:beta_subst_not_a_redex, other}}

  # ── 3e. ζ: `let` agrees with capture-avoiding substitution ─────────────────
  #
  # The antibody for the Core `:let` binder. `Eval`'s ζ pushes the *evaluated*
  # value of `e` into the NbE environment and never shifts; `Subst.instantiate/2`
  # shifts `e` by the binder depth. Different mechanisms, same answer — or the
  # `:let` node is unsound.
  #
  # Reusing `beta_nf_agrees/3` and `beta_type_agrees/3` verbatim is deliberate:
  # the property IS the same property, so it must be checked by the same code.
  # A pass here means ζ equates exactly what substitution equates — no distinct
  # normal forms collapsed — and terminates wherever substitution does (both
  # sides share the assay fuel and abstain together on exhaustion).
  defp zeta_subst(%{term: {:let, _g, _t, e, body}} = p) do
    ctx = ctx_of(p)
    subst_term = Subst.instantiate(body, [e])

    # `shift_subst/1` is the pure de Bruijn sigma-algebra (laws 1-4). Running it
    # on the `:let` term itself is what property-tests `Term.shift/3` and
    # `Term.subst/3`'s new clauses -- specifically that `body` is one binder
    # deeper than `ty`/`val`. Nothing else in the corpus generates a `:let` yet,
    # so without this the new binder's sigma-algebra would be covered only by
    # ExUnit.
    with :ok <- shift_subst(p.term),
         :ok <- beta_nf_agrees(ctx, p.term, subst_term),
         :ok <- beta_type_agrees(ctx, p.term, subst_term) do
      :ok
    end
  end

  defp zeta_subst(%{term: other}), do: {:violation, {:zeta_subst_not_a_let, other}}

  # ── 3f. a binder's GRADE is part of type identity ──────────────────────────
  #
  # Idris `Core/Normalise/Convert.idr:328` compares `multiplicity` in
  # `convBinders`, so `(1 x : A) -> B` and `(x : A) -> B` are DIFFERENT TYPES.
  # Comparison is by EQUALITY, never by the subusaging preorder: `leq(:linear,
  # :affine)` holds, and yet those two Π types must not convert.
  #
  # Reflexivity is checked first so the law cannot pass vacuously by rejecting
  # everything — a `Conv` that returned `false` unconditionally would otherwise
  # look healthy.
  defp grade_conv(%{term: {:pi, g, dom, cod} = t} = p) do
    ctx = ctx_of(p)
    env = Context.env(ctx)
    depth = Context.length(ctx)
    sig = SigMenu.env_of(p.sig)

    with :ok <- grade_conv_refl(t, env, depth, sig),
         :ok <- grade_conv_distinct(t, g, env, depth, sig) do
      # The use-site half needs a λ that INHABITS the Π. The identity λ does so
      # only when `dom == cod`; the shrinker happily rewrites a codomain into
      # something else (it does not preserve well-typedness), and the nested
      # cases have a Π codomain. Skip the half we cannot construct — the
      # conversion half above is the property, and the `pi_*` cells all satisfy
      # `dom == cod`, so it is still exercised.
      if dom == cod, do: grade_conv_check(ctx, g, dom, t, env), else: :ok
    end
  end

  # A λ's grade is part of the TERM's identity, exactly as a Π's is part of the type's.
  # Idris reaches `convBinders` (which compares `multiplicity`) from `convGen` on
  # Bind-vs-Bind, so Lam-vs-Lam is grade-sensitive; its η clause only fires for
  # Lam-vs-non-Bind. No use-site half here: a λ is the thing being compared.
  defp grade_conv(%{term: {:lam, g, _dom, _body} = t} = p) do
    ctx = ctx_of(p)
    env = Context.env(ctx)
    depth = Context.length(ctx)
    sig = SigMenu.env_of(p.sig)

    with :ok <- grade_conv_refl(t, env, depth, sig),
         do: grade_conv_distinct(t, g, env, depth, sig)
  end

  defp grade_conv(%{term: other}), do: {:violation, {:grade_conv_not_a_binder, other}}

  defp grade_conv_refl(t, env, depth, sig) do
    if Conv.conv?(t, t, env, depth, sig),
      do: :ok,
      else: {:violation, {:grade_conv_not_reflexive, t}}
  end

  # Every OTHER grade must yield a non-convertible binder — Π or λ alike.
  defp grade_conv_distinct(t, g, env, depth, sig) do
    Enum.reduce_while(Antigen.Generators.GradeConv.others(g), :ok, fn g2, _acc ->
      other = regrade(t, g2)

      if Conv.conv?(t, other, env, depth, sig) do
        {:halt, {:violation, {:grade_conv_collapsed, %{left: t, right: other}}}}
      else
        {:cont, :ok}
      end
    end)
  end

  defp regrade({:pi, _g, dom, cod}, g2), do: {:pi, g2, dom, cod}
  defp regrade({:lam, _g, dom, body}, g2), do: {:lam, g2, dom, body}

  # The use-site half: a λ checks against a Π of its own grade, and only that one.
  # This is where the discipline actually bites, and it is what a `Conv` that
  # ignored grades would silently permit.
  defp grade_conv_check(ctx, g, dom, t, env) do
    vpi = Eval.eval(t, env)

    same = Kernel.check(ctx, {:lam, g, dom, {:var, 0}}, vpi)

    if same != :ok do
      {:violation, {:grade_conv_same_grade_rejected, %{grade: g, reason: same}}}
    else
      Enum.reduce_while(Antigen.Generators.GradeConv.others(g), :ok, fn g2, _acc ->
        case Kernel.check(ctx, {:lam, g2, dom, {:var, 0}}, vpi) do
          :ok -> {:halt, {:violation, {:grade_conv_wrong_grade_accepted, %{pi: g, lam: g2}}}}
          {:error, _} -> {:cont, :ok}
        end
      end)
    end
  end

  # ── 3g. `Effect` inertness invariance ──────────────────────────────────────
  #
  # `Effect`/`pure`/`bind` are an INERT uninterpreted signature (effect-type-
  # former design §3.2, §9). Two obligations, both structural:
  #
  #   (a) inertness — `nf(t)` preserves the effect SKELETON (the arrangement and
  #       nesting of `effect_type`/`effect_pure`/`effect_bind` nodes). nf may still
  #       reduce ordinary *sub*terms — `pure((λx.x) 3)` normalizes its payload to
  #       `pure(3)` — so the comparison is on the skeleton (payloads collapsed to a
  #       hole), not the whole term. A monad law or a commuting conversion would
  #       rearrange that skeleton; nothing else can.
  #
  #   (b) left identity is DEFINITIONALLY FALSE — for `bind(pure(a), k)`, neither
  #       `k(a)` (`{:app, k, a}`, which β-reduces to `k`'s body) nor `pure(a)` is
  #       convertible with it. This is the equation whose accidental introduction
  #       into `Eval`/`Conv`/`Normalise` this antibody exists to catch.
  #
  # Reflexivity is checked first (as in `grade_conv`) so a `Conv` that rejected
  # everything cannot make (b) pass vacuously.
  defp effect_inert(%{term: t} = p) do
    ctx = ctx_of(p)
    env = Context.env(ctx)
    depth = Context.length(ctx)
    sig = SigMenu.env_of(p.sig)

    with :ok <- effect_reflexive(t, env, depth, sig),
         :ok <- effect_nf_preserves_skeleton(ctx, t),
         do: effect_left_identity_distinct(t, env, depth, sig)
  end

  defp effect_reflexive(t, env, depth, sig) do
    if Conv.conv?(t, t, env, depth, sig),
      do: :ok,
      else: {:violation, {:effect_not_reflexive, t}}
  end

  defp effect_nf_preserves_skeleton(ctx, t) do
    case Normalise.nf(ctx, t, fuel: TermAssay.assay_fuel()) do
      :fuel_exhausted ->
        :ok

      nf ->
        before = effect_skeleton(t)
        aft = effect_skeleton(nf)

        if before == aft do
          :ok
        else
          {:violation, {:effect_structure_changed, %{term: t, nf: nf, skeleton_before: before, skeleton_after: aft}}}
        end
    end
  end

  # `bind(pure(a), k)` must be convertible with NEITHER `k(a)` nor `pure(a)`.
  # Any other effect shape has no left-identity obligation — vacuously :ok.
  defp effect_left_identity_distinct({:effect_bind, {:effect_pure, a}, {:lam, _g, _dom, _body} = k}, env, depth, sig) do
    t = {:effect_bind, {:effect_pure, a}, k}
    k_of_a = {:app, k, a}
    pure_a = {:effect_pure, a}

    cond do
      Conv.conv?(t, k_of_a, env, depth, sig) ->
        {:violation, {:effect_left_identity_leaked, %{term: t, k_of_a: k_of_a}}}

      Conv.conv?(t, pure_a, env, depth, sig) ->
        {:violation, {:effect_bind_pure_collapsed, %{term: t, pure_a: pure_a}}}

      true ->
        :ok
    end
  end

  defp effect_left_identity_distinct(_t, _env, _depth, _sig), do: :ok

  # The effect skeleton: keep every `effect_type`/`effect_pure`/`effect_bind`
  # node and the `λ` binders that carry `k`, but collapse every maximal
  # non-effect subterm (payloads, domains, redexes) to `:hole`. Two terms have
  # the same skeleton iff they arrange their effect nodes identically, regardless
  # of how their ordinary subterms normalize.
  defp effect_skeleton({:effect_type, t}), do: {:effect_type, effect_skeleton(t)}
  defp effect_skeleton({:effect_pure, a}), do: {:effect_pure, effect_skeleton(a)}
  defp effect_skeleton({:effect_bind, e, k}), do: {:effect_bind, effect_skeleton(e), effect_skeleton(k)}
  defp effect_skeleton({:lam, _g, dom, body}), do: {:lam, effect_skeleton(dom), effect_skeleton(body)}
  defp effect_skeleton(_leaf), do: :hole

  # (a) β-reduction ≡ substitution. Normalized under the same fuel so a divergent
  # (fuel-exhausting) case abstains rather than false-positives.
  defp beta_nf_agrees(ctx, redex, subst_term) do
    fuel = TermAssay.assay_fuel()
    lhs = Normalise.nf(ctx, redex, fuel: fuel)
    rhs = Normalise.nf(ctx, subst_term, fuel: fuel)

    cond do
      lhs == :fuel_exhausted or rhs == :fuel_exhausted ->
        :ok

      lhs == rhs ->
        :ok

      true ->
        {:violation, {:beta_subst_mismatch, %{redex: redex, subst: subst_term, beta_nf: lhs, subst_nf: rhs}}}
    end
  end

  # (b) the substitution lemma: Γ,x:A ⊢ body:B and Γ ⊢ e:A ⟹ Γ ⊢ body[e]:B[e].
  # Both the redex and its substituted body must infer, to the same type (compared
  # by their quoted normal forms, as `weakening` does). A `subst_term` that fails to
  # infer, or infers a different type, is a capture/shift bug in `instantiate`.
  defp beta_type_agrees(ctx, redex, subst_term) do
    depth = Context.length(ctx)

    case {Kernel.infer(ctx, redex), Kernel.infer(ctx, subst_term)} do
      {{:ok, vr}, {:ok, vs}} ->
        qr = Normalise.quote(vr, depth)
        qs = Normalise.quote(vs, depth)
        if qr == qs, do: :ok, else: {:violation, {:beta_subst_type_mismatch, %{redex_type: qr, subst_type: qs}}}

      {{:error, er}, _} ->
        {:violation, {:beta_subst_redex_ill_typed, er}}

      {{:ok, _}, {:error, es}} ->
        {:violation, {:beta_subst_result_ill_typed, es}}
    end
  end

  # ── 3c. reduction order-independence ───────────────────────────────────────
  defp confluence(p) do
    ctx = ctx_of(p)
    t = p.term
    fuel = TermAssay.assay_fuel()
    full = Normalise.nf(ctx, t, fuel: fuel)

    staged =
      case Normalise.whnf(ctx, t, fuel: fuel) do
        :fuel_exhausted -> :skip
        w -> Normalise.nf(ctx, w, fuel: fuel)
      end

    cond do
      full == :fuel_exhausted -> :ok
      staged in [:skip, :fuel_exhausted] -> :ok
      full == staged -> :ok
      true -> {:violation, {:confluence_mismatch, full, staged}}
    end
  end
end
