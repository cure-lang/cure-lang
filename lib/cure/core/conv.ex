defmodule Cure.Core.Conv do
  @moduledoc """
  Definitional equality (conversion) by normalization-by-evaluation
  (design spec §4.5; mirrors Idris `Core/Normalise/Convert.idr` and Lean
  `type_checker.cpp`'s `is_def_eq`).

  `conv?/4,5` evaluates both terms under the shared value environment and
  compares the resulting values up to β, ι (incl. `case`-ι), η, and **δ**.

  δ (global unfolding) is **lazy** and **gated**: a value headed by a global is
  unfolded only when that global is totality-certified in the signature
  (`Cure.Core.Env`, populated by `Kernel.validate_certificate`, M7.2). Until
  then two `:nglobal` heads are convertible iff they are the same name. The
  signature is the optional last argument; with no signature, no δ is performed
  (β/ι/η only — the pre-M7 behaviour).

  Doing δ here (rather than eagerly in `eval`) keeps `eval` signature-free; the
  effect is identical — certified globals reduce wherever conversion compares
  them. η is handled here too, type-free (the §4.5 λ-vs-neutral trick).
  """

  alias Cure.Core.{Env, Eval, Normalise}

  @doc """
  Like `conv?/5`, but bounds the total number of δ-unfolds to `fuel`. Returns
  `{:ok, boolean}` if conversion decides within budget, or `:fuel_exhausted` if the
  δ-unfold count is hit first (a suspected non-normalization — the reflexivity
  assay's oracle, spec §4.3/§8). The verdict is a fixed step count, so it is
  machine-independent and replayable.
  """
  @spec conv_within?(
          Cure.Core.Term.t(),
          Cure.Core.Term.t(),
          [Cure.Core.Value.t()],
          non_neg_integer(),
          Env.t() | nil,
          pos_integer()
        ) ::
          {:ok, boolean()} | :fuel_exhausted
  def conv_within?(term1, term2, env, depth, sig, fuel) when is_integer(fuel) and fuel > 0 do
    Normalise.with_fuel(fuel, fn ->
      {:ok, conv?(term1, term2, env, depth, sig)}
    end)
  end

  @doc "True iff `term1` and `term2` are definitionally equal under `env`."
  @spec conv?(Cure.Core.Term.t(), Cure.Core.Term.t(), [Cure.Core.Value.t()], non_neg_integer(), Env.t() | nil) ::
          boolean()
  def conv?(term1, term2, env, depth, sig \\ nil) do
    conv_val?(Eval.eval(term1, env), Eval.eval(term2, env), depth, sig)
  end

  @doc "Value-level definitional equality — the core of `conv?`, for callers holding values."
  @spec conv_values?(Cure.Core.Value.t(), Cure.Core.Value.t(), non_neg_integer(), Env.t() | nil) ::
          boolean()
  def conv_values?(v1, v2, depth, sig \\ nil), do: conv_val?(v1, v2, depth, sig)

  # δ-whnf both sides (unfold certified-global heads), then compare structurally.
  defp conv_val?({:vneutral, n1} = v1, {:vneutral, n2} = v2, depth, sig) do
    # Canonical normalization freezes a global application when its body only
    # exposes a case stuck on a neutral. Conversion must nevertheless relate
    # that folded form to the explicitly exposed body (for example a motive
    # produced by dependent-match elaboration). Retry on demand with one stuck
    # case exposed on each side; subsequent comparison remains structural and
    # recursive calls retain the ordinary lazy policy.
    same_neutral_no_delta?(n1, n2, depth, sig) or
      conv_struct?(Normalise.whnf_value(v1, sig), Normalise.whnf_value(v2, sig), depth, sig) or
      conv_exposed_stuck?(v1, v2, depth, sig)
  end

  defp conv_val?(v1, v2, depth, sig) do
    conv_struct?(Normalise.whnf_value(v1, sig), Normalise.whnf_value(v2, sig), depth, sig)
  end

  defp conv_exposed_stuck?(v1, v2, depth, sig) do
    conv_struct?(
      Normalise.whnf_value(v1, sig, stuck_cases: :expose),
      Normalise.whnf_value(v2, sig, stuck_cases: :expose),
      depth,
      sig
    )
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  # A λ's GRADE is part of the term's identity, exactly as a Π's is part of the type's.
  # Idris reaches `convBinders` — which compares `multiplicity` — from `convGen` on
  # Bind-vs-Bind, and `sameBinders (Lam {}) (Lam {}) = True`
  # (`Core/Normalise/Convert.idr:328-337`). Its η clause (`:351`) only ever fires for
  # Lam-vs-**non**-Bind.
  #
  # This clause must therefore precede the η clauses below, which match *any* `:vlam`
  # on either side and so swallowed λ-vs-λ entirely: `{:vlam, :linear, …}` and
  # `{:vlam, :unrestricted, …}` were convertible, and `Conv` accepted terms Idris
  # rejects. Grades are compared by EQUALITY, never by `Grade.leq/2` — the preorder
  # belongs to the usage check, and a `Conv` that consulted it would make the whole
  # discipline decorative. Everything past the grade stays with η, so this adds the
  # missing check and changes nothing else.
  defp conv_struct?({:vlam, g1, _, _} = l, {:vlam, g2, _, _} = r, depth, sig),
    do: g1 == g2 and eta_eq?(l, r, depth, sig)

  # η: a λ against a NON-λ, compared by applying both to a fresh neutral.
  defp conv_struct?({:vlam, _, _, _} = l, r, depth, sig), do: eta_eq?(l, r, depth, sig)
  defp conv_struct?(l, {:vlam, _, _, _} = r, depth, sig), do: eta_eq?(r, l, depth, sig)

  defp conv_struct?({:vtype, l1}, {:vtype, l2}, _depth, _sig), do: l1 == l2

  # NOTE(int-facade): `{:vint_type}` can no longer arise from fresh elaboration
  # (spec 2026-07-18 §3a) but this clause (and its `same_value_no_delta?` twin
  # below) stay so conversion remains total on legacy/deserialized values.
  defp conv_struct?({:vint_type}, {:vint_type}, _depth, _sig), do: true
  defp conv_struct?({:vint, a}, {:vint, b}, _depth, _sig), do: a == b

  # A compact Int literal is definitionally equal to its FromNat/NegativeSuccessor
  # constructor value, both directions — the Int analogue of the vnat↔S/Z rules
  # below. Single-step peel (Int has just the two outermost ctors), then the
  # ctor↔ctor / ctor↔vnat rules finish the comparison on the compact Nat field.
  defp conv_struct?({:vint, n}, {:vctor, _, _} = c, depth, sig),
    do: conv_struct?(Eval.int_to_ctor({:vint, n}), c, depth, sig)

  defp conv_struct?({:vctor, _, _} = c, {:vint, n}, depth, sig),
    do: conv_struct?(c, Eval.int_to_ctor({:vint, n}), depth, sig)

  defp conv_struct?({:vfloat_type}, {:vfloat_type}, _depth, _sig), do: true
  defp conv_struct?({:vbinary_type}, {:vbinary_type}, _depth, _sig), do: true
  defp conv_struct?({:vatom_type}, {:vatom_type}, _depth, _sig), do: true
  defp conv_struct?({:vatom, a}, {:vatom, b}, _depth, _sig), do: a == b
  defp conv_struct?({:vfloat, a}, {:vfloat, b}, _depth, _sig), do: a == b

  # Compact Nat literals. Same representation → O(1) bignum equality. Cross
  # representation → peel the tower one `S`/`Z` layer to meet the literal (Lean's
  # `toCtorIfLit` / Agda's suc-strictness): `lit n` and the n-fold `S`-tower are
  # definitionally equal in BOTH directions, but the literal is never expanded —
  # each step recurses on a compact predecessor, so this is O(#layers actually
  # compared), never O(n) space. `S` has no params, so its field list is `[pred]`.
  defp conv_struct?({:vnat, a}, {:vnat, b}, _depth, _sig), do: a == b

  defp conv_struct?({:vnat, n}, {:vctor, _, _} = c, depth, sig),
    do: conv_struct?(Eval.nat_to_ctor({:vnat, n}), c, depth, sig)

  defp conv_struct?({:vctor, _, _} = c, {:vnat, n}, depth, sig),
    do: conv_struct?(c, Eval.nat_to_ctor({:vnat, n}), depth, sig)

  # A compact `Bounded` literal is definitionally equal to its `First`/`Next`
  # tower, both directions, peeling one compact layer per step — the analogue of
  # the `vnat`↔`S`/`Z` rules above (`First`≙`Z`, `Next`≙`S`). Unlike Nat, each
  # `Bounded` ctor value carries an erased implicit index `m` ahead of its fields
  # (declaration order `[m]` / `[m, pred]`); the index is erased so the cross-rep
  # rule ignores it and recurses only on the present predecessor (well-typedness
  # forces `m` to the value both sides already agree on).
  defp conv_struct?({:vbounded, a}, {:vbounded, b}, _depth, _sig), do: a == b

  defp conv_struct?({:vbounded, 0}, {:vctor, name, [_m]}, _depth, _sig),
    do: Eval.constructor_name_matches?(name, :First)

  defp conv_struct?({:vctor, name, [_m]}, {:vbounded, 0}, _depth, _sig),
    do: Eval.constructor_name_matches?(name, :First)

  defp conv_struct?({:vbounded, n}, {:vctor, name, [_m, pred]}, depth, sig) when n > 0,
    do: Eval.constructor_name_matches?(name, :Next) and conv_val?({:vbounded, n - 1}, pred, depth, sig)

  defp conv_struct?({:vctor, name, [_m, pred]}, {:vbounded, n}, depth, sig) when n > 0,
    do: Eval.constructor_name_matches?(name, :Next) and conv_val?(pred, {:vbounded, n - 1}, depth, sig)

  defp conv_struct?({:vneutral, n1}, {:vneutral, n2}, depth, sig),
    do: conv_neutral?(n1, n2, depth, sig)

  # Π types compare their GRADES, by equality. Idris does the same
  # (`Core/Normalise/Convert.idr:328`: `sameBinders bx by && multiplicity bx ==
  # multiplicity by`), so `(1 x : A) -> B` is a DIFFERENT TYPE from
  # `(x : A) -> B`. Never use the subusaging preorder here: `Grade.leq/2` says a
  # linear value is acceptable where an affine one is demanded, which is a fact
  # about USAGE, not about type identity. Comparing by `leq` would let a linear
  # function be passed where an unrestricted one is expected and the whole
  # discipline would be decorative.
  defp conv_struct?({:vpi, g1, d1, c1}, {:vpi, g2, d2, c2}, depth, sig),
    do: g1 == g2 and conv_val?(d1, d2, depth, sig) and conv_closure?(c1, c2, depth, sig)

  defp conv_struct?({:vdata, n1, vs1}, {:vdata, n2, vs2}, depth, sig),
    do: n1 == n2 and conv_spine?(vs1, vs2, depth, sig)

  defp conv_struct?({:vctor, n1, vs1}, {:vctor, n2, vs2}, depth, sig) do
    if Eval.constructor_name_matches?(n1, n2) do
      {vs1, vs2} = Cure.Core.Inductive.align_ctor_spines(sig, n1, vs1, vs2)
      conv_spine?(vs1, vs2, depth, sig)
    else
      false
    end
  end

  # Inert effect values: congruence ONLY — same node, pointwise-convertible
  # children. No reduction, no monad laws (design §3.2). Because these are
  # distinct value constructors, `bind(pure(a),k)` and `k(a)` (or `pure(a)`)
  # land on the `_, _` fallback below and compare unequal, which is the point.
  defp conv_struct?({:veffect_type, a}, {:veffect_type, b}, depth, sig),
    do: conv_val?(a, b, depth, sig)

  defp conv_struct?({:veffect_pure, a}, {:veffect_pure, b}, depth, sig),
    do: conv_val?(a, b, depth, sig)

  defp conv_struct?({:veffect_bind, e1, k1}, {:veffect_bind, e2, k2}, depth, sig),
    do: conv_val?(e1, e2, depth, sig) and conv_val?(k1, k2, depth, sig)

  defp conv_struct?(_, _, _, _), do: false

  # -- η / β-under-binder -----------------------------------------------------

  defp eta_eq?(lam, {:vlam, _, _, _} = other, depth, sig), do: apply_eq?(lam, other, depth, sig)
  defp eta_eq?(lam, {:vneutral, _} = other, depth, sig), do: apply_eq?(lam, other, depth, sig)
  defp eta_eq?(_lam, _other, _depth, _sig), do: false

  defp apply_eq?(v1, v2, depth, sig) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.apply(v1, fresh), Eval.apply(v2, fresh), depth + 1, sig)
  end

  defp conv_closure?({:closure, env1, t1}, {:closure, env2, t2}, depth, sig) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.eval(t1, [fresh | env1]), Eval.eval(t2, [fresh | env2]), depth + 1, sig)
  end

  defp conv_spine?(vs1, vs2, depth, sig) do
    length(vs1) == length(vs2) and
      Enum.zip(vs1, vs2) |> Enum.all?(fn {a, b} -> conv_val?(a, b, depth, sig) end)
  end

  # -- neutral conversion -----------------------------------------------------

  defp conv_neutral?({:nvar, l1}, {:nvar, l2}, _depth, _sig), do: l1 == l2
  # Uncertified globals are opaque, equal iff the same name (δ already tried in whnf).
  defp conv_neutral?({:nglobal, a}, {:nglobal, b}, _depth, _sig), do: a == b
  # A hole is convertible ONLY to a hole with the same id — each hole is its own
  # fresh axiom of its checked type (Agda/Idris postulate-per-hole). Distinct ids
  # fall through to the `_, _` catch-all below and compare unequal, so `refl : ?a
  # = ?b` cannot type-check across two different holes (first-class holes).
  defp conv_neutral?({:nhole, a}, {:nhole, b}, _depth, _sig), do: a == b

  defp conv_neutral?({:napp, n1, v1}, {:napp, n2, v2}, depth, sig),
    do: conv_neutral?(n1, n2, depth, sig) and conv_val?(v1, v2, depth, sig)

  # The scrutinee compares up to conversion (lifted to a value, so whnf can
  # force a redex scrutinee that δι-reduces past the stuck case) — a stuck
  # case's scrutinee is an argument position like any other, per Lean
  # `is_def_eq_app` (each arg via full `is_def_eq`) and Agda `compareElims`.
  defp conv_neutral?({:ncase, n1, m1, brs1}, {:ncase, n2, m2, brs2}, depth, sig) do
    conv_val?({:vneutral, n1}, {:vneutral, n2}, depth, sig) and conv_motive?(m1, m2, depth, sig) and
      conv_branches?(brs1, brs2, depth, sig)
  end

  defp conv_neutral?(_, _, _, _), do: false

  # A stuck-case motive is a COMPLETE function term captured in a closure (a full
  # λ over the scrutinee/indices), not a body-under-one-binder. So instantiate it
  # with NO extra binder — exactly as `Quote.instantiate` reads it back — and
  # compare the resulting function values (η handles the λ). Using `conv_closure?`
  # here would push a spurious binder, shifting the motive's captured environment
  # and making two motives that capture different values compare equal (unsound).
  defp conv_motive?({:closure, env1, t1}, {:closure, env2, t2}, depth, sig),
    do: conv_val?(Eval.eval(t1, env1), Eval.eval(t2, env2), depth, sig)

  defp conv_branches?(brs1, brs2, depth, sig) do
    length(brs1) == length(brs2) and
      Enum.zip(brs1, brs2)
      |> Enum.all?(fn {{c1, a1, cl1}, {c2, a2, cl2}} ->
        c1 == c2 and a1 == a2 and conv_branch_bodies?(a1, cl1, cl2, depth, sig)
      end)
  end

  defp conv_branch_bodies?(arity, {:closure, env1, body1}, {:closure, env2, body2}, depth, sig),
    do:
      conv_val?(
        Eval.open_branch(env1, body1, arity, depth),
        Eval.open_branch(env2, body2, arity, depth),
        depth + arity,
        sig
      )

  # Syntactic equality for neutral values before δ. This prevents certified
  # recursive globals from unfolding forever when conversion reaches the same
  # stuck recursive call on both sides (`plus(k, n)` vs `plus(k, n)`), while still
  # allowing δ when the two heads are not already identical.
  defp same_neutral_no_delta?({:nvar, l1}, {:nvar, l2}, _depth, _sig), do: l1 == l2
  defp same_neutral_no_delta?({:nglobal, a}, {:nglobal, b}, _depth, _sig), do: a == b
  # Holes carry no δ; the syntactic pre-δ fast path compares them by id, exactly
  # as the post-whnf `conv_neutral?` above (first-class holes).
  defp same_neutral_no_delta?({:nhole, a}, {:nhole, b}, _depth, _sig), do: a == b

  defp same_neutral_no_delta?({:napp, f1, a1}, {:napp, f2, a2}, depth, sig),
    do: same_neutral_no_delta?(f1, f2, depth, sig) and same_value_no_delta?(a1, a2, depth, sig)

  defp same_neutral_no_delta?(_, _, _depth, _sig), do: false

  defp same_value_no_delta?({:vneutral, n1}, {:vneutral, n2}, depth, sig),
    do: same_neutral_no_delta?(n1, n2, depth, sig)

  defp same_value_no_delta?({:vtype, l1}, {:vtype, l2}, _depth, _sig), do: l1 == l2
  defp same_value_no_delta?({:vint_type}, {:vint_type}, _depth, _sig), do: true
  defp same_value_no_delta?({:vint, a}, {:vint, b}, _depth, _sig), do: a == b
  # Same-representation fast-path; a cross-rep miss falls through to the real
  # `conv_struct?` peel (this predicate only short-circuits obvious equalities).
  defp same_value_no_delta?({:vnat, a}, {:vnat, b}, _depth, _sig), do: a == b
  defp same_value_no_delta?({:vbounded, a}, {:vbounded, b}, _depth, _sig), do: a == b
  defp same_value_no_delta?({:vfloat_type}, {:vfloat_type}, _depth, _sig), do: true
  defp same_value_no_delta?({:vbinary_type}, {:vbinary_type}, _depth, _sig), do: true
  defp same_value_no_delta?({:vatom_type}, {:vatom_type}, _depth, _sig), do: true
  defp same_value_no_delta?({:vatom, a}, {:vatom, b}, _depth, _sig), do: a == b
  defp same_value_no_delta?({:vfloat, a}, {:vfloat, b}, _depth, _sig), do: a == b

  defp same_value_no_delta?({:vdata, n1, args1}, {:vdata, n2, args2}, depth, sig),
    do: n1 == n2 and same_spine_no_delta?(args1, args2, depth, sig)

  defp same_value_no_delta?({:vctor, n1, args1}, {:vctor, n2, args2}, depth, sig) do
    if Eval.constructor_name_matches?(n1, n2) do
      {args1, args2} = Cure.Core.Inductive.align_ctor_spines(sig, n1, args1, args2)
      same_spine_no_delta?(args1, args2, depth, sig)
    else
      false
    end
  end

  defp same_value_no_delta?(_a, _b, _depth, _sig), do: false

  defp same_spine_no_delta?(args1, args2, depth, sig) do
    length(args1) == length(args2) and
      Enum.zip(args1, args2) |> Enum.all?(fn {a, b} -> same_value_no_delta?(a, b, depth, sig) end)
  end
end
