defmodule Antigen.UnifyInjectivitySymmetryAntibodyTest do
  @moduledoc """
  TCB antibody (K-bug 1, spec `2026-07-18-elaborator-gaps-verified-status.md` §2) —
  the kernel index unifier must decide a constructor-injectivity equation
  SYMMETRICALLY, independent of the argument order in which the two index vectors
  are presented.

  ## The bug this pins (RED at authoring)

  `Cure.Core.Kernel.unify_one/4` has a clause for an outer/scrutinee var on the
  RIGHT (`unify_one(r, {:var, j}, arity, _) when j >= arity`, kernel.ex ~1336) but
  NO symmetric clause for the same var on the LEFT. The resolve-before-bind
  re-unify step in `bind_index/4` (~1498) calls `unify_one(old, rterm, ...)` with
  `old`/`rterm` positions determined purely by the order in which the scrutinee's
  index pairs were processed — so which operand carries the outer var is
  order-sensitive. When the outer var lands on the left, every specific clause
  falls through to the generic catch-all, which returns `:undecided`, and
  `unify_spine` silently drops it.

  Concretely, for `refl : Eqv(x, x)` matched at scrutinee indices:

    * `Eqv(S(a), S(Z()))` (variable-first) — the forced equation `a := Z` is
      DROPPED; the returned `{:solved, subst}` is NOT a genuine unifier
      (`S(a) !≡ S(Z())` after applying it).
    * `Eqv(S(Z()), S(a))` (ground-first)  — `a := Z` is captured; the subst IS a
      genuine unifier.

  Both return `{:solved, _}`; the defect is entirely in the subst's content. This
  is a COMPLETENESS gap (the trusted kernel never accepts anything ill-typed — a
  dropped equation only makes the enclosing branch fail conversion downstream), so
  the antibody is a MUST-DECIDE-SYMMETRICALLY reach pin, not a
  never-equate-distinct-NF soundness pin.

  ## Obligations

    * REACH (variable-first must unify) — `branch_unify` on `Eqv(S(a), S(Z()))`
      returns a subst that is a genuine unifier: applying it to the ctor's
      result-index vector and the (shifted) scrutinee vector makes them pairwise
      convertible. RED until the missing symmetric `unify_one` clause is added.

    * CONTROL (ground-first stays a unifier) — the mirror `Eqv(S(Z()), S(a))`
      already unifies and MUST keep doing so. Guards against a fix that trades one
      order for the other.

    * SYMMETRY — both orders reach the SAME verdict (both genuine unifiers). The
      headline invariant; a fix that greens REACH without regressing CONTROL
      satisfies it.

  Independent oracle: the "is a genuine unifier" check applies the returned subst
  and asks `Cure.Core.Conv.conv_within?` — it never inspects kernel internals, so
  it cannot be satisfied by a subst that merely *looks* solved.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Quote, Term, Inductive}
  alias Cure.Elab.Program

  @fuel 1000

  # Families/constructors elaborate to owner-qualified identities.
  defp q(owner, name), do: Cure.Elab.Name.qualify(owner, name)

  defp elaborate!(src) do
    {:ok, s} = Program.elaborate(src)
    s
  end

  # Nat + the identity family `Eqv` with a reflexivity constructor `refl`.
  defp eqv_sig,
    do: elaborate!("mod E\n  type Nat = Z | S(Nat)\n  type Eqv indices (a: Nat, b: Nat)\n    refl : Eqv(x, x)\nend\n")

  # A context with one outer Nat var (`a`) in scope.
  defp ctx1(sig),
    do: Context.extend(Context.empty(sig), {:vdata, q("E", :Nat), []})

  # Value-domain scrutinee pieces.
  defp a_val, do: {:vneutral, {:nvar, 0}}
  defp z_val, do: {:vctor, q("E", :Z), []}
  defp s(v), do: {:vctor, q("E", :S), [v]}

  # ---- independent oracle: is the solved subst a genuine unifier? ------------

  defp apply_subst({:var, k} = v, subst) do
    case Map.get(subst, k) do
      nil -> v
      other -> apply_subst(other, subst)
    end
  end

  defp apply_subst(t, subst) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&apply_subst(&1, subst)) |> List.to_tuple()

  defp apply_subst(l, subst) when is_list(l), do: Enum.map(l, &apply_subst(&1, subst))
  defp apply_subst(x, _subst), do: x

  defp neutral_env(n), do: for(i <- 0..(n - 1), do: {:vneutral, {:nvar, n - 1 - i}})

  # Rebuild, exactly as `unify_indices` does, the two branch-frame index vectors:
  # the ctor's result_indices (vars < arity) and the shifted scrutinee vector.
  defp branch_frame_vectors(ctx, cname, scrut_values) do
    sig = Context.signature(ctx)
    %{args: tele, result_indices: result_indices} = Inductive.get_ctor(sig, cname)
    arity = length(tele)
    outer_depth = Context.length(ctx)

    scrut_shifted =
      Enum.map(scrut_values, fn v -> v |> Quote.reify(outer_depth) |> Term.shift(arity, 0) end)

    {result_indices, scrut_shifted, arity, outer_depth}
  end

  # Assert the solved subst genuinely unifies the two branch-frame vectors:
  # applying it makes the ctor's result indices and the scrutinee indices
  # pairwise convertible. A dropped forced equation fails this check.
  defp assert_is_unifier(ctx, cname, scrut_values, subst) do
    {result_indices, scrut_shifted, arity, outer_depth} =
      branch_frame_vectors(ctx, cname, scrut_values)

    n = arity + outer_depth
    env = neutral_env(n)
    sig = Context.signature(ctx)

    Enum.zip(result_indices, scrut_shifted)
    |> Enum.each(fn {r, s} ->
      r2 = apply_subst(r, subst)
      s2 = apply_subst(s, subst)

      assert {:ok, true} = Conv.conv_within?(r2, s2, env, n, sig, @fuel),
             "solved subst is not a unifier: #{inspect(r2)} !≡ #{inspect(s2)} under #{inspect(subst)}"
    end)
  end

  defp solve(ctx, scrut_values) do
    assert {:solved, subst} =
             Kernel.branch_unify(ctx, q("E", :Eqv), q("E", :refl), scrut_values)

    subst
  end

  # ---- Obligation 1: REACH (variable-first must unify) -----------------------

  test "REACH: Eqv(S(a), S(Z())) [variable-first] returns a genuine unifier" do
    ctx = ctx1(eqv_sig())
    scrut = [s(a_val()), s(z_val())]
    subst = solve(ctx, scrut)
    assert_is_unifier(ctx, q("E", :refl), scrut, subst)
  end

  # ---- Obligation 2: CONTROL (ground-first stays a unifier) ------------------

  test "CONTROL: Eqv(S(Z()), S(a)) [ground-first] returns a genuine unifier" do
    ctx = ctx1(eqv_sig())
    scrut = [s(z_val()), s(a_val())]
    subst = solve(ctx, scrut)
    assert_is_unifier(ctx, q("E", :refl), scrut, subst)
  end

  # ---- Obligation 3: SYMMETRY (both orders agree) ----------------------------

  test "SYMMETRY: both argument orders of S(a)/S(Z()) reach a genuine unifier" do
    ctx = ctx1(eqv_sig())

    var_first = [s(a_val()), s(z_val())]
    ground_first = [s(z_val()), s(a_val())]

    assert_is_unifier(ctx, q("E", :refl), var_first, solve(ctx, var_first))
    assert_is_unifier(ctx, q("E", :refl), ground_first, solve(ctx, ground_first))
  end
end
