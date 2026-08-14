defmodule Antigen.UnifyIndicesAntibodyTest do
  @moduledoc """
  TCB antibody — the resolve-before-bind FORCED-EQUATION step in the kernel index
  unifier (`Cure.Core.Kernel.unify_indices`/`bind_index`, spec §4.1) stays sound
  and terminating.

  Guards the change (kernel `ea8b26c`, fixed in `878ccc9`) that lets a matched
  constructor's result-index vector FORCE equations back onto the scrutinee's
  outer index vars (Agda's "Solution" step). The first cut of that change bound
  each forced pair blindly, so `c : T(a,a,b,b)` matched against `T(i,j,j,i)`
  planted BOTH `j := i` and `i := j` — a multi-key cyclic substitution `{i↦j,
  j↦i}` that `replace_branch_vars` applies as a variable SWAP instead of
  collapsing `i ≡ j`. The fix makes `bind_index` first CHASE its candidate term
  to its representative via `resolve_index_var` (kernel.ex `bind_index`), keeping
  `subst` a **union-find forest**: the second forced edge resolves to the same
  class as its key and degrades to the `key == rterm` no-op, so `i`/`j` collapse
  to one representative and no cycle can form. That union-find `resolve_index_var`
  guard is the invariant this antibody pins.

  Three obligations (spec §4.1):

    * CHAINED-CHASE TERMINATION — a scrutinee var forced through ≥2 intermediate
      already-bound keys in one branch (`c8 : T8(a,a,b,b,c,c,d,d)` vs the 4-cycle
      rotation `T8(i,j,j,k,k,l,l,i)`) must RETURN, not loop. Asserted under a
      bounded `Task` harness (macOS has no `timeout`).

    * NO MULTI-KEY BINDING CYCLE — the named `c : T(a,a,b,b)` vs `T(i,j,j,i)`
      case AND a deeper 3-way rotation `c6 : T6(a,a,b,b,c,c)` vs `T6(i,j,j,k,k,i)`
      each yield a `{:solved, subst}` whose var-edge graph is ACYCLIC (chasing
      from every key never revisits a key) and whose outer vars collapse to a
      SINGLE representative — a genuine unification, never a swap. If ANY
      construction still yields a cycle the fix is incomplete: STOP, do not weaken
      the assertion.

    * NO NORMAL-FORM COLLAPSE — a forced entry (`key >= arity`, `k ↦ t`) is
      produced ONLY when it is a real unifier: applying the whole solved subst to
      the two original branch-frame index vectors makes them pairwise CONVERTIBLE
      (`Cure.Core.Conv.conv_within?`). A spurious forced equation would not
      reconcile the vectors and would fail this check.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Quote, Term, Inductive}
  alias Cure.Elab.Program

  # Families/constructors elaborate to owner-qualified identities; `branch_unify`
  # and `Inductive.get_ctor` must be named canonically or the ctor is not found.
  defp q(owner, name), do: Cure.Elab.Name.qualify(owner, name)

  # ---- fixtures -------------------------------------------------------------

  defp elaborate!(src) do
    {:ok, s} = Program.elaborate(src)
    s
  end

  # SameLen: `same : SameLen(k, k)` — the minimal forced-equation shape
  # (arity 1; matching against SameLen(a, b) forces b := a).
  defp samelen_sig,
    do:
      elaborate!(
        "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"
      )

  # T(a,a,b,b): the named multi-key-cycle falsifier (arity 2).
  defp t4_sig,
    do:
      elaborate!(
        "mod C4\n  type Nat = Z | S(Nat)\n  type T indices (i0: Nat, i1: Nat, i2: Nat, i3: Nat)\n    c : T(a, a, b, b)\nend\n"
      )

  # T6(a,a,b,b,c,c): a deeper 3-way rotation variant (arity 3).
  defp t6_sig,
    do:
      elaborate!(
        "mod C6\n  type Nat = Z | S(Nat)\n  type T6 indices (i0: Nat, i1: Nat, i2: Nat, i3: Nat, i4: Nat, i5: Nat)\n    c6 : T6(a, a, b, b, c, c)\nend\n"
      )

  # T8(a,a,b,b,c,c,d,d): a 4-cycle rotation — the chained-chase termination case
  # (arity 4; the chase must hop through 3 intermediate keys).
  defp t8_sig,
    do:
      elaborate!(
        "mod C8\n  type Nat = Z | S(Nat)\n  type T8 indices (i0: Nat, i1: Nat, i2: Nat, i3: Nat, i4: Nat, i5: Nat, i6: Nat, i7: Nat)\n    c8 : T8(a, a, b, b, c, c, d, d)\nend\n"
      )

  # A context with `n` outer Nat vars in scope; scrutinee index VALUES are levels.
  defp ctx_with(sig, n, owner),
    do:
      Enum.reduce(1..n, Context.empty(sig), fn _, c ->
        Context.extend(c, {:vdata, q(owner, :Nat), []})
      end)

  defp lvl(i), do: {:vneutral, {:nvar, i}}

  # ---- subst inspection helpers (independent oracle, not kernel internals) ---

  # A substitution is cyclic iff chasing var-edges from some key revisits a key.
  defp acyclic?(subst),
    do: not Enum.any?(Map.keys(subst), fn k -> chase_cycle?(k, subst, MapSet.new()) end)

  defp chase_cycle?(k, subst, seen) do
    if MapSet.member?(seen, k) do
      true
    else
      case Map.get(subst, k) do
        {:var, k2} -> chase_cycle?(k2, subst, MapSet.put(seen, k))
        _ -> false
      end
    end
  end

  # Resolve a key through the substitution to its representative.
  defp rep(k, subst) do
    case Map.get(subst, k) do
      {:var, k2} -> rep(k2, subst)
      _ -> k
    end
  end

  defp forced_entries(subst, arity),
    do: subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= arity end)

  # Apply the (acyclic) subst as a full substitution, chasing var-edges to reps.
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

  # Neutral value env + depth for the branch de Bruijn frame of size `n`.
  defp neutral_env(n), do: for(i <- 0..(n - 1), do: {:vneutral, {:nvar, n - 1 - i}})

  @fuel 1000

  # For a solved subst carrying a forced (key >= arity) entry, assert the subst is
  # a genuine unifier: applying it to both original vectors yields pairwise
  # convertible terms (no spurious/collapsing forced equation).
  defp assert_no_collapse(ctx, cname, scrut_values, subst) do
    {result_indices, scrut_shifted, arity, outer_depth} =
      branch_frame_vectors(ctx, cname, scrut_values)

    assert forced_entries(subst, arity) != [],
           "scenario expected to induce a forced (key >= arity) entry"

    n = arity + outer_depth
    env = neutral_env(n)
    sig = Context.signature(ctx)

    Enum.zip(result_indices, scrut_shifted)
    |> Enum.each(fn {r, s} ->
      r2 = apply_subst(r, subst)
      s2 = apply_subst(s, subst)

      assert {:ok, true} = Conv.conv_within?(r2, s2, env, n, sig, @fuel),
             "forced subst is not a unifier: #{inspect(r2)} !≡ #{inspect(s2)} under #{inspect(subst)}"
    end)
  end

  # ---- Obligation 1: chained-chase termination -------------------------------

  test "chained chase through >=2 already-bound keys terminates (returns, no loop)" do
    s = t8_sig()
    ctx = ctx_with(s, 8, "C8")
    # T8(a,a,b,b,c,c,d,d) vs T8(i,j,j,k,k,l,l,i): a 4-cycle i≡j≡k≡l≡i forcing the
    # resolve chase through 3 intermediate keys.
    scrut = [lvl(0), lvl(1), lvl(1), lvl(2), lvl(2), lvl(3), lvl(3), lvl(0)]

    task = Task.async(fn -> Kernel.branch_unify(ctx, q("C8", :T8), q("C8", :c8), scrut) end)
    result = Task.yield(task, 5_000) || Task.shutdown(task)

    assert {:ok, {:solved, subst}} = result,
           "branch_unify did not return within budget (suspected chase loop): #{inspect(result)}"

    assert acyclic?(subst), "chained chase produced a cyclic subst: #{inspect(subst)}"
  end

  # ---- Obligation 2: no multi-key binding cycle ------------------------------

  test "T(a,a,b,b) vs T(i,j,j,i) collapses i≡j with an ACYCLIC subst (no swap)" do
    s = t4_sig()
    ctx = ctx_with(s, 2, "C4")
    i = lvl(0)
    j = lvl(1)

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("C4", :T), q("C4", :c), [i, j, j, i])
    assert acyclic?(subst), "expected acyclic subst, got cycle: #{inspect(subst)}"

    outer = subst |> Map.keys() |> Enum.filter(&(&1 >= 2))
    assert outer != []
    reps = outer |> Enum.map(&rep(&1, subst)) |> Enum.uniq()

    assert length(reps) == 1,
           "expected i,j to collapse to ONE rep (not a swap), got #{inspect(reps)} in #{inspect(subst)}"
  end

  test "deeper T6(a,a,b,b,c,c) vs T6(i,j,j,k,k,i) collapses i≡j≡k with an ACYCLIC subst" do
    s = t6_sig()
    ctx = ctx_with(s, 6, "C6")
    scrut = [lvl(0), lvl(1), lvl(1), lvl(2), lvl(2), lvl(0)]

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("C6", :T6), q("C6", :c6), scrut)
    assert acyclic?(subst), "expected acyclic subst, got cycle: #{inspect(subst)}"

    outer = subst |> Map.keys() |> Enum.filter(&(&1 >= 3))
    assert outer != []
    reps = outer |> Enum.map(&rep(&1, subst)) |> Enum.uniq()

    assert length(reps) == 1,
           "expected i,j,k to collapse to ONE rep, got #{inspect(reps)} in #{inspect(subst)}"
  end

  # ---- Obligation 3: no normal-form collapse ---------------------------------

  test "forced entry is a genuine unifier: SameLen(k,k) vs SameLen(a,b)" do
    s = samelen_sig()
    ctx = ctx_with(s, 2, "M")
    scrut = [lvl(0), lvl(1)]

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("M", :SameLen), q("M", :same), scrut)
    assert_no_collapse(ctx, q("M", :same), scrut, subst)
  end

  test "forced entries are genuine unifiers: T(a,a,b,b) vs T(i,j,j,i)" do
    s = t4_sig()
    ctx = ctx_with(s, 2, "C4")
    scrut = [lvl(0), lvl(1), lvl(1), lvl(0)]

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("C4", :T), q("C4", :c), scrut)
    assert_no_collapse(ctx, q("C4", :c), scrut, subst)
  end

  test "forced entries are genuine unifiers: T6(a,a,b,b,c,c) vs T6(i,j,j,k,k,i)" do
    s = t6_sig()
    ctx = ctx_with(s, 6, "C6")
    scrut = [lvl(0), lvl(1), lvl(1), lvl(2), lvl(2), lvl(0)]

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("C6", :T6), q("C6", :c6), scrut)
    assert_no_collapse(ctx, q("C6", :c6), scrut, subst)
  end
end
