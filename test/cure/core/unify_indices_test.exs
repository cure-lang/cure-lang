defmodule Cure.Core.UnifyIndicesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context}
  alias Cure.Elab.Program

  # Families/constructors elaborate to owner-qualified identities (`M#SameLen`,
  # `G#box`, `G#S`, …). `branch_unify` and the hand-built scrutinee `{:vctor, …}`
  # values must name them canonically — a bare name resolves to no registered ctor
  # and every match degrades to `:impossible`. (`Nat` is declared per-module and
  # coexists with the prelude's `Std.Nat#Nat`, so bare resolution is ambiguous;
  # qualify with the module owner explicitly.)
  defp q(owner, name), do: Cure.Elab.Name.qualify(owner, name)

  @src "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"

  defp sig,
    do:
      (fn ->
         {:ok, s} = Program.elaborate(@src)
         s
       end).()

  test "matching `same : SameLen(k,k)` against SameLen(a,b) forces b := a" do
    s = sig()
    # Two `Context.extend` calls give two outer vars: `a` (extended first) at
    # level 0, `b` (extended second) at level 1. `branch_unify`'s scrut_indices
    # are VALUES (levels); `unify_indices` reifies them to indices internally.
    ctx =
      Context.empty(s)
      |> Context.extend({:vdata, q("M", :Nat), []})
      |> Context.extend({:vdata, q("M", :Nat), []})

    # scrutinee index VALUES for [a, b] (SameLen(a, b)).
    scrut = [{:vneutral, {:nvar, 0}}, {:vneutral, {:nvar, 1}}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, q("M", :SameLen), q("M", :same), scrut)
    # `same` has arity 1 (the implicit `k`); the forced entry keys the OUTER var (>= arity).
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced != []
    assert {_k, {:var, _}} = hd(forced)
  end

  # --- Guard tests (Step 5): occurs / injectivity / conflict / no-regression ---

  # Families used by the guard tests. `box : Box(k)` gives a pure ctor-arg-only
  # solve; `vs : Vone(S(k))` exercises same-ctor injectivity; `vz : Vone(Z)`
  # exercises a rigid-head conflict.
  @guard_src "mod G\n  type Nat = Z | S(Nat)\n  type Box indices (n: Nat)\n    box : Box(k)\n  type Vone indices (n: Nat)\n    vs : Vone(S(k))\n    vz : Vone(Z)\nend\n"

  defp guard_sig,
    do:
      (fn ->
         {:ok, s} = Program.elaborate(@guard_src)
         s
       end).()

  defp one_var_ctx(s), do: Context.extend(Context.empty(s), {:vdata, q("G", :Nat), []})

  # Does any key of `subst` occur in its own bound value? (a cyclic binding)
  defp cyclic?(subst) do
    Enum.any?(subst, fn {k, v} -> occurs?(k, v) end)
  end

  defp occurs?(key, {:var, k}), do: k == key
  defp occurs?(key, t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&occurs?(key, &1))
  defp occurs?(key, l) when is_list(l), do: Enum.any?(l, &occurs?(key, &1))
  defp occurs?(_key, _), do: false

  # (a) Cycle rule (Agda Rules/LHS/Unify.hs): `SameLen(a, S(a))` matched against
  # `same : SameLen(k, k)` forces a = k = S(a), i.e. the strongly-rigid cyclic
  # equation `a = S(a)`. By acyclicity of Nat this is ABSURD, so the branch is
  # discharged :impossible (Idris/Agda-faithful) — the precise verdict that fixes
  # oracle cyc01. This SUPERSEDES the earlier conservative pin, which degraded the
  # cycle to a non-cyclic solve; the soundness obligation that pin guarded (never
  # FABRICATE a cyclic substitution) is preserved a fortiori — :impossible binds
  # nothing. See `Cure.Core.CycleRuleTest` and kernel `strongly_rigid_occurs?`.
  test "(a) cycle rule: `same : SameLen(k,k)` vs SameLen(a, S(a)) is :impossible (a = S(a) absurd)" do
    s = sig()
    # Single outer var `a`; second scrutinee index is the ctor value `S(a)`.
    ctx = one_var_ctx(s)
    scrut = [{:vneutral, {:nvar, 0}}, {:vctor, q("M", :S), [{:vneutral, {:nvar, 0}}]}]
    assert :impossible = Kernel.branch_unify(ctx, q("M", :SameLen), q("M", :same), scrut)
  end

  test "(b) injectivity: `vs : Vone(S(k))` vs Vone(S(a)) decomposes to k := a" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vctor, q("G", :S), [{:vneutral, {:nvar, 0}}]}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, q("G", :Vone), q("G", :vs), scrut)
    # arity 1: the ctor-arg key 0 is solved to the scrutinee var; no cyclic bind.
    assert Map.has_key?(subst, 0)
    assert {:var, _} = Map.get(subst, 0)
    refute cyclic?(subst)
  end

  test "(c) conflict: `vz : Vone(Z)` vs Vone(S(a)) is :impossible" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vctor, q("G", :S), [{:vneutral, {:nvar, 0}}]}]
    assert :impossible = Kernel.branch_unify(ctx, q("G", :Vone), q("G", :vz), scrut)
  end

  test "(d) no-regression: plain ctor-arg-only `box : Box(k)` vs Box(a) has no forced entry" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vneutral, {:nvar, 0}}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, q("G", :Box), q("G", :box), scrut)
    # Exactly the prior behavior: ctor-arg key (< arity 1) := scrutinee var; no
    # forced scrutinee-var (>= arity) entries induced.
    assert {:var, _} = Map.get(subst, 0)
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced == []
  end

  # --- (e) multi-key cycle regression (TCB gate falsifier, spec §4.1) ---
  #
  # `c : T(a, a, b, b)` matched against T(i, j, j, i) induces both `j := i` and
  # `i := j`. Before the union-find `resolve_index_var` guard, this produced the
  # cyclic substitution {i↦j, j↦i} — which `replace_branch_vars` applies as a
  # variable SWAP instead of collapsing `i ≡ j`, a real correctness defect in a
  # TCB path. The verdict must be a SOLVED, ACYCLIC substitution (i and j collapse
  # to a single representative), never a cycle.
  @cycle_src "mod C\n  type Nat = Z | S(Nat)\n  type T indices (i0: Nat, i1: Nat, i2: Nat, i3: Nat)\n    c : T(a, a, b, b)\nend\n"
  defp cycle_sig,
    do:
      (fn ->
         {:ok, s} = Program.elaborate(@cycle_src)
         s
       end).()

  # A substitution is cyclic iff chasing var-edges from some key revisits a key.
  defp acyclic?(subst) do
    not Enum.any?(Map.keys(subst), fn start -> chase_cycle?(start, subst, MapSet.new()) end)
  end

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

  test "(e) multi-key cycle: `c : T(a,a,b,b)` vs T(i,j,j,i) collapses i≡j WITHOUT a cyclic subst" do
    s = cycle_sig()

    ctx =
      Context.empty(s)
      |> Context.extend({:vdata, :Nat, []})
      |> Context.extend({:vdata, :Nat, []})

    i = {:vneutral, {:nvar, 0}}
    j = {:vneutral, {:nvar, 1}}

    assert {:solved, subst} = Kernel.branch_unify(ctx, q("C", :T), q("C", :c), [i, j, j, i])
    # The soundness obligation: no cyclic substitution.
    assert acyclic?(subst), "expected acyclic subst, got #{inspect(subst)}"
    # And the collapse is real: every OUTER key (>= arity 2) resolves to one
    # representative — i and j are genuinely unified, not swapped.
    outer_keys = subst |> Map.keys() |> Enum.filter(&(&1 >= 2))
    assert outer_keys != []
    reps = outer_keys |> Enum.map(&rep(&1, subst)) |> Enum.uniq()
    assert length(reps) == 1, "expected i,j to collapse to one rep, got reps #{inspect(reps)} in #{inspect(subst)}"
  end
end
