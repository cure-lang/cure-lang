defmodule Cure.Core.NatLitCoverageSoundnessTest do
  @moduledoc """
  Regression for the compact-`nat_lit` ↔ `Z`/`S` soundness hole in index
  unification. A scrutinee index that reifies to a compact `{:nat_lit, n}` must
  unify with a constructor's `Z`/`S` result index EXACTLY as the `S`-tower form
  does — `2 ≡ S(S(Z))`, `0 ≡ Z` definitionally. Before the fix, `head_key`
  treated `:nat_lit` as a rigid head distinct from `{:ctor, :S}`/`{:ctor, :Z}`,
  so `unify_one({:ctor,:S,…}, {:nat_lit,2})` verdicted `:impossible` and a `case`
  on `Vone(0)` could omit `vz` — its only inhabitant — and still pass coverage.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel}

  @nat {:data, :Nat, [], []}

  # Vone(n:Nat): vz : Vone(Z), vs : Vone(S k).
  defp env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Nat, [], [], 0),
      [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, @nat}], [])]
    )
    |> Inductive.declare(
      Inductive.family(:Vone, [], [{:n, @nat}], 0),
      [
        Inductive.ctor(:vz, [], [{:ctor, :Z, []}]),
        Inductive.ctor(:vs, [{:k, @nat}], [{:ctor, :S, [{:var, 0}]}])
      ]
    )
    |> Inductive.register_builtin(:nat, :Nat)
  end

  defp ctx, do: Context.empty(env())

  test "vz is reachable on Vone(0) whether the index is Z-form or compact nat 0" do
    assert :trivial == Kernel.branch_unify(ctx(), :Vone, :vz, [{:vctor, :Z, []}])
    # THE FIX: same semantic index, compact representation, same verdict.
    assert :trivial == Kernel.branch_unify(ctx(), :Vone, :vz, [{:vnat, 0}])
  end

  test "vs is genuinely impossible on Vone(0) in both representations (0 ≠ S _)" do
    assert :impossible == Kernel.branch_unify(ctx(), :Vone, :vs, [{:vctor, :Z, []}])
    assert :impossible == Kernel.branch_unify(ctx(), :Vone, :vs, [{:vnat, 0}])
  end

  test "vs on Vone(2) solves k := 1 (injectivity through the compact literal)" do
    # 2 ≡ S(1): vs : Vone(S k) must unify and force k := 1, not be ruled out.
    assert {:solved, _subst} = Kernel.branch_unify(ctx(), :Vone, :vs, [{:vnat, 2}])
  end

  test "vz is genuinely impossible on Vone(2) (2 ≠ Z)" do
    assert :impossible == Kernel.branch_unify(ctx(), :Vone, :vz, [{:vnat, 2}])
  end
end
