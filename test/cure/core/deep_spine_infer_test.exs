defmodule Cure.Core.DeepSpineInferTest do
  # Guards the linearity of `infer`/`check` on deep constructor spines.
  #
  # `nf` and `conv?` were already linear (eval-once + one value walk), but `infer`
  # was O(n²): `check_ctor_app_rec`/`do_spine` re-evaluated the ENTIRE remaining
  # surface sub-tower (`Eval.eval(arg, env)`) at every spine level. The fix threads
  # each field's value UP from its recursive check (Idris's value-returning
  # checker), so a depth-n tower is checked in one linear pass. This test both
  # pins correctness at depth and fails loudly (timeout) if the quadratic returns.
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context}

  @nat {:data, :Nat, [], []}

  defp nat_ctx do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
        Inductive.ctor(:Zero, [], []),
        Inductive.ctor(:Succ, [{:n, @nat}], [])
      ])

    Context.empty(env)
  end

  # Succ(Succ(... Zero)) of the given depth, built without deep Elixir recursion.
  defp tower(depth) do
    Enum.reduce(1..depth//1, {:ctor, :Zero, []}, fn _, acc -> {:ctor, :Succ, [acc]} end)
  end

  test "infer types a shallow Nat tower correctly" do
    assert {:ok, {:vdata, :Nat, []}} = Kernel.infer(nat_ctx(), tower(10))
  end

  test "check accepts a shallow Nat tower against Nat" do
    nat_val = Cure.Core.Eval.eval(@nat, [])
    assert :ok == Kernel.check(nat_ctx(), tower(10), nat_val)
  end

  test "infer on a deep Nat tower stays linear (no O(n^2) re-eval)" do
    ctx = nat_ctx()
    depth = 30_000

    {micros, result} = :timer.tc(fn -> Kernel.infer(ctx, tower(depth)) end)

    assert {:ok, {:vdata, :Nat, []}} = result

    # Pre-fix this depth took ~12 s (quadratic). Linear is tens of ms; the 4 s
    # ceiling is a wide margin that still catches a reintroduced quadratic.
    assert micros < 4_000_000,
           "infer on a depth-#{depth} tower took #{Float.round(micros / 1000, 1)} ms " <>
             "(> 4000 ms) — the O(n^2) spine re-eval has likely regressed"
  end

  test "infer types the '😀' codepoint as an eager Nat tower (the motivating case)" do
    # U+1F600 GRINNING FACE. As an eagerly-built Nat literal this is a
    # 128_512-deep Succ tower — the case that took 4m23s under the O(n²) infer.
    # Linear now types it in a fraction of a second. (Char stays a native int
    # literal in the surface language for exactly this reason; this test only
    # pins that even the pathological eager tower is no longer quadratic.)
    depth = ?😀
    assert depth == 128_512
    ctx = nat_ctx()

    {micros, result} = :timer.tc(fn -> Kernel.infer(ctx, tower(depth)) end)

    assert {:ok, {:vdata, :Nat, []}} = result

    assert micros < 4_000_000,
           "infer on the '😀' (depth-#{depth}) tower took " <>
             "#{Float.round(micros / 1000, 1)} ms (> 4000 ms) — quadratic infer has regressed"
  end
end
