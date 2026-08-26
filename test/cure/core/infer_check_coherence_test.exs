defmodule Cure.Core.InferCheckCoherenceTest do
  @moduledoc """
  Task #14 (spec 2026-07-09-infer-check-coherence): check subsumes infer+conv
  on the params-on-spine ctor spelling — the shape whose arity the fields-only
  checking strategy cannot measure. Lean-aligned (check = infer + def-eq).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Kernel}

  # Reuse k6_param_ctor_infer_test.exs's env/ctx construction verbatim.
  defp ctx do
    env = Builtins.seed(Env.empty())
    Context.empty(env)
  end

  @spine_refl {:ctor, :reflexive, [{:data, :"Std.Int#Int", [], []}, {:int_lit, 3}]}

  test "coherence: the spine reflexive checks against its own inferred type" do
    ctx = ctx()
    assert {:ok, inferred} = Kernel.infer(ctx, @spine_refl)
    assert :ok = Kernel.check(ctx, @spine_refl, inferred)
  end

  test "wrong-endpoint expected rejects with conversion_failure, not ctor_arity" do
    ctx = ctx()
    wrong = {:vdata, :"Std.Equivalent#Equivalent", [{:vdata, :"Std.Int#Int", []}, {:vint, 3}, {:vint, 4}]}
    assert {:error, {:conversion_failure, _, _}} = Kernel.check(ctx, @spine_refl, wrong)
  end

  test "genuinely malformed arity still rejects :ctor_arity" do
    ctx = ctx()
    bad = {:ctor, :reflexive, [{:data, :"Std.Int#Int", [], []}, {:int_lit, 3}, {:int_lit, 3}]}
    {:ok, good_ty} = Kernel.infer(ctx, @spine_refl)
    assert {:error, :ctor_arity} = Kernel.check(ctx, bad, good_ty)
  end

  test "checking position inside inference: (λ p : Eq(Int,3,3). p)(spine_refl) infers" do
    ctx = ctx()
    eq_ty = {:data, :"Std.Equivalent#Equivalent", [{:data, :"Std.Int#Int", [], []}], [{:int_lit, 3}, {:int_lit, 3}]}
    term = {:app, {:lam, Cure.Core.Grade.unrestricted(), eq_ty, {:var, 0}}, @spine_refl}
    assert {:ok, _} = Kernel.infer(ctx, term)
  end
end
