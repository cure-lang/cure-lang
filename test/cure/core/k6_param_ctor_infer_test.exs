defmodule Cure.Core.K6ParamCtorInferTest do
  @moduledoc """
  K6 / spec §E.1 — constructor parameters ride the spine (Lean's kernel form), so
  a parameter-bearing constructor is checkable in INFERENCE position (not only
  checking mode). `refl : {w:a} -> Equivalent(a, w, w)` has family parameter `a`; supplied
  in the spine ahead of the witness, the kernel reads + re-checks it and
  synthesizes the constructor's `vdata` — no metavariable inference in the TCB.

  This unblocks the Eq-cluster's `bridge_step` (rw07), which today falls back to
  the primitive `{:refl}` precisely because a bare inductive `refl` had no
  inference rule (`:ctor_requires_checking_mode`).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel}

  test "infer accepts a param constructor with the param in the spine" do
    ctx = Context.empty(Builtins.seed(Env.empty()))
    # refl at a=Int, w=3  ->  Equivalent(Int, 3, 3).  Spine = [param a, witness w].
    term = {:ctor, :reflexive, [{:data, :"Std.Int#Int", [], []}, {:int_lit, 3}]}

    assert {:ok, {:vdata, :"Std.Equivalent#Equivalent", [{:vdata, :"Std.Int#Int", []}, {:vint, 3}, {:vint, 3}]}} =
             Kernel.infer(ctx, term)
  end

  test "infer still rejects a param constructor with params ABSENT (checking-mode only)" do
    ctx = Context.empty(Builtins.seed(Env.empty()))
    # Fields-only spine (no param) stays inference-mode-rejected — unchanged.
    term = {:ctor, :reflexive, [{:int_lit, 3}]}

    assert {:error, {:ctor_requires_checking_mode, :"Std.Equivalent#Equivalent"}} =
             Kernel.infer(ctx, term)
  end
end
