defmodule Antigen.SpineCtorCoherenceAntibodyTest do
  @moduledoc """
  Task #14 antibody: the exact historical counterexample (params-on-spine
  reflexive, K6 inference spelling) round-trips infer→check through the real
  kernel. Regression here = the check-mode ctor clause stopped delegating its
  unmeasurable arity to check_via_infer.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Kernel}

  test "infer→check round-trip on the spine reflexive" do
    ctx = Context.empty(Builtins.seed(Env.empty()))
    t = {:ctor, :reflexive, [{:data, :"Std.Int#Int", [], []}, {:int_lit, 3}]}
    assert {:ok, ty} = Kernel.infer(ctx, t)
    assert :ok = Kernel.check(ctx, t, ty)
  end
end
