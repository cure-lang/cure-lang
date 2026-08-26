defmodule Antigen.Meta.WeakKernelTest do
  use ExUnit.Case, async: true
  alias Antigen.Meta.WeakKernel

  @single [
    infer_accepts_all: :infer,
    infer_wrong_type: :infer,
    check_accepts_all: :check,
    positive_accepts_all: :positive?,
    conv_always_true: :conv_within,
    conv_exhausts_fuel: :conv_within
  ]

  test "real/0 maps each op to the real kernel capture" do
    r = WeakKernel.real()
    assert r.infer == (&Cure.Core.Kernel.infer/2)
    assert r.check == (&Cure.Core.Kernel.check/3)
    assert r.conv_within == (&Cure.Core.Conv.conv_within?/6)
    assert r.positive? == (&Cure.Core.Inductive.positive?/2)
    assert r.check_def == (&Cure.Core.Kernel.check_def/2)
    assert r.check_family == (&Cure.Core.Kernel.check_family/2)
    assert r.check_ctor == (&Cure.Core.Kernel.check_ctor/3)
  end

  test "each single-key weakening overrides exactly its key, leaving the rest real" do
    r = WeakKernel.real()

    for {name, mapkey} <- @single do
      w = WeakKernel.weaken(name)
      refute Map.fetch!(w, mapkey) == Map.fetch!(r, mapkey)
      for {k, v} <- r, k != mapkey, do: assert(Map.fetch!(w, k) == v)
    end
  end

  test "universe_accepts_all overrides all three check_* keys, leaving the rest real" do
    r = WeakKernel.real()
    w = WeakKernel.weaken(:universe_accepts_all)
    for k <- [:check_def, :check_family, :check_ctor], do: refute(Map.fetch!(w, k) == Map.fetch!(r, k))
    for k <- [:infer, :check, :conv_within, :positive?], do: assert(Map.fetch!(w, k) == Map.fetch!(r, k))
  end

  test "the permissive stubs behave as specified" do
    assert WeakKernel.weaken(:check_accepts_all).check.(:ctx, :t, :ty) == :ok
    assert WeakKernel.weaken(:positive_accepts_all).positive?.(:env, :fam) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_def.(:env, :dn) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_family.(:env, :fam) == :ok
    assert WeakKernel.weaken(:universe_accepts_all).check_ctor.(:env, :fam, :ctor) == :ok
    assert WeakKernel.weaken(:conv_always_true).conv_within.(1, 2, 3, 4, 5, 6) == {:ok, true}
    assert WeakKernel.weaken(:conv_exhausts_fuel).conv_within.(1, 2, 3, 4, 5, 6) == :fuel_exhausted
    # accept-all infer returns {:ok, _} even for a blatantly ill-typed term
    assert {:ok, _} =
             WeakKernel.weaken(:infer_accepts_all).infer.(
               Cure.Core.Context.empty(Cure.Core.Env.empty()),
               {:app, {:ctor, :Z, []}, {:ctor, :Z, []}}
             )
  end
end
