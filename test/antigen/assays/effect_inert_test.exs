defmodule Antigen.Assays.EffectInertTest do
  @moduledoc """
  The `kernel/effect_inert` antibody (design `2026-07-09-effect-type-former-design.md`
  §9): the inert `Effect`/`pure`/`bind` signature must never acquire a reduction —
  no monad laws. `nf` preserves the effect skeleton and `bind(pure(a), k)` is
  definitionally distinct from both `k(a)` and `pure(a)`.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.KernelLaw
  alias Antigen.Generators.EffectInert
  alias Antigen.{Challenge, Runner}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Conv, Kernel, Context, Env, Inductive}

  @omega Cure.Core.Grade.unrestricted()
  @effect_int {:effect_type, {:data, :Int, [], []}}

  defp ch(term),
    do:
      Challenge.new(
        kind: :typed_term,
        assay: "kernel/effect_inert",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: @effect_int, term: term}
      )

  test "runner routes kernel/effect_inert to KernelLaw and it is registered" do
    assert Runner.assay_module_for("kernel/effect_inert") == Antigen.Assays.KernelLaw
    assert "kernel/effect_inert" in Runner.registered_assays()
  end

  test "the assay returns :ok on every generated effect cell (sound kernel)" do
    for {_type, term, note} <- EffectInert.cases() do
      assert :ok == KernelLaw.run(ch(term)), "effect_inert falsely fired on #{note}"
    end
  end

  test "gen/0 produces every declared cover cell (coverage is real)" do
    hit =
      for c <- B.interp(EffectInert.gen()) |> Enum.take(400), into: MapSet.new(), do: c.cover_tag

    for {_assay, cell} <- EffectInert.cover_cells() do
      assert MapSet.member?(hit, cell), "declared cover cell #{cell} was never generated"
    end
  end

  # Teeth: the property is testing a fact a monad law would break. The generator
  # emits `bind(pure(3), λx. pure(x))`; here we prove — via the public kernel API,
  # NOT the assay — that it is well-typed AND that left identity is genuinely
  # FALSE. If a reduction crept into Eval/Conv/Normalise, the two `refute`s below
  # would flip and the assay would fire; the final assert pins that it currently
  # passes on this exact term.
  test "bind(pure(a), k) is a real, non-vacuous left-identity check" do
    sig = Antigen.CanonBuiltins.seed(Env.empty())
    ctx = Context.empty(sig)
    int_fid = Inductive.builtin(sig, :int)
    a = {:int_lit, 3}
    k = {:lam, @omega, {:data, :Int, [], []}, {:effect_pure, {:var, 0}}}
    t = {:effect_bind, {:effect_pure, a}, k}

    assert {:ok, {:veffect_type, {:vdata, ^int_fid, []}}} = Kernel.infer(ctx, t)

    # k(a) here reduces to pure(3); neither it nor pure(3) may be convertible with t.
    refute Conv.conv?(t, {:app, k, a}, [], 0)
    refute Conv.conv?(t, {:effect_pure, a}, [], 0)

    assert :ok == KernelLaw.run(ch(t))
  end

  # nf reduces the PAYLOAD of `pure((λx.x) 3)` to `3` (so the check is not
  # vacuously :ok because nf did nothing) while leaving the `pure` node intact —
  # exactly the "reduce subterms, preserve effect structure" contract.
  test "nf reduces an effect node's payload but preserves the effect skeleton" do
    t = {:effect_pure, {:app, {:lam, @omega, {:data, :Int, [], []}, {:var, 0}}, {:int_lit, 3}}}
    nf = Kernel.normalize(Context.empty(Antigen.CanonBuiltins.seed(Env.empty())), t)

    assert nf == {:effect_pure, {:int_lit, 3}}, "nf failed to reduce the payload redex"
    assert nf != t, "nf was a no-op — the skeleton-preservation check would be vacuous"
    assert :ok == KernelLaw.run(ch(t))
  end
end
