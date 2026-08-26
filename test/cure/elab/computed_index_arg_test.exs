defmodule Cure.Elab.ComputedIndexArgTest do
  @moduledoc """
  Regression: an index variable that appears ONLY inside a computed
  (non-family) index expression in a constructor's ARGUMENT type must still be
  inferred as an implicit binder.

  `loop`-style FRP constructors have exactly this shape — the fed-back signal
  vector `cv` occurs only inside `app(av, cv)` in the argument, never as a bare
  family index arg. Before the fix `collect_implicit_vars` only harvested bare
  variables sitting directly in a family application, so `cv` dangled and the
  kernel reported `:unknown_global` for the whole family.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type Sig = SigC | SigE
    type Dec = DDec | DCau
    fn dmeet(a: Dec, b: Dec) -> Dec = match a
      DDec() -> match b
        DDec() -> DDec()
        DCau() -> DCau()
      DCau() -> DCau()
    type SList = SNil | SCons(Sig, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(x, r) -> SCons(x, app(r, ys))
    type SF indices (i: SList, o: SList, dec: Dec)
      prim : SF(av, bv, DCau)
      dpre : SF(av, bv, DDec)
      seq : SF(av, bv, d1) -> SF(bv, cv, d2) -> SF(av, cv, dmeet(d1, d2))
      loop : SF(app(av, cv), app(bv, cv), DDec) -> SF(av, bv, DCau)
  """

  test "constructor with computed index in argument position (existential cv) elaborates" do
    assert {:ok, _env} = Program.elaborate("mod CIdx\n" <> @preamble <> "end\n")
  end

  test "the loop constructor is usable: well-formed decoupled feedback accepts" do
    # A decoupled (DDec) feedback body loops (the fed-back `cv` occurs only inside
    # the computed `app(av, cv)` argument index — the shape the fix enables).
    # NB: `loop(seq(a, b))` — a body that is itself a COMPOSITION whose Dec index
    # is `dmeet(DDec, DDec)` — is a SEPARATE, scope-pinned completeness gap: the
    # elaborator's argument index-UNIFICATION does not normalise a computed index
    # (`dmeet(DDec,DDec) ≡ DDec`) the way body-vs-return kernel conversion does.
    # That is orthogonal to this implicit-inference fix; see the plan's Phase-6
    # note. Here the body is passed directly, isolating the fix under test.
    src =
      "mod CIdx\n" <>
        @preamble <>
        "  fn wf({av: SList}, {bv: SList}, {cv: SList}, body: SF(app(av, cv), app(bv, cv), DDec)) -> SF(av, bv, DCau) = loop(body)\n" <>
        "end\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "soundness control: causal feedback body is rejected (instantaneous cycle)" do
    src =
      "mod CIdx\n" <>
        @preamble <>
        "  fn bad({av: SList}, {bv: SList}, {cv: SList}, body: SF(app(av, cv), app(bv, cv), DCau)) -> SF(av, bv, DCau) = loop(body)\n" <>
        "end\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
