defmodule Cure.Elab.CtorResultFrameTest do
  @moduledoc """
  A constructor whose result type has COMPUTED indices over the caller's context
  variables (`seq`/`seqd` : `… -> SF(app(av,cv), app(bv,cv), …)`) must have that
  result type evaluated in the CALLER's frame. When such a constructor is applied
  as ANOTHER constructor's argument (`loop(seqd(a,b))`), the inferred result type
  drives meta-solving for the outer constructor's erased indices — so a mis-framed
  result (evaluated under `[]`) mis-levels `av,bv,cv` and corrupts the outer
  application. `loop(seqd(a,b))` isolates this framing bug from the δ-reduction
  path (its result index is a literal `DDec`, no `dmeet` to reduce);
  `loop(seq(a,b))` exercises both fixes together (oracle `frp/frp06`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @hdr """
  mod M
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
      seqd : SF(av, bv, DDec) -> SF(bv, cv, DDec) -> SF(av, cv, DDec)
      seq : SF(av, bv, d1) -> SF(bv, cv, d2) -> SF(av, cv, dmeet(d1, d2))
      loop : SF(app(av, cv), app(bv, cv), DDec) -> SF(av, bv, DCau)
  """

  test "FRAME: loop wrapping a compound computed-index ctor (direct DDec, no delta)" do
    src =
      @hdr <>
        "  fn cl({av: SList}, {bv: SList}, {cv: SList}, {mv: SList}, a: SF(app(av, cv), mv, DDec), b: SF(mv, app(bv, cv), DDec)) -> SF(av, bv, DCau) = loop(seqd(a, b))\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "composed loop loop(seq(a,b)) — framing + computed-index delta together" do
    src =
      @hdr <>
        "  fn cl({av: SList}, {bv: SList}, {cv: SList}, {mv: SList}, a: SF(app(av, cv), mv, DDec), b: SF(mv, app(bv, cv), DDec)) -> SF(av, bv, DCau) = loop(seq(a, b))\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end
end
