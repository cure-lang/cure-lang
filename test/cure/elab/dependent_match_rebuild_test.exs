defmodule Cure.Elab.DependentMatchRebuildTest do
  @moduledoc """
  A dependent match whose branch bodies RECONSTRUCT a constructor at the branch-
  refined index (`match s | prim() -> prim() | seq(l,r) -> seq(l,r)`). The nullary
  `prim`/`dpre` have erased indices that no present argument determines, so they
  must be pinned from the branch's expected type (checking-mode constructor
  elaboration, `pin_ctor_result`). Idris parity (oracle
  `frp/frp07_dependent_match_rebuild`). The pin still runs the real conversion, so
  reconstructing the WRONG constructor at a refined index must REJECT (soundness).
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
      dpre : SF(av, bv, DDec)
      seq : SF(av, bv, d1) -> SF(bv, cv, d2) -> SF(av, cv, dmeet(d1, d2))
  """

  test "reconstructing each constructor at the branch-refined index elaborates" do
    src =
      @hdr <>
        "  fn ident({as: SList}, {bs: SList}, {d: Dec}, s: SF(as, bs, d)) -> SF(as, bs, d) = match s\n    prim() -> prim()\n    dpre() -> dpre()\n    seq(l, r) -> seq(l, r)\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "SOUNDNESS: reconstructing the WRONG constructor at a refined index is rejected" do
    # The `prim` branch is refined to `SF(as,bs,DCau)`, but returns `dpre()`
    # (`SF(_,_,DDec)`). DDec ≢ DCau, so the pin's conversion must reject.
    src =
      @hdr <>
        "  fn bad({as: SList}, {bs: SList}, {d: Dec}, s: SF(as, bs, d)) -> SF(as, bs, d) = match s\n    prim() -> dpre()\n    dpre() -> dpre()\n    seq(l, r) -> seq(l, r)\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
