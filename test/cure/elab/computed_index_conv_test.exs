defmodule Cure.Elab.ComputedIndexConvTest do
  @moduledoc """
  A computed index in ARGUMENT position must unify up-to-δ: feeding
  `seqg(x,y) : G(dmeet(d1,d2))` to a constructor expecting `G(DDec)` requires the
  elaborator's index unification to reduce `dmeet(DDec,DDec) ≡ DDec`
  (`Unify.unify/4`'s δ-convertibility fallback through the trusted `Conv`). This
  is Idris parity (oracle `frp/frp05_computed_index_arg`). The fallback uses the
  real conversion — so a genuinely non-decoupled index (`dmeet(DCau,DDec) = DCau`)
  fed where `DDec` is required must still REJECT (soundness control).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @hdr """
  mod M
    type Dec = DDec | DCau
    fn dmeet(a: Dec, b: Dec) -> Dec = match a
      DDec() -> match b
        DDec() -> DDec()
        DCau() -> DCau()
      DCau() -> DCau()
    type G indices (d: Dec)
      mkd : G(DDec)
      seqg : G(d1) -> G(d2) -> G(dmeet(d1, d2))
      need : G(DDec) -> G(DCau)
  """

  test "a computed index dmeet(DDec,DDec) unifies with DDec in argument position" do
    src = @hdr <> "  fn f(x: G(DDec), y: G(DDec)) -> G(DCau) = need(seqg(x, y))\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "SOUNDNESS: a non-decoupled computed index dmeet(DCau,DDec)=DCau is rejected where DDec is required" do
    src = @hdr <> "  fn f(x: G(DCau), y: G(DDec)) -> G(DCau) = need(seqg(x, y))\nend\n"
    assert {:error, _} = Program.elaborate(src)
  end
end
