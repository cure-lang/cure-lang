defmodule Cure.Elab.PostponeProofArgTest do
  @moduledoc """
  Argument-order postponement for a PROOF/value argument whose type is stuck on a
  metavariable that a LATER sibling argument solves.

  A callee `consume(x, {hi}, e : elt(EFin x, hi) = OT, c : Carrier(EFin x, hi))`
  carries an implicit `hi` that the trailing `Carrier` argument determines. Called
  with the proof BEFORE the carrier, the proof's expected type `elt(EFin x, ?hi)`
  is a case-tree stuck on the unsolved `?hi`, so unifying it against the supplied
  proof's type `slt(x, k) = OT` fails — even though, once `?hi := EFin k` is solved
  by the carrier, `elt(EFin x, EFin k)` reduces to exactly `slt(x, k)`.

  Before the fix, `bidir_app_slot` halted on that unify failure, so argument ORDER
  decided typability (carrier-first elaborated, proof-first did not). This is the
  intrinsic well-scoped-BST recursion pattern in miniature. The fix defers the
  proof argument (a placeholder holds its slot) and re-checks it once the carrier
  has solved `?hi` — the assembled call is kernel-re-checked regardless.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @preamble """
    use Std.Equivalent
    type OKey = OA | OB | OC
    type OBit = OF | OT
    fn slt(x: OKey, y: OKey) -> OBit = match x
      OA() -> OT()
      OB() -> OF()
      OC() -> OF()
    type EKey = EBot | EFin(OKey) | ETop
    fn elt(a: EKey, b: EKey) -> OBit = match a
      EBot() -> OT()
      EFin(x) -> match b
        EBot() -> OF()
        EFin(y) -> slt(x, y)
        ETop() -> OT()
      ETop() -> OF()
    type Carrier indices (lo: EKey, hi: EKey)
      Mk : Carrier(lo, hi)
  """

  test "proof argument is postponed until a later sibling solves its index metavar" do
    src = """
    mod PostponeProofFirst
    #{@preamble}
      fn consume(x: OKey, {hi: EKey}, e: Equivalent(OBit, elt(EFin(x), hi), OT()), c: Carrier(EFin(x), hi)) -> OBit = OT()
      fn drive(x: OKey, k: OKey, lt: Equivalent(OBit, slt(x, k), OT()), c: Carrier(EFin(x), EFin(k))) -> OBit =
        consume(x, lt, c)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "carrier-first ordering keeps working (no regression)" do
    src = """
    mod PostponeCarrierFirst
    #{@preamble}
      fn consume(x: OKey, {hi: EKey}, c: Carrier(EFin(x), hi), e: Equivalent(OBit, elt(EFin(x), hi), OT())) -> OBit = OT()
      fn drive(x: OKey, k: OKey, c: Carrier(EFin(x), EFin(k)), lt: Equivalent(OBit, slt(x, k), OT())) -> OBit =
        consume(x, c, lt)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "antibody: a genuinely ill-typed proof still rejects even when postponed" do
    # `pf : slt(x,k) = OF` cannot inhabit `elt(EFin x, EFin k) = OT` (= `slt(x,k) = OT`);
    # postponement must not launder a real type error into an accept.
    src = """
    mod PostponeAntibody
    #{@preamble}
      fn consume(x: OKey, {hi: EKey}, e: Equivalent(OBit, elt(EFin(x), hi), OT()), c: Carrier(EFin(x), hi)) -> OBit = OT()
      fn drive(x: OKey, k: OKey, bad: Equivalent(OBit, slt(x, k), OF()), c: Carrier(EFin(x), EFin(k))) -> OBit =
        consume(x, bad, c)
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
