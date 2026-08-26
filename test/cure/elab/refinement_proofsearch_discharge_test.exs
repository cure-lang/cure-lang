defmodule Cure.Elab.RefinementProofSearchDischargeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # An OPEN refinement obligation — one whose truth depends on a free binder, so
  # the closed-obligation `Confirmed()` discharge cannot fire — is now routed
  # through the auto-lemma proof search. When a proof is derivable from in-scope
  # evidence or a `@lemma`, the refined value type-checks with no hand-written
  # proof. Soundness is unchanged: ProofSearch kernel-rechecks every candidate,
  # and the assembled pair is re-checked by the fallback's `Kernel.check`.

  test "an open comparison obligation matching an in-scope hypothesis is auto-discharged" do
    assert {:ok, _env} =
             Program.elaborate("""
             mod RefineWireEvidence
               use Std.Nat
               use Std.Bool
               use Std.Proof.IntMath
               fn wrap(x: Int, evidence: IsTrue(x > 0)) -> {n: Int | n > 0} = x
             end
             """)
  end

  test "an open obligation with no available evidence is still rejected" do
    assert {:error, _} =
             Program.elaborate("""
             mod RefineWireNoEvidence
               use Std.Nat
               use Std.Bool
               use Std.Proof.IntMath
               fn wrap(x: Int) -> {n: Int | n > 0} = x
             end
             """)
  end
end
