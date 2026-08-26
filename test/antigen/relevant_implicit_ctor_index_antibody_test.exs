defmodule Antigen.RelevantImplicitCtorIndexAntibodyTest do
  @moduledoc """
  E-layer antibody (E2-residual, spec
  `2026-07-18-relevant-implicit-ctor-index-design.md`) — a constructor index may be
  IMPLICIT (solved, non-positional) yet RELEVANT (quantity ω, retained and usable),
  the fourth plicity/quantity quadrant Idris writes `{k : Nat}`. Cure previously
  welded plicity to quantity (inferred index ⇒ implicit+erased; explicit dom ⇒
  explicit+ω), so this shape forced an explicit `(k: T)` field. Decoupling plicity
  from quantity — application/pattern key off PLICITY, erasure keys off QUANTITY —
  adds the missing quadrant WITHOUT touching the kernel (it never reads plicities).

  The oracle probes `relimpl01`/`relimpl02` pin the ACCEPT/REJECT directions against
  Idris. This antibody pins that the decoupling is SOUND, not a blanket accept:

    * REACH — a relevant implicit `{k: NatT}` is constructed with `k` OMITTED
      (solved from the `Vec(k)` argument's index), pattern-bound by name, and
      RETURNED. Accepted because `k` is retained (ω).

    * CONTROL erasure — the plicity/quantity decoupling did NOT launder quantity.
      An INFERRED index (`VCons`'s `m`) is implicit AND erased (0). Left unforced by
      a free-index scrutinee, bound by name, and returned, it USES an erased value
      relevantly — the Relevance gate must still reject it.

    * CONTROL solving — the relevant implicit is genuinely SOLVED, not fabricated.
      A `{k: NatT}` that appears in no argument and no result index is
      underdetermined at construction, so it must reject with an unsolved
      metavariable rather than inventing a value.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # A relevant implicit `{k: NatT}`: solved from `Vec(k)`, retained, returnable.
  defp reach_src do
    """
    mod RelImplAb
      type NatT = ZZ | SS(NatT)
      type Vec indices (n: NatT)
        VNil  : Vec(ZZ)
        VCons : NatT -> Vec(m) -> Vec(SS(m))
      type Box indices ()
        MkBox : {k: NatT} -> Vec(k) -> Box
      fn ex() -> Box = MkBox(VCons(ZZ, VNil))
      fn getk(b: Box) -> NatT = match b
        MkBox({k = kk}, v) -> kk
    end
    """
  end

  test "REACH: relevant implicit `{k}` constructed-omitted, bound by name, returned" do
    assert {:ok, _} = Program.elaborate(reach_src())
  end

  # An UNFORCED erased inferred index (`m`), bound by name and returned relevantly.
  defp erased_src do
    """
    mod RelImplErasedAb
      type NatT = ZZ | SS(NatT)
      type Vec indices (n: NatT)
        VNil  : Vec(ZZ)
        VCons : NatT -> Vec(m) -> Vec(SS(m))
      fn getm(n: NatT, v: Vec(n)) -> NatT = match v
        VNil()                  -> ZZ
        VCons({m = mm}, x, rest) -> mm
    end
    """
  end

  test "CONTROL erasure: an erased inferred index used relevantly is still rejected" do
    assert {:error, {:source_context, {:erased_used_relevantly, %{def: :getm, binder: 2, site: :returned}}, context}} =
             Program.elaborate(erased_src())

    assert context.checking == :getm
    assert context.expectation_origin == :trusted_declaration_check
    assert context.expression_category == :relevance_check
    assert context.span.start_line == 6
    assert context.span.start_column == 41
  end

  # A relevant implicit appearing in no argument / index — unsolvable at construction.
  defp unsolvable_src do
    """
    mod RelImplUnsolvAb
      type NatT = ZZ | SS(NatT)
      type Opaque indices ()
        MkOpaque : {k: NatT} -> Opaque
      fn ex() -> Opaque = MkOpaque()
    end
    """
  end

  test "CONTROL solving: an underdetermined relevant implicit rejects, not fabricated" do
    assert {:error, {:source_context, {:unsolved_metavariables, _}, _}} = Program.elaborate(unsolvable_src())
  end
end
